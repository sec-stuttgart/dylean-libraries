module

public import DyLibraries.Communication.Core
public import DyExtensions.EquationalTheory.AEAD
public import DyExtensions.Actions.PersistentLocalUpdateableState

namespace DY.Communication

open DY.Comparse

public instance [BytesFunctor] [RequestResponseConfig α] : CoreConfig (WireMessage α) where
  tag := RequestResponseConfig.tag (α := α) ++ ".Core"

public def aeadKeyName (α : Type) [RequestResponseConfig α] : String :=
  RequestResponseConfig.tag (α := α) ++ ".AEAD"

public inductive SenderAuthentication where
  | authenticated
  | unauthenticated
deriving DecidableEq

public structure ClientSendRequest [BytesFunctor] (α : Type) where
  client : Option Participant
  server : Participant
  request : α
  key : Bytes
deriving DecidableEq

public structure ServerReceiveRequest [BytesFunctor] (α : Type) where
  client : Option Participant
  request : α
  key : Bytes
deriving DecidableEq

public structure ClientReceiveResponse [BytesFunctor] (α : Type) where
  server : Participant
  response : α
  key : Bytes
deriving DecidableEq

public inductive CommunicationState [BytesFunctor] (α : Type) where
  | clientSendRequest (state : ClientSendRequest α)
  | serverReceiveRequest (state : ServerReceiveRequest α)
  | clientReceiveResponse (state : ClientReceiveResponse α)
deriving DecidableEq

public inductive RequestResponseEvent [BytesFunctor] (α : Type) where
  | clientSendRequest (authentication : SenderAuthentication)
      (client server : Participant) (request : α) (key : Bytes)
  | serverReceiveRequest (client : Option Participant)
      (server : Participant) (request : α) (key : Bytes)
  | serverSendResponse (client : Option Participant)
      (server : Participant) (request response : α) (key : Bytes)
  | clientReceiveResponse (client : Participant) (response : α)
      (metadata : CommunicationMetadata α)
deriving DecidableEq

public def requestAuthentication [BytesFunctor]
    (metadata : CommunicationMetadata α) : SenderAuthentication :=
  if metadata.client.isSome then .authenticated else .unauthenticated

public section StateFormats

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

public instance : ParseableSerializeable SenderAuthentication := .make <|
  .triviallyIsomorphic
    (Comparse.NonExtensibleMessageFormat.toExtensible (.fin8 2 (by decide)))
    (fun id => match id with | 0 => .authenticated | 1 => .unauthenticated)
    (fun x => match x with | .authenticated => 0 | .unauthenticated => 1)
    (by grind)
    (by grind)

@[expose] def ClientSendRequest.internalType (α : Type) : Fin 2 → Type
  | 0 => Bytes × Participant × α
  | 1 => Bytes × Participant × Participant × α

@[expose] def ClientSendRequest.internalMf [ParseableSerializeable α] :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (ClientSendRequest.internalType α id)
  | 0 => .prod .slowBytes (.prod .slowString ParseableSerializeable.mf)
  | 1 => .prod .slowBytes (.prod .slowString (.prod .slowString ParseableSerializeable.mf))

@[expose] def ClientSendRequest.mf [ParseableSerializeable α] :
    Comparse.ExtensibleMessageFormat Bytes (ClientSendRequest α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) ClientSendRequest.internalMf)
    (fun x => match x with
      | ⟨0, key, server, request⟩ => { client := none, server, request, key }
      | ⟨1, key, client, server, request⟩ => { client := some client, server, request, key })
    (fun x => match x.client with
      | none => ⟨0, x.key, x.server, x.request⟩
      | some client => ⟨1, x.key, client, x.server, x.request⟩)
    (by
      rintro ⟨⟨i, hi⟩, value⟩
      have : i = 0 ∨ i = 1 := by omega
      rcases this with h | h <;> subst i <;> rfl)
    (by
      rintro ⟨client, server, request, key⟩
      cases client <;> rfl)

instance [ParseableSerializeable α] :
    ∀ id, (ClientSendRequest.internalMf (α := α) id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [ClientSendRequest.internalMf, ClientSendRequest.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    ∀ id, (ClientSendRequest.internalMf (α := α) id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [ClientSendRequest.internalMf, ClientSendRequest.internalType]
    infer_instance

instance [ParseableSerializeable α] : (ClientSendRequest.mf (α := α)).IsNonAmbiguous := by
  dsimp [ClientSendRequest.mf]
  infer_instance

instance [ParseableSerializeable α] :
    (ClientSendRequest.mf (α := α)).HasUniqueRepresentation := by
  dsimp [ClientSendRequest.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (ClientSendRequest α) :=
  .make ClientSendRequest.mf

@[simp]
public theorem ClientSendRequest.IsWellFormed_eq [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : ClientSendRequest α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.request tr) := by
  rcases x with ⟨client, server, request, key⟩
  cases client <;>
    simp [IsWellFormed, ParseableSerializeable.mf, ClientSendRequest.mf,
      ClientSendRequest.internalMf, ClientSendRequest.internalType]

@[expose] def ServerReceiveRequest.internalType (α : Type) : Fin 2 → Type
  | 0 => Bytes × α
  | 1 => Bytes × Participant × α

@[expose] def ServerReceiveRequest.internalMf [ParseableSerializeable α] :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (ServerReceiveRequest.internalType α id)
  | 0 => .prod .slowBytes ParseableSerializeable.mf
  | 1 => .prod .slowBytes (.prod .slowString ParseableSerializeable.mf)

@[expose] def ServerReceiveRequest.mf [ParseableSerializeable α] :
    Comparse.ExtensibleMessageFormat Bytes (ServerReceiveRequest α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) ServerReceiveRequest.internalMf)
    (fun x => match x with
      | ⟨0, key, request⟩ => { client := none, request, key }
      | ⟨1, key, client, request⟩ => { client := some client, request, key })
    (fun x => match x.client with
      | none => ⟨0, x.key, x.request⟩
      | some client => ⟨1, x.key, client, x.request⟩)
    (by
      rintro ⟨⟨i, hi⟩, value⟩
      have : i = 0 ∨ i = 1 := by omega
      rcases this with h | h <;> subst i <;> rfl)
    (by
      rintro ⟨client, request, key⟩
      cases client <;> rfl)

instance [ParseableSerializeable α] :
    ∀ id, (ServerReceiveRequest.internalMf (α := α) id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [ServerReceiveRequest.internalMf, ServerReceiveRequest.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    ∀ id, (ServerReceiveRequest.internalMf (α := α) id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [ServerReceiveRequest.internalMf, ServerReceiveRequest.internalType]
    infer_instance

instance [ParseableSerializeable α] : (ServerReceiveRequest.mf (α := α)).IsNonAmbiguous := by
  dsimp [ServerReceiveRequest.mf]
  infer_instance

instance [ParseableSerializeable α] :
    (ServerReceiveRequest.mf (α := α)).HasUniqueRepresentation := by
  dsimp [ServerReceiveRequest.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (ServerReceiveRequest α) :=
  .make ServerReceiveRequest.mf

@[simp]
public theorem ServerReceiveRequest.IsWellFormed_eq [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : ServerReceiveRequest α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.request tr) := by
  rcases x with ⟨client, request, key⟩
  cases client <;>
    simp [IsWellFormed, ParseableSerializeable.mf, ServerReceiveRequest.mf,
      ServerReceiveRequest.internalMf, ServerReceiveRequest.internalType]

public instance [ParseableSerializeable α] : ParseableSerializeable (ClientReceiveResponse α) :=
  .make <| .triviallyIsomorphic
    (.prod .slowBytes (.prod .slowString ParseableSerializeable.mf))
    (fun ⟨key, server, response⟩ => { server, response, key })
    (fun { server, response, key } => ⟨key, server, response⟩)

@[simp]
public theorem ClientReceiveResponse.IsWellFormed_eq [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : ClientReceiveResponse α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.response tr) := by
  simp [IsWellFormed, ParseableSerializeable.mf]

@[expose] def CommunicationState.internalType [BytesFunctor] (α : Type) : Fin 3 → Type
  | 0 => ClientSendRequest α
  | 1 => ServerReceiveRequest α
  | 2 => ClientReceiveResponse α

@[expose] def CommunicationState.internalMf [ParseableSerializeable α] :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (CommunicationState.internalType α id)
  | 0 => ParseableSerializeable.mf (a := ClientSendRequest α)
  | 1 => ParseableSerializeable.mf (a := ServerReceiveRequest α)
  | 2 => ParseableSerializeable.mf (a := ClientReceiveResponse α)

@[expose] public def CommunicationState.mf [ParseableSerializeable α] :
    Comparse.ExtensibleMessageFormat Bytes (CommunicationState α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 3 (by decide)) CommunicationState.internalMf)
    (fun x => match x with
      | ⟨0, state⟩ => .clientSendRequest state
      | ⟨1, state⟩ => .serverReceiveRequest state
      | ⟨2, state⟩ => .clientReceiveResponse state)
    (fun x => match x with
      | .clientSendRequest state => ⟨0, state⟩
      | .serverReceiveRequest state => ⟨1, state⟩
      | .clientReceiveResponse state => ⟨2, state⟩)
    (by grind)
    (by grind)

instance [ParseableSerializeable α] :
    ∀ id, (CommunicationState.internalMf (α := α) id).IsNonAmbiguous
  | 0 | 1 | 2 => by
    dsimp [CommunicationState.internalMf, CommunicationState.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    ∀ id, (CommunicationState.internalMf (α := α) id).HasUniqueRepresentation
  | 0 | 1 | 2 => by
    dsimp [CommunicationState.internalMf, CommunicationState.internalType]
    infer_instance

instance [ParseableSerializeable α] : (CommunicationState.mf (α := α)).IsNonAmbiguous := by
  dsimp [CommunicationState.mf]
  infer_instance

instance [ParseableSerializeable α] :
    (CommunicationState.mf (α := α)).HasUniqueRepresentation := by
  dsimp [CommunicationState.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (CommunicationState α) :=
  .make CommunicationState.mf

@[simp]
public theorem CommunicationState.IsWellFormed_eq [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : CommunicationState α) (tr : τ) : IsWellFormed pre x tr = match x with
      | .clientSendRequest state => IsWellFormed pre state tr
      | .serverReceiveRequest state => IsWellFormed pre state tr
      | .clientReceiveResponse state => IsWellFormed pre state tr := by
  cases x <;>
    simp [IsWellFormed, ParseableSerializeable.mf, CommunicationState.mf,
      CommunicationState.internalMf, CommunicationState.internalType]

end StateFormats

section StoredRequests

variable [BytesFunctor] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT (CommunicationState α))]

/-- Reconstruct response metadata from the server's retained request. -/
private def getServerMetadata
  (server : Participant) (stateId : Nat) :
  Traceful (CommunicationMetadata α)
:= do
  let state ← PersistentLocalUpdateableState.getLocalState (StateT := CommunicationState α) server stateId
  let .serverReceiveRequest received := state | failure
  pure { client := received.client, server, request := received.request, key := received.key, stateHandle := stateId }

/-- Reconstruct response metadata from the client's retained request. -/
private def getClientMetadata
  (client : Participant) (stateId : Nat) :
  Traceful (CommunicationMetadata α)
:= do
  let state ← PersistentLocalUpdateableState.getLocalState (StateT := CommunicationState α) client stateId
  let .clientSendRequest sent := state | failure
  pure { client := sent.client, server := sent.server, request := sent.request, key := sent.key, stateHandle := stateId }

end StoredRequests

section Runtime

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has AEAD.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [DecidableEq α] [RequestResponseConfig α]
variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent (WireMessage α)))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

/-- Allocate a fresh state ID and retain the communication state at that address. -/
private def storeCommunicationState
  (participant : Participant) (state : CommunicationState α) :
  Traceful Nat
:= do
  let stateId ← PersistentLocalUpdateableState.newSessionId (CommunicationState α) participant
  let _ ← PersistentLocalUpdateableState.setLocalState participant stateId state
  pure stateId

/-- Send an anonymous request and return its network handle and local state ID. -/
public def sendRequest
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  Traceful (Nat × Nat)
:= do
  let key ← Random.genRand 32
  ProtocolEvent.logEvent (.clientSendRequest .unauthenticated client server request key : RequestResponseEvent α)
  let stateId ← storeCommunicationState client (.clientSendRequest { client := none, server, request, key } : CommunicationState α)
  let messageHandle ← sendConfidential (α := WireMessage α) handles client server (.request { request, key })
  pure (messageHandle, stateId)

/-- Send an authenticated request and return its network handle and local state ID. -/
public def sendRequestAuthenticated
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  Traceful (Nat × Nat)
:= do
  let key ← Random.genRand 32
  ProtocolEvent.logEvent (.clientSendRequest .authenticated client server request key : RequestResponseEvent α)
  let stateId ← storeCommunicationState client (.clientSendRequest { client := some client, server, request, key } : CommunicationState α)
  let messageHandle ← sendConfidentialAuthenticated (α := WireMessage α) handles client server (.request { request, key })
  pure (messageHandle, stateId)

/-- Receive an anonymous request and return its payload and local state ID. -/
public def receiveRequest
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  Traceful (α × Nat)
:= do
  let message ← receiveConfidential (α := WireMessage α) handles server messageHandle
  let requestMessage ← match message.payload with
    | .request requestMessage => pure requestMessage
    | _ => failure
  ProtocolEvent.logEvent (.serverReceiveRequest none server requestMessage.request requestMessage.key : RequestResponseEvent α)
  let stateId ← storeCommunicationState server (.serverReceiveRequest { client := none, request := requestMessage.request, key := requestMessage.key } : CommunicationState α)
  pure (requestMessage.request, stateId)

/-- Receive an authenticated request and return its payload and local state ID. -/
public def receiveRequestAuthenticated
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  Traceful (α × Nat)
:= do
  let message ← receiveConfidentialAuthenticated (α := WireMessage α) handles server messageHandle
  let requestMessage ← match message.payload with
    | .request requestMessage => pure requestMessage
    | _ => failure
  ProtocolEvent.logEvent (.serverReceiveRequest (some message.sender) server requestMessage.request requestMessage.key : RequestResponseEvent α)
  let stateId ← storeCommunicationState server (.serverReceiveRequest { client := some message.sender, request := requestMessage.request, key := requestMessage.key } : CommunicationState α)
  pure (requestMessage.request, stateId)

/-- Encrypt and serialize a response using the retained request context. -/
private def computeResponseMessage
  (server : Participant) (metadata : CommunicationMetadata α)
  (nonce : Bytes) (response : α) :
  Bytes
:=
  let associatedData := serialize ({ client := metadata.client, server } : AssociatedData)
  let ciphertext := AEAD.encrypt metadata.key nonce (serialize response) associatedData
  serialize (.response { nonce, ciphertext } : WireMessage α)

/-- Check the retained server context before encrypting and logging a response. -/
private def sendResponseWithMetadata
  (server : Participant) (metadata : CommunicationMetadata α) (response : α) :
  Traceful Nat
:= do
  let state : CommunicationState α ← PersistentLocalUpdateableState.getLocalState server metadata.stateHandle
  let received ← match state with
    | .serverReceiveRequest received => pure received
    | _ => failure
  guard (metadata.server = server)
  guard (received.client = metadata.client)
  guard (received.key = metadata.key)
  guard (received.request = metadata.request)
  ProtocolEvent.logEvent (.serverSendResponse metadata.client server received.request response received.key : RequestResponseEvent α)
  let nonce ← Random.genRand 32
  Network.sendMessage (computeResponseMessage server metadata nonce response)

/-- Parse and authenticate a response against its retained request context. -/
private def decodeResponseMessage
  (server : Participant) (key messageBytes : Bytes)
  (metadata : CommunicationMetadata α) :
  Err α
:= do
  let wire : WireMessage α ← parse messageBytes
  let envelope ← match wire with
    | .response envelope => pure envelope
    | _ => failure
  let associatedData := serialize ({ client := metadata.client, server } : AssociatedData)
  let responseBytes ← AEAD.decrypt key envelope.nonce envelope.ciphertext associatedData
  parse responseBytes

/-- Receive a response using the immutable client-send state at
`metadata.stateHandle`.  A successful call appends a fresh receive state but
does not replace the send state, so the same valid response is intentionally
replayable with the original handle. -/
private def receiveResponseWithMetadata
  (client : Participant) (metadata : CommunicationMetadata α)
  (messageHandle : Nat) :
  Traceful α
:= do
  let state : CommunicationState α ← PersistentLocalUpdateableState.getLocalState client metadata.stateHandle
  let sent ← match state with
    | .clientSendRequest sent => pure sent
    | _ => failure
  guard (sent.client = metadata.client)
  guard (sent.server = metadata.server)
  guard (sent.key = metadata.key)
  guard (sent.request = metadata.request)
  match metadata.client with
  | some actualClient => guard (actualClient = client)
  | none => pure ()
  let messageBytes ← Network.receiveMessage messageHandle
  let response ← decodeResponseMessage sent.server sent.key messageBytes metadata
  let _newStateId ← storeCommunicationState client (.clientReceiveResponse { server := sent.server, response, key := sent.key } : CommunicationState α)
  ProtocolEvent.logEvent (.clientReceiveResponse client response metadata : RequestResponseEvent α)
  pure response

/-- Receive a response using an internal authenticated request context. -/
private def receiveResponseAuthenticatedWithMetadata
  (client : Participant) (metadata : AuthenticatedMetadata α)
  (messageHandle : Nat) :
  Traceful α
:=
  receiveResponseWithMetadata client metadata.toMetadata messageHandle

/-- Send a response using only the server's local request ID. -/
public def sendResponse
  (server : Participant) (stateId : Nat) (response : α) :
  Traceful Nat
:= do
  let metadata ← getServerMetadata (α := α) server stateId
  sendResponseWithMetadata server metadata response

/-- Receive a response using the original client request ID; valid responses remain replayable. -/
public def receiveResponse
  (client : Participant) (stateId messageHandle : Nat) :
  Traceful α
:= do
  let metadata ← getClientMetadata (α := α) client stateId
  receiveResponseWithMetadata client metadata messageHandle

/-- Receive a response for an authenticated request owned by this client. -/
public def receiveResponseAuthenticated
  (client : Participant) (stateId messageHandle : Nat) :
  Traceful α
:= do
  let metadata ← getClientMetadata (α := α) client stateId
  guard (metadata.client = some client)
  receiveResponseWithMetadata client metadata messageHandle

/-- Disclose the communication state at this participant-scoped ID. -/
public def compromiseCommunicationState (participant : Participant) (stateId : Nat) : Traceful Nat :=
  PersistentLocalUpdateableState.compromise (CommunicationState α) participant stateId

public def initializeRequestResponse (client server : Participant) :
    Traceful (CommunicationKeyHandles × CommunicationKeyHandles) :=
  initializeCore (α := WireMessage α) client server

end Runtime

end DY.Communication
