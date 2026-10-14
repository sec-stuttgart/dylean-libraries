module

public import DyLibraries.Communication.All
public import DyLibraries.Communication.RequestResponse.Properties
public meta import DyLibraries.Communication.Data
public meta import DY.EquationalTheory.Sign
public meta import DyExtensions.EquationalTheory.PublicKeyEncryption
public meta import DyExtensions.EquationalTheory.AEAD
import DY.Meta

namespace DY.Example.Login

open DY.Comparse DY.Communication

public section

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

instance : ParseableSerializeable String := .make .string

structure Payload where
  kind : String
  client : Participant
  secret : Bytes
  deriving DecidableEq

instance : ParseableSerializeable Payload := .make <| .triviallyIsomorphic (.prod .slowString (.prod .slowString .bytes)) (fun ⟨kind, client, secret⟩ => {kind, client, secret}) (fun p => (p.kind, p.client, p.secret))

@[simp, grind =] theorem Payload.IsWellFormed_eq (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (p : Payload) (tr : τ) : IsWellFormed pre p tr = pre p.secret tr := by
  simp [IsWellFormed, ParseableSerializeable.mf]

grind_pattern [grind_later] Payload.IsWellFormed_eq => IsWellFormed pre p tr

instance : RequestResponseConfig Payload where
  tag := "Login"

/-- Provisioned over a trusted channel, before the client starts a login. -/
structure Credentials where
  client : Participant
  server : Participant
  password : Bytes
  deriving DecidableEq

instance : ParseableSerializeable Credentials := .make <| .triviallyIsomorphic (.prod .slowString (.prod .slowString .bytes)) (fun ⟨client, server, password⟩ => {client, server, password}) (fun p => (p.client, p.server, p.password))

/-- Credentials contain only their password as symbolic bytes. -/
@[simp, grind =]
theorem Credentials.IsWellFormed_eq
  (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre] (state : Credentials) (tr : τ) :
  IsWellFormed pre state tr = pre state.password tr
:= by
  simp [IsWellFormed, ParseableSerializeable.mf]

inductive LoginEvent where
  | provisioned (client server : Participant) (password : Bytes)
  | started (client server : Participant) (password : Bytes)
  | authenticated (client server : Participant) (password cookie : Bytes)
  | cookieReceived (client server : Participant) (cookie : Bytes)
  deriving DecidableEq

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  Random,
  ProtocolEvent LoginEvent,
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),
  PersistentLocalState.CompromisableState Credentials,

/-- Returns the client and server credential handles. Passwords are symbolic,
unguessable secrets; this example does not model dictionary attacks. -/
def provision (client server : Participant) : Traceful (Nat × Nat) := do
  let password ← Random.genRand 32
  ProtocolEvent.logEvent (.provisioned client server password : LoginEvent)
  let credentials : Credentials := {client, server, password}
  let clientState ← PersistentLocalState.storeLocalState client credentials
  let serverState ← PersistentLocalState.storeLocalState server credentials
  return (clientState, serverState)

def Client.start (client : Participant) (stateHandle : Nat) (keys : CommunicationKeyHandles) : Traceful (Nat × Nat) := do
  let st : Credentials ← PersistentLocalState.getLocalState client stateHandle
  guard (st.client = client)
  ProtocolEvent.logEvent (.started client st.server st.password : LoginEvent)
  sendRequest (α := Payload) keys client st.server {kind := "request", client, secret := st.password}

def Server.authenticate (server : Participant) (stateHandle : Nat) (keys : CommunicationKeyHandles) (messageHandle : Nat) : Traceful Nat := do
  let st : Credentials ← PersistentLocalState.getLocalState server stateHandle
  guard (st.server = server)
  let (request, metadata) ← receiveRequest (α := Payload) keys server messageHandle
  guard (request.kind = "request" ∧ request.client = st.client ∧ request.secret = st.password)
  let cookie ← Random.genRand 32
  ProtocolEvent.logEvent (.authenticated st.client server st.password cookie : LoginEvent)
  sendResponse (α := Payload) server metadata {kind := "cookie", client := st.client, secret := cookie}

def Client.finish (client : Participant) (stateId : Nat) (messageHandle : Nat) : Traceful Bytes := do
  let .clientSendRequest sent ← PersistentLocalUpdateableState.getLocalState (StateT := CommunicationState Payload) client stateId | failure
  let response ← receiveResponse (α := Payload) client stateId messageHandle
  guard (sent.request.kind = "request" ∧ sent.request.client = client ∧ response.kind = "cookie" ∧ response.client = client)
  ProtocolEvent.logEvent (.cookieReceived client sent.server response.secret : LoginEvent)
  return response.secret

end
end DY.Example.Login
