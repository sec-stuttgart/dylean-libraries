module

public import DY.Comparse
public import DY.Actions.PersistentLocalState

namespace DY.Communication

open DY.Comparse

public class CoreConfig (α : Type) where
  tag : String

public class RequestResponseConfig (α : Type) where
  tag : String

variable [BytesFunctor]

public structure CommunicationMessage (α : Type) where
  sender : Participant
  receiver : Participant
  payload : α
deriving DecidableEq

public inductive EncryptionInput (α : Type) where
  | unsigned (sender receiver : Participant) (payload : α)
  | signed (sender receiver : Participant) (payload : α)
deriving DecidableEq

public inductive SignatureInput (α : Type) where
  | plain (sender receiver : Participant) (payload : α)
  | encrypted (payload publicKey : Bytes)
deriving DecidableEq

public structure SignedCommunicationMessage where
  message : Bytes
  signature : Bytes
deriving DecidableEq

public structure RequestMessage (α : Type) where
  request : α
  key : Bytes
deriving DecidableEq

public structure ResponseEnvelope where
  nonce : Bytes
  ciphertext : Bytes
deriving DecidableEq

/-- The identities authenticated as AEAD associated data.  `client = none`
represents the deliberately anonymous request mode. -/
public structure AssociatedData where
  client : Option Participant
  server : Participant
deriving DecidableEq

/-- Every communication-layer value placed on the network has an explicit
constructor tag.  The payload parameter keeps independently configured
request/response protocols from sharing a wire type. -/
public inductive WireMessage (α : Type) where
  | signature (message : SignedCommunicationMessage)
  | request (message : RequestMessage α)
  | response (message : ResponseEnvelope)
deriving DecidableEq

/-- Internal request context, also used as a proof witness for a retained state ID. -/
public structure CommunicationMetadata (α : Type) where
  key : Bytes
  client : Option Participant
  server : Participant
  stateHandle : Nat
  request : α
deriving DecidableEq

/-- Internal authenticated request context whose client identity cannot be absent. -/
public structure AuthenticatedMetadata (α : Type) where
  key : Bytes
  client : Participant
  server : Participant
  stateHandle : Nat
  request : α
deriving DecidableEq

public def AuthenticatedMetadata.toMetadata (x : AuthenticatedMetadata α) :
    CommunicationMetadata α where
  key := x.key
  client := some x.client
  server := x.server
  stateHandle := x.stateHandle
  request := x.request

public section Formats

variable [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

@[expose] def EncryptionInput.internalType (α : Type) : Fin 2 → Type
  | 0 | 1 => Participant × Participant × α

@[expose] def EncryptionInput.internalMf
    (mf : Comparse.ExtensibleMessageFormat Bytes α) :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (EncryptionInput.internalType α id)
  | 0 | 1 => .prod .slowString (.prod .slowString mf)

@[expose] public def EncryptionInput.mf
    (mf : Comparse.ExtensibleMessageFormat Bytes α) :
    Comparse.ExtensibleMessageFormat Bytes (EncryptionInput α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) (EncryptionInput.internalMf mf))
    (fun x => match x with
      | ⟨0, sender, receiver, payload⟩ => .unsigned sender receiver payload
      | ⟨1, sender, receiver, payload⟩ => .signed sender receiver payload)
    (fun x => match x with
      | .unsigned sender receiver payload => ⟨0, sender, receiver, payload⟩
      | .signed sender receiver payload => ⟨1, sender, receiver, payload⟩)
    (by grind)
    (by grind)

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.IsNonAmbiguous] :
    ∀ id, (EncryptionInput.internalMf mf id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [EncryptionInput.internalMf, EncryptionInput.internalType]
    infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.HasUniqueRepresentation] :
    ∀ id, (EncryptionInput.internalMf mf id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [EncryptionInput.internalMf, EncryptionInput.internalType]
    infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.IsNonAmbiguous] : (EncryptionInput.mf mf).IsNonAmbiguous := by
  dsimp [EncryptionInput.mf]
  infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.HasUniqueRepresentation] : (EncryptionInput.mf mf).HasUniqueRepresentation := by
  dsimp [EncryptionInput.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (EncryptionInput α) :=
  .make (EncryptionInput.mf ParseableSerializeable.mf)

@[simp]
public theorem EncryptionInput.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : EncryptionInput α) (tr : τ) :
    IsWellFormed pre x tr = match x with
      | .unsigned _ _ payload | .signed _ _ payload => IsWellFormed pre payload tr := by
  cases x <;>
    simp [IsWellFormed, ParseableSerializeable.mf, EncryptionInput.mf,
      EncryptionInput.internalMf, EncryptionInput.internalType]

@[expose] def SignatureInput.internalType (α : Type) : Fin 2 → Type
  | 0 => Participant × Participant × α
  | 1 => Bytes × Bytes

@[expose] def SignatureInput.internalMf
    (mf : Comparse.ExtensibleMessageFormat Bytes α) :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (SignatureInput.internalType α id)
  | 0 => .prod .slowString (.prod .slowString mf)
  | 1 => .prod .slowBytes .bytes

@[expose] public def SignatureInput.mf
    (mf : Comparse.ExtensibleMessageFormat Bytes α) :
    Comparse.ExtensibleMessageFormat Bytes (SignatureInput α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) (SignatureInput.internalMf mf))
    (fun x => match x with
      | ⟨0, sender, receiver, payload⟩ => .plain sender receiver payload
      | ⟨1, payload, publicKey⟩ => .encrypted payload publicKey)
    (fun x => match x with
      | .plain sender receiver payload => ⟨0, sender, receiver, payload⟩
      | .encrypted payload publicKey => ⟨1, payload, publicKey⟩)
    (by grind)
    (by grind)

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.IsNonAmbiguous] :
    ∀ id, (SignatureInput.internalMf mf id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [SignatureInput.internalMf, SignatureInput.internalType]
    infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.HasUniqueRepresentation] :
    ∀ id, (SignatureInput.internalMf mf id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [SignatureInput.internalMf, SignatureInput.internalType]
    infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.IsNonAmbiguous] : (SignatureInput.mf mf).IsNonAmbiguous := by
  dsimp [SignatureInput.mf]
  infer_instance

instance (mf : Comparse.ExtensibleMessageFormat Bytes α)
    [mf.HasUniqueRepresentation] : (SignatureInput.mf mf).HasUniqueRepresentation := by
  dsimp [SignatureInput.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (SignatureInput α) :=
  .make (SignatureInput.mf ParseableSerializeable.mf)

@[simp]
public theorem SignatureInput.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : SignatureInput α) (tr : τ) :
    IsWellFormed pre x tr = match x with
      | .plain _ _ payload => IsWellFormed pre payload tr
      | .encrypted payload publicKey => pre payload tr ∧ pre publicKey tr := by
  cases x <;>
    simp [IsWellFormed, ParseableSerializeable.mf, SignatureInput.mf,
      SignatureInput.internalMf, SignatureInput.internalType]

public instance : ParseableSerializeable SignedCommunicationMessage := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨message, signature⟩ => { message, signature })
    (fun { message, signature } => ⟨message, signature⟩)

@[simp]
public theorem SignedCommunicationMessage.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : SignedCommunicationMessage) (tr : τ) :
    IsWellFormed pre x tr = (pre x.message tr ∧ pre x.signature tr) := by
  simp [IsWellFormed, ParseableSerializeable.mf]

public instance [ParseableSerializeable α] : ParseableSerializeable (RequestMessage α) := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes ParseableSerializeable.mf)
    (fun ⟨key, request⟩ => { request, key })
    (fun { request, key } => ⟨key, request⟩)

@[simp]
public theorem RequestMessage.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : RequestMessage α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.request tr) := by
  simp [IsWellFormed, ParseableSerializeable.mf]

public instance : ParseableSerializeable ResponseEnvelope := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨nonce, ciphertext⟩ => { nonce, ciphertext })
    (fun { nonce, ciphertext } => ⟨nonce, ciphertext⟩)

@[simp]
public theorem ResponseEnvelope.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : ResponseEnvelope) (tr : τ) :
    IsWellFormed pre x tr = (pre x.nonce tr ∧ pre x.ciphertext tr) := by
  simp [IsWellFormed, ParseableSerializeable.mf]

@[expose] def OptionParticipant.internalType : Fin 2 → Type
  | 0 => Unit
  | 1 => Participant

@[expose] def OptionParticipant.internalMf :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (OptionParticipant.internalType id)
  | 0 => Comparse.NonExtensibleMessageFormat.toExtensible .unit
  | 1 => Comparse.NonExtensibleMessageFormat.toExtensible .slowString

@[expose] def OptionParticipant.mf :
    Comparse.ExtensibleMessageFormat Bytes (Option Participant) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) OptionParticipant.internalMf)
    (fun x => match x with | ⟨0, ()⟩ => none | ⟨1, p⟩ => some p)
    (fun x => match x with | none => ⟨0, ()⟩ | some p => ⟨1, p⟩)
    (by grind)
    (by grind)

instance : ∀ id, (OptionParticipant.internalMf id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [OptionParticipant.internalMf, OptionParticipant.internalType]
    infer_instance

instance : ∀ id, (OptionParticipant.internalMf id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [OptionParticipant.internalMf, OptionParticipant.internalType]
    infer_instance

instance : OptionParticipant.mf.IsNonAmbiguous := by
  dsimp [OptionParticipant.mf]
  infer_instance

instance : OptionParticipant.mf.HasUniqueRepresentation := by
  dsimp [OptionParticipant.mf]
  infer_instance

public instance : ParseableSerializeable (Option Participant) :=
  .make OptionParticipant.mf

@[expose] def AssociatedData.internalType : Fin 2 → Type
  | 0 => Participant
  | 1 => Participant × Participant

@[expose] def AssociatedData.internalMf :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (AssociatedData.internalType id)
  | 0 => Comparse.NonExtensibleMessageFormat.toExtensible .slowString
  | 1 => .prod .slowString (Comparse.NonExtensibleMessageFormat.toExtensible .slowString)

@[expose] def AssociatedData.mf : Comparse.ExtensibleMessageFormat Bytes AssociatedData :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) AssociatedData.internalMf)
    (fun x => match x with
      | ⟨0, server⟩ => { client := none, server }
      | ⟨1, client, server⟩ => { client := some client, server })
    (fun x => match x.client with
      | none => ⟨0, x.server⟩
      | some client => ⟨1, client, x.server⟩)
    (by
      rintro ⟨⟨i, hi⟩, value⟩
      have : i = 0 ∨ i = 1 := by omega
      rcases this with h | h <;> subst i <;> rfl)
    (by rintro ⟨client, server⟩; cases client <;> rfl)

instance : ∀ id, (AssociatedData.internalMf id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [AssociatedData.internalMf, AssociatedData.internalType]
    infer_instance

instance : ∀ id, (AssociatedData.internalMf id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [AssociatedData.internalMf, AssociatedData.internalType]
    infer_instance

instance : AssociatedData.mf.IsNonAmbiguous := by
  dsimp [AssociatedData.mf]
  infer_instance

instance : AssociatedData.mf.HasUniqueRepresentation := by
  dsimp [AssociatedData.mf]
  infer_instance

public instance : ParseableSerializeable AssociatedData := .make AssociatedData.mf

@[simp]
public theorem AssociatedData.IsWellFormed_eq
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : AssociatedData) (tr : τ) : IsWellFormed pre x tr = True := by
  rcases x with ⟨client, server⟩
  cases client <;>
    simp [IsWellFormed, ParseableSerializeable.mf, AssociatedData.mf,
      AssociatedData.internalMf, AssociatedData.internalType]

@[expose] def WireMessage.internalType (α : Type) : Fin 3 → Type
  | 0 => SignedCommunicationMessage
  | 1 => RequestMessage α
  | 2 => ResponseEnvelope

@[expose] def WireMessage.internalMf [ParseableSerializeable α] :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (WireMessage.internalType α id)
  | 0 => ParseableSerializeable.mf (a := SignedCommunicationMessage)
  | 1 => ParseableSerializeable.mf (a := RequestMessage α)
  | 2 => ParseableSerializeable.mf (a := ResponseEnvelope)

@[expose] public def WireMessage.mf [ParseableSerializeable α] :
    Comparse.ExtensibleMessageFormat Bytes (WireMessage α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 3 (by decide)) WireMessage.internalMf)
    (fun x => match x with
      | ⟨0, message⟩ => .signature message
      | ⟨1, message⟩ => .request message
      | ⟨2, message⟩ => .response message)
    (fun x => match x with
      | .signature message => ⟨0, message⟩
      | .request message => ⟨1, message⟩
      | .response message => ⟨2, message⟩)
    (by grind)
    (by grind)

instance [ParseableSerializeable α] :
    ∀ id, (WireMessage.internalMf (α := α) id).IsNonAmbiguous
  | 0 | 1 | 2 => by
    dsimp [WireMessage.internalMf, WireMessage.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    ∀ id, (WireMessage.internalMf (α := α) id).HasUniqueRepresentation
  | 0 | 1 | 2 => by
    dsimp [WireMessage.internalMf, WireMessage.internalType]
    infer_instance

instance [ParseableSerializeable α] : (WireMessage.mf (α := α)).IsNonAmbiguous := by
  dsimp [WireMessage.mf]
  infer_instance

instance [ParseableSerializeable α] :
    (WireMessage.mf (α := α)).HasUniqueRepresentation := by
  dsimp [WireMessage.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (WireMessage α) :=
  .make WireMessage.mf

@[simp]
public theorem WireMessage.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : WireMessage α) (tr : τ) : IsWellFormed pre x tr = match x with
      | .signature message => IsWellFormed pre message tr
      | .request message => IsWellFormed pre message tr
      | .response message => IsWellFormed pre message tr := by
  cases x <;>
    simp [IsWellFormed, ParseableSerializeable.mf, WireMessage.mf,
      WireMessage.internalMf, WireMessage.internalType]

@[expose] def CommunicationMetadata.internalType (α : Type) : Fin 2 → Type
  | 0 => Bytes × Participant × Nat × α
  | 1 => Bytes × Participant × Participant × Nat × α

@[expose] def CommunicationMetadata.internalMf [ParseableSerializeable α] :
    ∀ id, Comparse.ExtensibleMessageFormat Bytes (CommunicationMetadata.internalType α id)
  | 0 => .prod .slowBytes (.prod .slowString (.prod .slowNat ParseableSerializeable.mf))
  | 1 => .prod .slowBytes
      (.prod .slowString (.prod .slowString (.prod .slowNat ParseableSerializeable.mf)))

@[expose] def CommunicationMetadata.mf [ParseableSerializeable α] :
    Comparse.ExtensibleMessageFormat Bytes (CommunicationMetadata α) :=
  .triviallyIsomorphic
    (.sigma (.fin8 2 (by decide)) CommunicationMetadata.internalMf)
    (fun x => match x with
      | ⟨0, key, server, stateHandle, request⟩ =>
        { key, client := none, server, stateHandle, request }
      | ⟨1, key, client, server, stateHandle, request⟩ =>
        { key, client := some client, server, stateHandle, request })
    (fun x => match x.client with
      | none => ⟨0, x.key, x.server, x.stateHandle, x.request⟩
      | some client => ⟨1, x.key, client, x.server, x.stateHandle, x.request⟩)
    (by
      rintro ⟨⟨i, hi⟩, value⟩
      have : i = 0 ∨ i = 1 := by omega
      rcases this with h | h <;> subst i <;> rfl)
    (by
      rintro ⟨key, client, server, stateHandle, request⟩
      cases client <;> rfl)

instance [ParseableSerializeable α] :
    ∀ id, (CommunicationMetadata.internalMf (α := α) id).IsNonAmbiguous
  | 0 | 1 => by
    dsimp [CommunicationMetadata.internalMf, CommunicationMetadata.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    ∀ id, (CommunicationMetadata.internalMf (α := α) id).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp [CommunicationMetadata.internalMf, CommunicationMetadata.internalType]
    infer_instance

instance [ParseableSerializeable α] :
    (CommunicationMetadata.mf (α := α)).IsNonAmbiguous := by
  dsimp [CommunicationMetadata.mf]
  infer_instance

instance [ParseableSerializeable α] :
    (CommunicationMetadata.mf (α := α)).HasUniqueRepresentation := by
  dsimp [CommunicationMetadata.mf]
  infer_instance

public instance [ParseableSerializeable α] : ParseableSerializeable (CommunicationMetadata α) :=
  .make CommunicationMetadata.mf

@[simp]
public theorem CommunicationMetadata.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : CommunicationMetadata α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.request tr) := by
  rcases x with ⟨key, client, server, stateHandle, request⟩
  cases client <;>
    simp [IsWellFormed, ParseableSerializeable.mf, CommunicationMetadata.mf,
      CommunicationMetadata.internalMf, CommunicationMetadata.internalType]

public instance [ParseableSerializeable α] : ParseableSerializeable (AuthenticatedMetadata α) :=
  .make <| .triviallyIsomorphic
    (.prod .slowBytes
      (.prod .slowString (.prod .slowString (.prod .slowNat ParseableSerializeable.mf))))
    (fun ⟨key, client, server, stateHandle, request⟩ =>
      { key, client, server, stateHandle, request })
    (fun { key, client, server, stateHandle, request } =>
      ⟨key, client, server, stateHandle, request⟩)

@[simp]
public theorem AuthenticatedMetadata.IsWellFormed_eq
    [ParseableSerializeable α]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (x : AuthenticatedMetadata α) (tr : τ) :
    IsWellFormed pre x tr = (pre x.key tr ∧ IsWellFormed pre x.request tr) := by
  simp [IsWellFormed, ParseableSerializeable.mf]

end Formats

end DY.Communication
