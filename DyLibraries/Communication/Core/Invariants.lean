module

public import DY.Communication.Core

namespace DY.Communication

open DY.Comparse

/-- Encryption keys share the channel usage; ownership is recorded by their labels and state. -/
@[expose]
public def communicationPkeUsage
  (α : Type) [BytesFunctor] [CoreConfig α] : Usage
:=
  { type := "PKEKey", tag := pkeKeyName α, data := none }

/-- Signing keys share the channel usage; ownership is recorded by their labels and state. -/
@[expose]
public def communicationSignatureUsage
  (α : Type) [BytesFunctor] [CoreConfig α] : Usage
:=
  { type := "SigKey", tag := signatureKeyName α, data := none }

public def communicationLabel
    [BytesFunctor] [ExecTraceTypes]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [CoreConfig α]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
    (sender receiver : Participant) : Label where
  isCorrupt tr :=
    (∃ pk, LongTermKeys.LongTermKeyCompromised (pkeKeyName α) sender pk tr) ∨
    (∃ pk, LongTermKeys.LongTermKeyCompromised (pkeKeyName α) receiver pk tr) ∨
    (∃ vk, LongTermKeys.LongTermKeyCompromised (signatureKeyName α) sender vk tr) ∨
    (∃ vk, LongTermKeys.LongTermKeyCompromised (signatureKeyName α) receiver vk tr)

/-- Protocols layered over communication can require additional facts whenever
they emit one of the three kinds of send event. -/
public class HigherLayerEventPredicates
    [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] (α : Type) where
  confidential : ProofTrace → Participant → Participant → α → Prop
  authenticated : ProofTrace → Participant → Participant → α → Prop
  confidentialAuthenticated : ProofTrace → Participant → Participant → α → Prop
  confidential_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → confidential tr1 sender receiver payload →
    confidential tr2 sender receiver payload
  authenticated_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → authenticated tr1 sender receiver payload →
    authenticated tr2 sender receiver payload
  confidentialAuthenticated_later : ∀ tr1 tr2 sender receiver payload,
    tr1 ≤ tr2 → confidentialAuthenticated tr1 sender receiver payload →
    confidentialAuthenticated tr2 sender receiver payload

grind_pattern [grind_later] HigherLayerEventPredicates.confidential_later =>
  tr1 ≤ tr2, HigherLayerEventPredicates.confidential tr1 sender receiver payload

grind_pattern [grind_later] HigherLayerEventPredicates.authenticated_later =>
  tr1 ≤ tr2, HigherLayerEventPredicates.authenticated tr1 sender receiver payload

grind_pattern [grind_later] HigherLayerEventPredicates.confidentialAuthenticated_later =>
  tr1 ≤ tr2, HigherLayerEventPredicates.confidentialAuthenticated tr1 sender receiver payload

@[instance_reducible]
public def defaultHigherLayerEventPredicates
    [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] (α : Type) :
    HigherLayerEventPredicates α where
  confidential _ _ _ _ := True
  authenticated _ _ _ _ := True
  confidentialAuthenticated _ _ _ _ := True
  confidential_later := by simp
  authenticated_later := by simp
  confidentialAuthenticated_later := by simp

public def participantCommunicationCompromised
    [BytesFunctor] [ExecTraceTypes] [CoreConfig α]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
    (participant : Participant) (tr : ExecTrace) : Prop :=
  (∃ pk, LongTermKeys.LongTermKeyCompromised (pkeKeyName α) participant pk tr) ∨
  (∃ vk, LongTermKeys.LongTermKeyCompromised (signatureKeyName α) participant vk tr)

public theorem participantCommunicationCompromised_later
    [BytesFunctor] [ExecTraceTypes] [CoreConfig α]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
    (participant : Participant) (tr1 tr2 : ExecTrace) :
    tr1 ≤ tr2 → participantCommunicationCompromised (α := α) participant tr1 →
    participantCommunicationCompromised (α := α) participant tr2 := by
  simp [participantCommunicationCompromised]
  grind

grind_pattern participantCommunicationCompromised_later =>
  tr1 ≤ tr2, participantCommunicationCompromised (α := α) participant tr1

section PkeKeys

variable [BytesFunctor] [BytesLength] [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF] [CoreConfig α]
variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]

/-- A communication public key retains the label of its corresponding secret
key. Publishability alone would not justify encrypting confidential payloads. -/
@[instance_reducible]
public instance communicationPkeProofConfig :
    LongTermKeys.ProofConfig (pkeKeyName α) (fun _ => communicationPkeUsage α) (LongTermKeys.label (pkeKeyName α)) where
  IsLongTermPublicKey participant publicKey tr :=
    ∃ secretKey, publicKey = PublicKeyEncryption.pk secretKey ∧
      secretKey.Invariant tr ∧
      secretKey.label tr = LongTermKeys.label (pkeKeyName α) participant publicKey ∧
      secretKey.HasUsage (communicationPkeUsage α) tr
  label_canFlow := by intros; exact canFlowRefl _ _
  IsLongTermPublicKey_le := by
    intro participant publicKey tr1 tr2 hle ⟨secretKey, hkey, hinv, hlabel, husage⟩
    refine ⟨secretKey, hkey, ?_, ?_, ?_⟩ <;> grind
  IsLongTermPublicKey_implied := by
    intro participant secretKey tr hinv hlabel husage
    exact ⟨secretKey, rfl, hinv, hlabel, husage⟩
  IsLongTermPublicKey_implies := by
    rintro participant publicKey tr ⟨secretKey, rfl, hinv, _, _⟩
    simp [Bytes.Publishable, PublicKeyEncryption.pk.Invariant _ _ hinv]
    exact canFlowRefl _ _

end PkeKeys

section SignatureKeys

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor.Has Signature.SubF] [CoreConfig α]
variable [BytesInvariants] [BytesInvariantsProofs] [Signature.SignPred]
variable [BytesInvariants.Has Signature.invariants]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]

/-- Signing keys use the channel usage and retain their owner through the key label. -/
@[instance_reducible]
public instance communicationSignatureProofConfig :
    LongTermKeys.ProofConfig (signatureKeyName α) (fun _ => communicationSignatureUsage α)
      (LongTermKeys.label (signatureKeyName α)) where
  IsLongTermPublicKey participant verificationKey tr :=
    verificationKey.Publishable tr ∧
    verificationKey.signkeyLabel tr = LongTermKeys.label (signatureKeyName α) participant verificationKey ∧
    verificationKey.SignkeyHasUsage (communicationSignatureUsage α) tr
  label_canFlow := by intros; exact canFlowRefl _ _
  IsLongTermPublicKey_le := by grind
  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

end SignatureKeys

section Predicates

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]

/-- Communication's PKE component records which send event justified an
honest encryption and requires every matching secret key to protect the
plaintext label.  The universal key clause makes this predicate safely
composable without relying on a partial inverse for `pk`. -/
@[instance_reducible]
public def corePkeEncryptPred
    (α : Type)
    [ParseableSerializeable (EncryptionInput α)]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
    [BytesFunctor.Has PublicKeyEncryption.SubF] : PublicKeyEncryption.EncryptPred where
  pred _usage publicKey message tr :=
    (match parse (a := EncryptionInput α) message with
      | some (.unsigned sender receiver payload : EncryptionInput α) =>
        tr.erase.EventLogged (.confidentialSend sender receiver payload : CoreEvent α)
      | some (.signed sender receiver payload : EncryptionInput α) =>
        tr.erase.EventLogged (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α)
      | none => False) ∧
    ∀ sk, publicKey = PublicKeyEncryption.pk sk →
      (message.label tr).canFlow (sk.label tr) tr.erase

omit [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF] in
public theorem corePkeEncryptPredProof
    (α : Type)
    [ParseableSerializeable (EncryptionInput α)]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesInvariants]
    [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
    [pred : PublicKeyEncryption.EncryptPred]
  (hpred : pred = corePkeEncryptPred α) :
    PublicKeyEncryption.EncryptPredProof := by
  subst pred
  letI : PublicKeyEncryption.EncryptPred := corePkeEncryptPred α
  refine { pred_later := ?_, pred_key_label := ?_ }
  ·
    intro _ _ _ usage publicKey message tr1 tr2 hpk hm hle hpred
    rcases hpred with ⟨hevent, hlabel⟩
    constructor
    · generalize hparse : parse (a := EncryptionInput α) message = parsed at hevent ⊢
      cases parsed with
      | none => contradiction
      | some input =>
        cases input <;>
          exact Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) hevent
    · intro sk hkey
      have hmLabel := Bytes.label_later message tr1 tr2 hle hm
      have hskWf : sk.WellFormed tr1 := by
        subst publicKey
        simpa using hpk
      have hskLabel := Bytes.label_later sk tr1 tr2 hle hskWf
      rw [← hmLabel, ← hskLabel]
      exact Label.canFlowLater _ _ _ _ (Trace.erase_le _ _ hle) (hlabel sk hkey)
  ·
    intro usage sk message tr h
    exact h.2 sk (Eq.refl _)

public def coreSignPredicate
    (α : Type)
    [ParseableSerializeable (SignatureInput α)]
    [ParseableSerializeable (EncryptionInput α)]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    (message : Bytes) (tr : ProofTrace) : Prop :=
  match parse (a := SignatureInput α) message with
    | some (.plain sender receiver payload : SignatureInput α) =>
      tr.erase.EventLogged (.authenticatedSend sender receiver payload : CoreEvent α)
    | some (.encrypted encryptedPayload publicKey : SignatureInput α) =>
      ∃ nonce plaintext sender receiver payload,
        encryptedPayload = PublicKeyEncryption.encrypt publicKey nonce plaintext ∧
        parse (a := EncryptionInput α) plaintext =
          some (.signed sender receiver payload : EncryptionInput α) ∧
        tr.erase.EventLogged
          (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α)
    | none => False

/-- Signature authentication is tied to a prior matching send event.  For the
encrypted form, the predicate also records the exact PKE construction that
contains the signed communication payload. -/
@[instance_reducible]
public def coreSignPred
    (α : Type)
    [ParseableSerializeable (SignatureInput α)]
    [ParseableSerializeable (EncryptionInput α)]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
    [BytesFunctor.Has PublicKeyEncryption.SubF] : Signature.SignPred where
  pred _ _ message tr := coreSignPredicate α message tr

omit [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF] in
public theorem coreSignPredProof
    (α : Type)
    [ParseableSerializeable (SignatureInput α)]
    [ParseableSerializeable (EncryptionInput α)]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesInvariants]
    [pred : Signature.SignPred]
    (hpred : pred = coreSignPred α) : Signature.SignPredProof := by
  subst pred
  letI : Signature.SignPred := coreSignPred α
  refine { pred_later := ?_ }
  ·
    intro _ _ _ skUsage verificationKey message tr1 tr2 _ _ hle hpred
    change coreSignPredicate α message tr1 at hpred
    change coreSignPredicate α message tr2
    generalize hparseInput : parse (a := SignatureInput α) message = parsed at hpred ⊢
    cases parsed with
    | none =>
      simp only [coreSignPredicate, hparseInput] at hpred
    | some input =>
      cases input with
      | plain =>
        simp only [coreSignPredicate, hparseInput] at hpred ⊢
        exact Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) hpred
      | encrypted =>
        simp only [coreSignPredicate, hparseInput] at hpred ⊢
        rcases hpred with ⟨nonce, plaintext, sender, receiver, payload, henc, hparse, hevent⟩
        exact ⟨nonce, plaintext, sender, receiver, payload, henc, hparse,
          Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) hevent⟩

end Predicates

section Events

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
variable [HigherLayerEventPredicates α]

public def coreEventInvariant (tr : ProofTrace) (event : CoreEvent α) : Prop :=
  match event with
  | .confidentialSend sender receiver payload =>
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload tr ∧
    HigherLayerEventPredicates.confidential tr sender receiver payload
  | .confidentialReceive sender receiver payload =>
    tr.erase.EventLogged (.confidentialSend sender receiver payload : CoreEvent α) ∨
    IsWellFormed Bytes.Publishable payload tr
  | .authenticatedSend sender receiver payload =>
    IsWellFormed Bytes.Publishable payload tr ∧
    HigherLayerEventPredicates.authenticated tr sender receiver payload
  | .authenticatedReceive sender receiver payload =>
    IsWellFormed Bytes.Publishable payload tr ∧
    (tr.erase.EventLogged (.authenticatedSend sender receiver payload : CoreEvent α) ∨
      participantCommunicationCompromised (α := α) sender tr.erase)
  | .confidentialAuthenticatedSend sender receiver payload =>
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload tr ∧
    HigherLayerEventPredicates.confidentialAuthenticated tr sender receiver payload
  | .confidentialAuthenticatedReceive sender receiver payload =>
    (tr.erase.EventLogged
        (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α) ∨
      participantCommunicationCompromised (α := α) sender tr.erase) ∧
    (tr.erase.EventLogged
        (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α) ∨
      IsWellFormed Bytes.Publishable payload tr)

public theorem coreEventInvariant_later [BytesInvariantsProofs]
    (event : CoreEvent α) (tr1 tr2 : ProofTrace) (hle : tr1 ≤ tr2)
    (h : coreEventInvariant tr1 event) : coreEventInvariant tr2 event := by
  cases event <;> simp only [coreEventInvariant] at h ⊢
  all_goals grind [HigherLayerEventPredicates.confidential_later,
    HigherLayerEventPredicates.authenticated_later,
    HigherLayerEventPredicates.confidentialAuthenticated_later,
    IsWellFormed_KnowableBy_later, IsWellFormed_Publishable_later]

grind_pattern [grind_later] coreEventInvariant_later => tr1 ≤ tr2, coreEventInvariant tr1 event

@[instance_reducible]
public def coreEventInv : ProtocolEvent.EventInv (CoreEvent α) where
  invariant := coreEventInvariant

end Events

end DY.Communication
