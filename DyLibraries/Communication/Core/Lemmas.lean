module

public import DY.EquationalTheory.SplitPKE
public import DY.EquationalTheory.SplitSignature
import all DY.Bytes.Invariants

public import DY.Communication.Core.Invariants
public import DY.Trace.ReachabilityTheorem
import all DY.Communication.Core
import all DY.Communication.Core.Invariants
import all DY.Trace.Manipulation
import all DY.Trace.Monad
import all DY.Comparse
import DY.Meta.Step

namespace DY.Communication
open DY.Comparse

set_option linter.unusedSectionVars false

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF] [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [ExecTraceTypes.Has Network.ExecEntryT] [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
private theorem coreLabel_canFlow_pkeLabel
    (sender receiver : Participant) (publicKey : Bytes) (tr : ExecTrace) :
    (communicationLabel (α := α) sender receiver).canFlow
      (LongTermKeys.label (pkeKeyName α) receiver publicKey) tr := by
  intro later hle hcorrupt
  exact Or.inr (Or.inl ⟨publicKey, hcorrupt⟩)

private theorem decryptMessage_parts
    (secretKey messageBytes : Bytes) (message : CommunicationMessage α)
    (h : decryptMessage secretKey messageBytes = some message) :
    ∃ plaintext : Bytes, PublicKeyEncryption.decrypt secretKey messageBytes = some plaintext ∧
      parse (a := EncryptionInput α) plaintext =
        some (.unsigned message.sender message.receiver message.payload) := by
  simp only [decryptMessage, bind, pure, instMonadErr._aux_13, instMonadErr._aux_5,
    OptionT.bind, OptionT.pure, OptionT.mk, OptionT.fail, failure,
    instAlternativeErr._aux_1] at h
  repeat' (split at h <;> simp_all)
  all_goals grind

private theorem verifyAndDecryptMessage_parts
    (sender receiver : Participant) (secretKey verificationKey messageBytes : Bytes)
    (message : CommunicationMessage α)
    (h : verifyAndDecryptMessage sender receiver secretKey verificationKey messageBytes = some message) :
    message.sender = sender ∧ message.receiver = receiver ∧
    ∃ signed : SignedCommunicationMessage, ∃ ciphertext publicKey plaintext : Bytes,
      parse (a := WireMessage α) messageBytes = some (.signature signed) ∧
      parse (a := SignatureInput α) signed.message = some (.encrypted ciphertext publicKey) ∧
      Signature.verify verificationKey signed.message signed.signature ∧
      publicKey = PublicKeyEncryption.pk secretKey ∧
      PublicKeyEncryption.decrypt secretKey ciphertext = some plaintext ∧
      parse (a := EncryptionInput α) plaintext = some (.signed sender receiver message.payload) := by
  simp only [verifyAndDecryptMessage, verifyMessage, bind, pure, guard,
    instMonadErr._aux_13, instMonadErr._aux_5, OptionT.bind, OptionT.pure,
    OptionT.mk, OptionT.fail, failure, instAlternativeErr._aux_1] at h
  repeat' (split at * <;> simp_all)
  all_goals grind (splits := 40) (gen := 20)

@[instance]
private theorem getSender_preservesTrace (messageBytes : Bytes) (secretKey : Option Bytes) :
    HoareTriple (getSender (α := α) messageBytes secretKey) (fun _ => True) (fun _ _ => True) := by
  constructor
  simp only [hoareTriple, wp, OptionT.run]
  intros
  split <;> trivial

private theorem verifyMessage_plain_parts
    (sender receiver : Participant) (verificationKey messageBytes : Bytes) (verified : Sum α Bytes)
    (h : verifyMessage sender receiver messageBytes none verificationKey = some verified) :
    ∃ signed : SignedCommunicationMessage, ∃ payload : α,
      verified = .inl payload ∧
      parse (a := WireMessage α) messageBytes = some (.signature signed) ∧
      parse (a := SignatureInput α) signed.message = some (.plain sender receiver payload) ∧
      Signature.verify verificationKey signed.message signed.signature := by
  simp only [verifyMessage, bind, pure, guard, instMonadErr._aux_13, instMonadErr._aux_5,
    OptionT.bind, OptionT.pure, OptionT.mk, OptionT.fail, failure, instAlternativeErr._aux_1] at h
  repeat' (split at * <;> simp_all)
  all_goals grind (splits := 40) (gen := 20)

end DY.Communication

namespace DY.Communication
open DY.Comparse

section
variable [BytesFunctor] [BytesLength] [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [BytesInvariants]

/-- Dispatch signature obligations to the channel registered at the signing usage. -/
public theorem splitSignPredicate_eq
  [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  (usage : Usage) (key message : Bytes) (tr : ProofTrace)
  (ht : usage.type = "SigKey") (hg : usage.tag = signatureKeyName α) :
  Signature.SignPred.pred usage key message tr ↔ coreSignPredicate α message tr
:= by
  exact Signature.SignPred.HasStep.pred_eq (tag := signatureKeyName α) (component := coreSignPred α) usage key message tr ht hg

/-- PKE dispatch retains the public-key compromise alternative. A publishable
secret key satisfies arbitrary `HasUsage`, so it must not select a policy. -/
public theorem splitPkePredicate_intro
  [PublicKeyEncryption.EncryptPred] [PublicKeyEncryption.EncryptPred.Has (pkeKeyName α) (corePkeEncryptPred α)]
  (usage : Usage) (sk message : Bytes) (tr : ProofTrace)
  (ht : usage.type = "PKEKey") (hg : usage.tag = pkeKeyName α)
  (hu : sk.HasUsage usage tr) (hm : message.Invariant tr)
  (hp : (corePkeEncryptPred α).pred usage (PublicKeyEncryption.pk sk) message tr) :
  PublicKeyEncryption.EncryptPred.pred (sk.usage tr) (PublicKeyEncryption.pk sk) message tr ∨ message.Publishable tr
:= by
  rcases hu with hu | hpub
  · left
    rw [hu]
    exact (PublicKeyEncryption.EncryptPred.HasStep.pred_eq (tag := pkeKeyName α) (component := corePkeEncryptPred α) usage (PublicKeyEncryption.pk sk) message tr ht hg).mpr hp
  · exact Or.inr ⟨hm, canFlowTrans _ _ _ _ (hp.2 sk rfl) hpub⟩

/-- Recover the channel's PKE obligation or public plaintext, including keys
whose arbitrary claimed usage is justified only by compromise. -/
public theorem splitPkePredicate_elim
  [PublicKeyEncryption.EncryptPred] [PublicKeyEncryption.EncryptPredProof]
  [PublicKeyEncryption.EncryptPred.Has (pkeKeyName α) (corePkeEncryptPred α)]
  (usage : Usage) (sk message : Bytes) (tr : ProofTrace)
  (ht : usage.type = "PKEKey") (hg : usage.tag = pkeKeyName α)
  (hu : sk.HasUsage usage tr) (hm : message.Invariant tr)
  (hp : PublicKeyEncryption.EncryptPred.pred (sk.usage tr) (PublicKeyEncryption.pk sk) message tr) :
  (corePkeEncryptPred α).pred usage (PublicKeyEncryption.pk sk) message tr ∨ message.Publishable tr
:= by
  rcases hu with hu | hpub
  · left
    rw [hu] at hp
    exact (PublicKeyEncryption.EncryptPred.HasStep.pred_eq (tag := pkeKeyName α) (component := corePkeEncryptPred α) usage (PublicKeyEncryption.pk sk) message tr ht hg).mp hp
  · exact Or.inr ⟨hm, canFlowTrans _ _ _ _ (PublicKeyEncryption.EncryptPredProof.pred_key_label _ _ _ _ hp) hpub⟩
end
end DY.Communication

namespace DY.Communication
open DY.Comparse

set_option linter.unusedSectionVars false

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF] [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [ExecTraceTypes.Has Network.ExecEntryT] [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
-- Fix the concrete crypto and PKI predicates in the component assumptions.
variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
variable [PublicKeyEncryption.EncryptPred] [PublicKeyEncryption.EncryptPredProof]
variable [PublicKeyEncryption.EncryptPred.Has (pkeKeyName α) (corePkeEncryptPred α)]
variable [BytesInvariants.Has PublicKeyEncryption.Ciphertext.invariants]
variable [Signature.SignPred]
variable [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
variable [BytesInvariants.Has Signature.invariants]
variable [HigherLayerEventPredicates α]
attribute [local instance] coreEventInv
variable [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has Random.invariants]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (CoreEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (CoreEvent α))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (pkeKeyName α))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (signatureKeyName α))]

omit [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  [BytesInvariants.Has Signature.invariants]
  [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))] in
/-- Send with the channel policy selected by the receiver key usage; caller obligations are unchanged. -/
@[instance]
public theorem sendConfidential.proof
    (handles : CommunicationKeyHandles) (sender receiver : Participant) (payload : α) :
    HoareTriple (sendConfidential handles sender receiver payload)
      (fun tr => HigherLayerEventPredicates.confidential tr sender receiver payload ∧
        IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload tr)
      (fun _ tr => tr.erase.EventLogged (.confidentialSend sender receiver payload : CoreEvent α)) := by
  apply HoareTriple.mk
  unfold sendConfidential
  step
  step with ⟨fun _ => communicationLabel (α := α) sender receiver, Usage.nothing⟩
  step by
    simp only [ProtocolEvent.EventInv.invariant, coreEventInvariant]
    grind
  unfold encryptMessage
  hoist
  step by
    have hpk : LongTermKeys.IsLongTermPublicKey (pkeKeyName α) receiver receiverPublicKey tr := by assumption
    obtain ⟨sk, rfl, hsk, hlabel, husage⟩ := hpk
    have hm : (serialize (.unsigned sender receiver payload : EncryptionInput α)).KnowableBy (communicationLabel (α := α) sender receiver) tr := by
      simp only [KnowableBy_serialize, EncryptionInput.IsWellFormed_eq]
      grind
    have hf := coreLabel_canFlow_pkeLabel (α := α) sender receiver (PublicKeyEncryption.pk sk) tr.erase
    have hlocal : (corePkeEncryptPred α).pred (communicationPkeUsage α) (PublicKeyEncryption.pk sk) (serialize (.unsigned sender receiver payload : EncryptionInput α)) tr := by
      change (_ ∧ _)
      constructor
      · simpa only [parse_serialize_inv] using (by assumption : tr.erase.EventLogged (.confidentialSend sender receiver payload : CoreEvent α))
      · intro sk' heq
        have := PublicKeyEncryption.pk_injective heq
        subst sk'
        rw [hlabel]
        exact canFlowTrans _ _ _ _ hm.2 hf
    have hc := splitPkePredicate_intro (α := α) (communicationPkeUsage α) sk _ tr rfl rfl husage hm.1 hlocal
    grind [PublicKeyEncryption.keyUsage_pk, PublicKeyEncryption.pk.Invariant]
  step
  grind

-- Parsing facts are separated from the invariant proofs below.
omit [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  [BytesInvariants.Has Signature.invariants]
  [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))] in
/-- Decrypt under a registered key family, recovering the channel send event or public plaintext.
Dispatch needs the stored key usage; public receive operations recover it from the key store. -/
@[instance]
public theorem decryptMessage.proof
  (secretKey messageBytes : Bytes) :
  HoareTriple (decryptMessage (α := α) secretKey messageBytes)
    (fun tr => ∃ usage : Usage,
      usage.type = "PKEKey" ∧ usage.tag = pkeKeyName α ∧
      secretKey.Invariant tr ∧ messageBytes.Publishable tr ∧ secretKey.HasUsage usage tr)
    (fun message tr => tr.erase.EventLogged
      (.confidentialSend message.sender message.receiver message.payload : CoreEvent α) ∨
      IsWellFormed Bytes.Publishable message.payload tr)
:= by
  constructor
  intro tr hpre htr
  obtain ⟨usage, ht, hg, hpre⟩ := hpre
  simp only [wp, OptionT.run]
  split
  · trivial
  · rename_i message hdec
    obtain ⟨plaintext, hd, hp⟩ := decryptMessage_parts secretKey messageBytes message hdec
    have hout := PublicKeyEncryption.decrypt.Invariant _ _ _ tr hpre.1 hpre.2.1.1 hd
    rcases hout.2 with hpred | hpub
    · have hh := splitPkePredicate_elim (α := α) usage secretKey plaintext tr ht hg hpre.2.2 hout.1 hpred
      have heq := serialize_parse_inv _ _ hp
      subst plaintext
      change ((_ ∧ _) ∨ _) at hh
      simp only [parse_serialize_inv] at hh
      simpa only [Publishable_serialize, EncryptionInput.IsWellFormed_eq] using hh.imp And.left id
    · have heq := serialize_parse_inv _ _ hp
      subst plaintext
      exact Or.inr (by simpa only [Publishable_serialize, EncryptionInput.IsWellFormed_eq] using hpub)

omit [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  [BytesInvariants.Has Signature.invariants]
  [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))] in
/-- Receive under the registered channel policy, preserving the send-event or public-payload alternative without a caller condition. -/
@[instance]
public theorem receiveConfidential.proof
    (handles : CommunicationKeyHandles) (receiver : Participant) (messageHandle : Nat) :
    HoareTriple (receiveConfidential (α := α) handles receiver messageHandle)
      (fun _ => True)
      (fun message tr => message.receiver = receiver ∧ tr.erase.EventLogged
        (.confidentialReceive message.sender receiver message.payload : CoreEvent α)) := by
  unfold receiveConfidential
  step
  step
  step by
    refine ⟨communicationPkeUsage α, rfl, rfl, ?_⟩
    simp_all only [LongTermKeys.IsLongTermSecretKey]
    grind
  step
  step by
    simp only [ProtocolEvent.EventInv.invariant, coreEventInvariant]
    grind
  step
  grind

omit [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))] in
/-- Authenticate a public payload using the signing family registered for this channel. -/
@[instance]
public theorem sendAuthenticated.proof
  (handles : CommunicationKeyHandles) (sender receiver : Participant) (payload : α) :
  HoareTriple (sendAuthenticated handles sender receiver payload)
    (fun tr => HigherLayerEventPredicates.authenticated tr sender receiver payload ∧
      IsWellFormed Bytes.Publishable payload tr)
    (fun _ tr => tr.erase.EventLogged (.authenticatedSend sender receiver payload : CoreEvent α))
:= by
  have signatureAgreement (key message : Bytes) (tr : ProofTrace) :
      Signature.SignPred.pred (communicationSignatureUsage α) key message tr ↔ coreSignPredicate α message tr :=
    splitSignPredicate_eq (α := α) _ _ _ _ rfl rfl

  apply HoareTriple.mk
  unfold sendAuthenticated
  step
  step with ⟨fun _ => LongTermKeys.label (signatureKeyName α) sender (Signature.vk senderSecretKey), Usage.nothing⟩
  step by
    simp only [ProtocolEvent.EventInv.invariant, coreEventInvariant]
    grind
  let message := serialize (.plain sender receiver payload : SignatureInput α)
  have hm : message.Publishable tr := by
    simp only [message, Publishable_serialize, SignatureInput.IsWellFormed_eq]
    grind
  let signature := Signature.sign senderSecretKey nonce message
  step_let signature with ⟨communicationSignatureUsage α⟩ by
    simp_all only [LongTermKeys.IsLongTermSecretKey, communicationSignatureUsage,
      message, coreSignPredicate, parse_serialize_inv]
    grind
  step by
    change (serialize (.signature {message, signature} : WireMessage α)).Publishable tr
    simp only [Publishable_serialize, WireMessage.IsWellFormed_eq, SignedCommunicationMessage.IsWellFormed_eq]
    grind
  grind

/-- Sign and encrypt using the channel registrations, preserving the original send contract. -/
@[instance]
public theorem sendConfidentialAuthenticated.proof
  (handles : CommunicationKeyHandles) (client server : Participant) (payload : α) :
  HoareTriple (sendConfidentialAuthenticated handles client server payload)
    (fun tr => HigherLayerEventPredicates.confidentialAuthenticated tr client server payload ∧
      IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) client server)) payload tr)
    (fun _ tr => tr.erase.EventLogged (.confidentialAuthenticatedSend client server payload : CoreEvent α))
:= by
  have signatureAgreement (key message : Bytes) (tr : ProofTrace) :
      Signature.SignPred.pred (communicationSignatureUsage α) key message tr ↔ coreSignPredicate α message tr :=
    splitSignPredicate_eq (α := α) _ _ _ _ rfl rfl

  apply HoareTriple.mk
  unfold sendConfidentialAuthenticated
  step
  step
  step with ⟨fun _ => communicationLabel (α := α) client server, Usage.nothing⟩
  step with ⟨fun _ => LongTermKeys.label (signatureKeyName α) client (Signature.vk senderSecretKey),
    Usage.nothing⟩
  step by
    simp only [ProtocolEvent.EventInv.invariant, coreEventInvariant]
    grind
  let ciphertext := PublicKeyEncryption.encrypt receiverPublicKey encryptionNonce
    (serialize (.signed client server payload :
      EncryptionInput α))
  step_let ciphertext by
    have hpk : LongTermKeys.IsLongTermPublicKey (pkeKeyName α) server receiverPublicKey tr := by assumption
    obtain ⟨sk, rfl, hsk, hlabel, husage⟩ := hpk
    have hm : (serialize (.signed client server payload : EncryptionInput α)).KnowableBy (communicationLabel (α := α) client server) tr := by
      simp only [KnowableBy_serialize, EncryptionInput.IsWellFormed_eq]
      grind
    have hf := coreLabel_canFlow_pkeLabel (α := α) client server (PublicKeyEncryption.pk sk) tr.erase
    have hlocal : (corePkeEncryptPred α).pred (communicationPkeUsage α) (PublicKeyEncryption.pk sk) (serialize (.signed client server payload : EncryptionInput α)) tr := by
      change (_ ∧ _)
      constructor
      · simpa only [parse_serialize_inv] using (by assumption : tr.erase.EventLogged (.confidentialAuthenticatedSend client server payload : CoreEvent α))
      · intro sk' heq
        have := PublicKeyEncryption.pk_injective heq
        subst sk'
        rw [hlabel]
        exact canFlowTrans _ _ _ _ hm.2 hf
    have hc := splitPkePredicate_intro (α := α) (communicationPkeUsage α) sk _ tr rfl rfl husage hm.1 hlocal
    grind [PublicKeyEncryption.keyUsage_pk, PublicKeyEncryption.pk.Invariant]
  let signature := Signature.sign senderSecretKey signatureNonce
    (serialize (.encrypted ciphertext receiverPublicKey : SignatureInput α))
  have hmsg : (serialize (.encrypted ciphertext receiverPublicKey : SignatureInput α)).Publishable tr := by
    have hct : ciphertext.Publishable tr := by grind
    have hpk : receiverPublicKey.Publishable tr := by
      have hpk : LongTermKeys.IsLongTermPublicKey (pkeKeyName α) server receiverPublicKey tr := by assumption
      exact (LongTermKeys.ProofConfig.IsLongTermPublicKey_implies (pkeKeyName α) server receiverPublicKey tr hpk)
    simpa only [Publishable_serialize, SignatureInput.IsWellFormed_eq] using And.intro hct hpk
  step_let signature with ⟨communicationSignatureUsage α⟩ by
    simp_all only [LongTermKeys.IsLongTermSecretKey, communicationSignatureUsage,
      coreSignPredicate, parse_serialize_inv]
    grind
  step by
    change (serialize (.signature {
      message := serialize (.encrypted ciphertext receiverPublicKey : SignatureInput α),
      signature } : WireMessage α)).Publishable tr
    simp only [Publishable_serialize, WireMessage.IsWellFormed_eq, SignedCommunicationMessage.IsWellFormed_eq]
    grind
  grind

/-- Verify and decrypt using the configured signing family and stored decryption-key usage,
preserving the original authentication and public-plaintext compromise alternatives. -/
@[instance]
public theorem verifyAndDecryptMessage.proof
  (sender server : Participant) (secretKey verificationKey messageBytes : Bytes) :
  HoareTriple (verifyAndDecryptMessage (α := α) sender server secretKey verificationKey messageBytes)
    (fun tr => ∃ usage : Usage,
      usage.type = "PKEKey" ∧ usage.tag = pkeKeyName α ∧ secretKey.Invariant tr ∧
      LongTermKeys.IsLongTermPublicKey (signatureKeyName α) sender verificationKey tr ∧ messageBytes.Publishable tr ∧ secretKey.HasUsage usage tr)
    (fun message tr => message.sender = sender ∧ message.receiver = server ∧
      coreEventInvariant tr (.confidentialAuthenticatedReceive sender server message.payload : CoreEvent α))
:= by
  have signatureAgreement (key message : Bytes) (tr : ProofTrace) :
      Signature.SignPred.pred (communicationSignatureUsage α) key message tr ↔ coreSignPredicate α message tr :=
    splitSignPredicate_eq (α := α) _ _ _ _ rfl rfl

  constructor
  intro tr hpre htr
  obtain ⟨usage, ht, hg, hpre⟩ := hpre
  simp only [wp, OptionT.run]
  split
  · trivial
  · rename_i message hdec
    obtain ⟨hsender, hreceiver, signed, ciphertext, publicKey, plaintext,
      hwire, hinput, hverify, hpk, hdecrypt, hparse⟩ :=
      verifyAndDecryptMessage_parts sender server secretKey verificationKey messageBytes message hdec
    have hsigned : signed.message.Publishable tr ∧ signed.signature.Publishable tr := by
      have hw : IsWellFormed Bytes.Publishable (.signature signed : WireMessage α) tr := by grind
      simpa only [WireMessage.IsWellFormed_eq, SignedCommunicationMessage.IsWellFormed_eq] using hw
    have hcipher : ciphertext.Publishable tr := by
      have hw : IsWellFormed Bytes.Publishable (.encrypted ciphertext publicKey : SignatureInput α) tr := by grind
      simp only [SignatureInput.IsWellFormed_eq] at hw
      exact hw.1
    have hvk := hpre.2.1
    simp only [LongTermKeys.IsLongTermPublicKey] at hvk
    have hv := Signature.verify.Invariant verificationKey signed.message signed.signature
      (communicationSignatureUsage α) tr hvk.1.1 hsigned.1.1 hsigned.2.1 hvk.2.2 hverify
    have hpke := PublicKeyEncryption.decrypt.Invariant _ _ _ tr hpre.1 hcipher.1 hdecrypt
    have hplainEq := serialize_parse_inv _ _ hparse
    have hinputEq := serialize_parse_inv _ _ hinput
    have hconf : tr.erase.EventLogged
        (.confidentialAuthenticatedSend sender server message.payload : CoreEvent α) ∨
        IsWellFormed Bytes.Publishable message.payload tr := by
      have hh : (corePkeEncryptPred α).pred usage (PublicKeyEncryption.pk secretKey) plaintext tr ∨ plaintext.Publishable tr := by
        rcases hpke.2 with hp | hp
        · exact splitPkePredicate_elim (α := α) usage secretKey plaintext tr ht hg hpre.2.2.2 hpke.1 hp
        · exact Or.inr hp
      rw [hplainEq] at hh
      change ((_ ∧ _) ∨ _) at hh
      simp only [parse_serialize_inv, Publishable_serialize, EncryptionInput.IsWellFormed_eq] at hh
      exact hh.imp And.left id
    have hauth : tr.erase.EventLogged
        (.confidentialAuthenticatedSend sender server message.payload : CoreEvent α) ∨
        participantCommunicationCompromised (α := α) sender tr.erase := by
      rcases hv with hv | hv
      · have hv := hv rfl
        simp only [signatureAgreement, coreSignPredicate, hinput] at hv
        obtain ⟨nonce, original, sender', server', payload', hc, hp, he⟩ := hv
        rw [hc, hpk, PublicKeyEncryption.decrypt_encrypt] at hdecrypt
        have ho : original = plaintext := Option.some.inj hdecrypt
        subst original
        have heq : sender' = sender ∧ server' = server ∧ payload' = message.payload := by grind
        grind
      · rw [hvk.2.1, ← canFlowPubEqIsCorrupt] at hv
        exact Or.inr (Or.inr ⟨verificationKey, hv⟩)
    exact ⟨hsender, hreceiver, hauth, hconf⟩

/-- Receive an authenticated confidential message under global policies with no caller condition. -/
@[instance]
public theorem receiveConfidentialAuthenticated.proof
  (handles : CommunicationKeyHandles) (receiver : Participant) (messageHandle : Nat) :
  HoareTriple (receiveConfidentialAuthenticated (α := α) handles receiver messageHandle)
    (fun _ => True)
    (fun message tr => message.receiver = receiver ∧ tr.erase.EventLogged
      (.confidentialAuthenticatedReceive message.sender receiver message.payload : CoreEvent α))
:= by
  unfold receiveConfidentialAuthenticated
  step
  step
  step
  step
  step by
    refine ⟨communicationPkeUsage α, rfl, rfl, ?_⟩
    simp_all only [LongTermKeys.IsLongTermSecretKey]
    grind
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    grind
  step
  grind

omit [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))] in
/-- Verify using the registered signing family, recovering the send event unless the sender is compromised. -/
@[instance]
public theorem verifyMessage.proof
  (sender receiver : Participant) (verificationKey messageBytes : Bytes) :
  HoareTriple (verifyMessage (α := α) sender receiver messageBytes none verificationKey)
    (fun tr => LongTermKeys.IsLongTermPublicKey (signatureKeyName α) sender verificationKey tr ∧ messageBytes.Publishable tr)
    (fun verified tr => match verified with
      | .inl payload => coreEventInvariant tr (.authenticatedReceive sender receiver payload : CoreEvent α)
      | .inr _ => False)
:= by
  have signatureAgreement (key message : Bytes) (tr : ProofTrace) :
      Signature.SignPred.pred (communicationSignatureUsage α) key message tr ↔ coreSignPredicate α message tr :=
    splitSignPredicate_eq (α := α) _ _ _ _ rfl rfl

  constructor
  intro tr hpre htr
  simp only [wp, OptionT.run]
  split
  · trivial
  · rename_i verified hverify
    obtain ⟨signed, payload, rfl, hwire, hinput, hverified⟩ :=
      verifyMessage_plain_parts sender receiver verificationKey messageBytes verified hverify
    have hsigned : signed.message.Publishable tr ∧ signed.signature.Publishable tr := by
      have hw : IsWellFormed Bytes.Publishable (.signature signed : WireMessage α) tr := by grind
      simpa only [WireMessage.IsWellFormed_eq, SignedCommunicationMessage.IsWellFormed_eq] using hw
    have hpub : IsWellFormed Bytes.Publishable payload tr := by
      have hw : IsWellFormed Bytes.Publishable (.plain sender receiver payload : SignatureInput α) tr := by grind
      simpa only [SignatureInput.IsWellFormed_eq] using hw
    have hvk := hpre.1
    simp only [LongTermKeys.IsLongTermPublicKey] at hvk
    have hv := Signature.verify.Invariant verificationKey signed.message signed.signature
      (communicationSignatureUsage α) tr hvk.1.1 hsigned.1.1 hsigned.2.1 hvk.2.2 hverified
    refine ⟨hpub, ?_⟩
    rcases hv with hv | hv
    · have hv := hv rfl
      simpa only [signatureAgreement, coreSignPredicate, hinput] using Or.inl hv
    · rw [hvk.2.1, ← canFlowPubEqIsCorrupt] at hv
      exact Or.inr (Or.inr ⟨verificationKey, hv⟩)

omit [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))] in
/-- Receive an authenticated message under the global signing policy with no caller condition. -/
@[instance]
public theorem receiveAuthenticated.proof
  (handles : CommunicationKeyHandles) (receiver : Participant) (messageHandle : Nat) :
  HoareTriple (receiveAuthenticated (α := α) handles receiver messageHandle)
    (fun _ => True)
    (fun message tr => message.receiver = receiver ∧
      tr.erase.EventLogged (.authenticatedReceive message.sender receiver message.payload : CoreEvent α))
:= by
  apply HoareTriple.mk
  intro tr _ htr
  unfold receiveAuthenticated
  step
  step
  step
  step
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_bind, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  step
  step by
    simp only [ProtocolEvent.EventInv.invariant]
    grind
  step
  grind

/-- Initialize both key families under the global signing policy without a caller condition. -/
@[instance]
public theorem initializeCore.proof (sender receiver : Participant) :
    HoareTriple (initializeCore (α := α) sender receiver) (fun _ => True) (fun _ _ => True) := by
  unfold initializeCore
  step
  split
  step
  split
  step
  split
  step
  split
  step
  grind

section Reachability

-- Pure message helpers do not extend the trace. Reachability steps cover the
-- seven trace actions, with the same caller obligations as their specifications.

@[expose] public def receiveConfidential.reachability : ReachabilityConfig :=
  .make (fun (handles, receiver, messageHandle) => receiveConfidential (α := α) handles receiver messageHandle)

@[expose] public def receiveAuthenticated.reachability : ReachabilityConfig :=
  .make (fun (handles, receiver, messageHandle) => receiveAuthenticated (α := α) handles receiver messageHandle)

@[expose] public def receiveConfidentialAuthenticated.reachability : ReachabilityConfig :=
  .make (fun (handles, receiver, messageHandle) => receiveConfidentialAuthenticated (α := α) handles receiver messageHandle)

@[expose] public def initializeCore.reachability : ReachabilityConfig :=
  .make (fun (sender, receiver) => initializeCore (α := α) sender receiver)

/-- Send preconditions constrain authorization and payloads on invariant lifts
of the execution trace; they do not assume invariant preservation by the action. -/
@[expose] public def sendConfidential.reachability : ReachabilityConfig where
  Input := CommunicationKeyHandles × Participant × Participant × α
  PreCond := fun (_, sender, receiver, payload) tr => ∀ proofTr : ProofTrace, proofTr.erase = tr → proofTr.Invariant →
    HigherLayerEventPredicates.confidential proofTr sender receiver payload ∧
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload proofTr
  step := fun (handles, sender, receiver, payload) => ⟨_, sendConfidential handles sender receiver payload⟩

@[expose] public def sendAuthenticated.reachability : ReachabilityConfig where
  Input := CommunicationKeyHandles × Participant × Participant × α
  PreCond := fun (_, sender, receiver, payload) tr => ∀ proofTr : ProofTrace, proofTr.erase = tr → proofTr.Invariant →
    HigherLayerEventPredicates.authenticated proofTr sender receiver payload ∧
    IsWellFormed Bytes.Publishable payload proofTr
  step := fun (handles, sender, receiver, payload) => ⟨_, sendAuthenticated handles sender receiver payload⟩

@[expose] public def sendConfidentialAuthenticated.reachability : ReachabilityConfig where
  Input := CommunicationKeyHandles × Participant × Participant × α
  PreCond := fun (_, sender, receiver, payload) tr => ∀ proofTr : ProofTrace, proofTr.erase = tr → proofTr.Invariant →
    HigherLayerEventPredicates.confidentialAuthenticated proofTr sender receiver payload ∧
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload proofTr
  step := fun (handles, sender, receiver, payload) => ⟨_, sendConfidentialAuthenticated handles sender receiver payload⟩

omit [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  [BytesInvariants.Has Signature.invariants]
  [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))] in
public instance : ReachableImpliesInvariant (sendConfidential.reachability (α := α)) where
  pf := by
    rintro ⟨handles, sender, receiver, payload⟩
    change HoareTriple (sendConfidential (α := α) handles sender receiver payload) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    have hcaller := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step
    trivial

omit [Signature.SignPred] [Signature.SignPred.Has (signatureKeyName α) (coreSignPred α)]
  [BytesInvariants.Has Signature.invariants]
  [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName α))] in
public instance : ReachableImpliesInvariant (receiveConfidential.reachability (α := α)) where
  pf := by
    rintro ⟨handles, receiver, messageHandle⟩
    change HoareTriple (receiveConfidential (α := α) handles receiver messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

omit [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))] in
/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem sendAuthenticated.reachability.sound
  : ReachableImpliesInvariant (sendAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, sender, receiver, payload⟩
    change HoareTriple (sendAuthenticated (α := α) handles sender receiver payload) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    have hcaller := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step
    trivial

omit [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName α))] in
/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem receiveAuthenticated.reachability.sound
  : ReachableImpliesInvariant (receiveAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, receiver, messageHandle⟩
    change HoareTriple (receiveAuthenticated (α := α) handles receiver messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem sendConfidentialAuthenticated.reachability.sound
  : ReachableImpliesInvariant (sendConfidentialAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, sender, receiver, payload⟩
    change HoareTriple (sendConfidentialAuthenticated (α := α) handles sender receiver payload) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    have hcaller := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step
    trivial

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem receiveConfidentialAuthenticated.reachability.sound
  : ReachableImpliesInvariant (receiveConfidentialAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, receiver, messageHandle⟩
    change HoareTriple (receiveConfidentialAuthenticated (α := α) handles receiver messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial


/-- Initializing the channel key families preserves the trace invariant. -/
public instance : ReachableImpliesInvariant (initializeCore.reachability (α := α)) where
  pf input := initializeCore.proof input.1 input.2

end Reachability

end DY.Communication
