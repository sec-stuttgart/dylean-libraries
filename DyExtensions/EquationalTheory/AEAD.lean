module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation

namespace DY.AEAD

public class CanEncrypt (Bytes : Type u) where
  encrypt : (key: Bytes) → (nonce: Bytes) → (message: Bytes) → (associatedData: Bytes) → Bytes
  decrypt : (key: Bytes) → (nonce: Bytes) → (ciphertext: Bytes) → (associatedData: Bytes) → Err Bytes

export CanEncrypt (encrypt decrypt)

section Constructors

namespace Ciphertext

public structure SubF (Bytes : Type) where
  key : Bytes
  nonce : Bytes
  message : Bytes
  associatedData : Bytes

public instance : ALaCarte.FunctorSizeOf SubF where
  sizeOf | { key, nonce, message, associatedData } => sizeOf key + sizeOf nonce + sizeOf message + sizeOf associatedData

public instance : ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 4 }
  toRepr | { key, nonce, message, associatedData } => {
    id := (), data := (), as := #v[key, nonce, message, associatedData]
  }
  fromRepr | { as, .. } => {
    key := as[0], nonce := as[1], message := as[2], associatedData := as[3]
  }
  from_to | { key, nonce, message, associatedData } => by rfl
  to_from | { id, data, as } => by simp_all <;> grind
  sizeOf_eq | { key, nonce, message, associatedData } => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance : ALaCarte.RepresentableDecidableEq SubF where
public instance : ALaCarte.RepresentableOrd SubF where
public instance : SubBytesFunctor SubF where

public def SubF.length [BytesFunctor] : Bytes.PartialLength SubF :=
  fun { key, nonce, message, associatedData } rec =>
    16 + rec message

end Ciphertext

#combine into BytesFunctor, BytesLength from
  Ciphertext,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Ciphertext.SubF.pack (x : Ciphertext.SubF Bytes) := BytesView.pack x

public instance : CanEncrypt Bytes where
  encrypt key nonce message associatedData :=
    ({ key, nonce, message, associatedData } : Ciphertext.SubF Bytes).pack
  decrypt key nonce ciphertext associatedData :=
    match ciphertext.view? Ciphertext.SubF with
    | some c =>
      if c.key = key && c.nonce = nonce && c.associatedData = associatedData then
        some c.message
      else
        none
    | none => none

@[simp]
public theorem decrypt_encrypt (key nonce message associatedData : Bytes) :
    decrypt key nonce (encrypt key nonce message associatedData) associatedData = some message := by
  simp only [decrypt, encrypt]
  grind

end Constructors

section AttackerKnowledge

public def encrypt.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ key nonce message associatedData,
    out = encrypt key nonce message associatedData ∧
      p key ∧ p nonce ∧ p message ∧ p associatedData

public def decrypt.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ key nonce ciphertext associatedData,
    decrypt key nonce ciphertext associatedData = some out ∧
      p key ∧ p nonce ∧ p ciphertext ∧ p associatedData

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  encrypt,
  decrypt,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public theorem attacker_knows_encrypt
    (key nonce message associatedData : Bytes) (tr : ExecTrace) :
    key.AttackerKnows tr → nonce.AttackerKnows tr → message.AttackerKnows tr →
    associatedData.AttackerKnows tr →
    (encrypt key nonce message associatedData).AttackerKnows tr := by
  intro hk hn hm had
  apply Bytes.AttackerKnows.prove encrypt.attackerKnowledge
  refine ⟨key, nonce, message, associatedData, rfl, ?_⟩
  exact ⟨hk, hn, hm, had⟩

public theorem attacker_knows_decrypt
    (key nonce ciphertext associatedData message : Bytes) (tr : ExecTrace) :
    key.AttackerKnows tr → nonce.AttackerKnows tr → ciphertext.AttackerKnows tr →
    associatedData.AttackerKnows tr →
    decrypt key nonce ciphertext associatedData = some message →
    message.AttackerKnows tr := by
  intro hk hn hct had hdec
  apply Bytes.AttackerKnows.prove decrypt.attackerKnowledge
  refine ⟨key, nonce, ciphertext, associatedData, hdec, ?_⟩
  exact ⟨hk, hn, hct, had⟩

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor]

public class EncryptPred where
  pred : [BytesWellFormed] → [GetUsage] → [GetLabel] →
    Usage → Bytes → Bytes → Bytes → Bytes → ProofTrace → Prop

public class EncryptPredProof
    [BytesFunctor.Has AEAD.SubF] [BytesInvariants] [EncryptPred] where
  pred_later : [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ usage key nonce message associatedData tr1 tr2,
      key.WellFormed tr1 → nonce.WellFormed tr1 → message.WellFormed tr1 → associatedData.WellFormed tr1 →
      tr1 ≤ tr2 → EncryptPred.pred usage key nonce message associatedData tr1 →
      EncryptPred.pred usage key nonce message associatedData tr2
  pred_key_label : ∀ usage key nonce message associatedData tr,
    EncryptPred.pred usage key nonce message associatedData tr →
    (message.label tr).canFlow (key.label tr) tr.erase

grind_pattern EncryptPredProof.pred_later =>
  tr1 ≤ tr2, EncryptPred.pred usage key nonce message associatedData tr1

public def Ciphertext.invariants [EncryptPred] : Bytes.PartialInvariants Ciphertext.SubF where
  well_formed := fun { key, nonce, message, associatedData } rec tr =>
    (rec key) tr ∧ (rec nonce) tr ∧ (rec message) tr ∧ (rec associatedData) tr
  usage := fun _ _ _ => Usage.nothing
  label := fun _ _ _ => Label.pub
  invariant := fun { key, nonce, message, associatedData } rec tr =>
    (rec key) tr ∧ (rec nonce) tr ∧ (rec message) tr ∧ (rec associatedData) tr ∧
    -- A public plaintext alone does not justify bypassing authentication.
    (EncryptPred.pred (key.usage tr) key nonce message associatedData tr ∨
      ((key.label tr).canFlow Label.pub tr.erase ∧
        (message.label tr).canFlow Label.pub tr.erase))

public theorem Ciphertext.invariantsProofs
    [BytesFunctor.Has AEAD.SubF]
    [BytesInvariants] [EncryptPred] [EncryptPredProof] :
    Bytes.PartialInvariantsProofs Ciphertext.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [Ciphertext.invariants, ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind

set_option linter.unusedSectionVars false in
#combine [BytesFunctor.Has SubF] [EncryptPred] into
  BytesInvariants,
  BytesInvariantsProofs [EncryptPredProof]
from
  Ciphertext,

variable [BytesFunctor.Has SubF]

@[simp]
public theorem encrypt.WellFormed [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (key nonce message associatedData : Bytes) (tr : ProofTrace) :
    (encrypt key nonce message associatedData).WellFormed tr =
      (key.WellFormed tr ∧ nonce.WellFormed tr ∧ message.WellFormed tr ∧
        associatedData.WellFormed tr) := by
  simp [encrypt, Bytes.WellFormed.eq, Ciphertext.invariants]

@[simp]
public theorem encrypt.label [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (key nonce message associatedData : Bytes) (tr : ProofTrace) :
    (encrypt key nonce message associatedData).label tr = Label.pub := by
  simp [encrypt, Bytes.label.eq, Ciphertext.invariants]

public theorem encrypt.Invariant [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (key nonce message associatedData : Bytes) (tr : ProofTrace) :
    key.Invariant tr → nonce.Invariant tr → message.Invariant tr →
    associatedData.Invariant tr →
    (EncryptPred.pred (key.usage tr) key nonce message associatedData tr ∨ (key.Publishable tr ∧ message.Publishable tr)) →
    (encrypt key nonce message associatedData).Invariant tr := by
  simp [encrypt, Bytes.Invariant.eq, Ciphertext.invariants, Bytes.Publishable]
  grind

public theorem decrypt.Invariant [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (key nonce ciphertext associatedData message : Bytes) (tr : ProofTrace) :
    key.Invariant tr → nonce.Invariant tr → ciphertext.Invariant tr →
    associatedData.Invariant tr →
    decrypt key nonce ciphertext associatedData = some message →
    message.Invariant tr ∧
      (EncryptPred.pred (key.usage tr) key nonce message associatedData tr ∨ (key.Publishable tr ∧ message.Publishable tr)) := by
  intro hk hn hct had hdec
  simp [decrypt] at hdec
  split at hdec <;> try contradiction
  rename_i c hc
  split at hdec <;> try contradiction
  rename_i hfields
  have hm : c.message = message := by grind
  subst message
  have hview := Bytes.pack_view? Ciphertext.SubF ciphertext
  simp only [hc] at hview
  subst hview
  simp [Bytes.Invariant.eq, Ciphertext.invariants] at hct
  have hkey : c.key = key := by grind
  have hadEq : c.associatedData = associatedData := by grind
  have hnEq : c.nonce = nonce := by grind
  rw [hkey, hnEq, hadEq] at hct
  rcases hct with ⟨_, _, hmInv, _, hpred | hpub⟩
  · exact ⟨hmInv, Or.inl hpred⟩
  · exact ⟨hmInv, Or.inr ⟨⟨hk, hpub.1⟩, ⟨hmInv, hpub.2⟩⟩⟩

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]

public instance [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (key nonce message associatedData : Bytes) :
    HoareTriplePure (encrypt key nonce message associatedData)
      (fun tr => key.Invariant tr ∧ nonce.Invariant tr ∧ message.Invariant tr ∧
        associatedData.Invariant tr ∧
        (EncryptPred.pred (key.usage tr) key nonce message associatedData tr ∨ (key.Publishable tr ∧ message.Publishable tr)))
      (fun res tr => res.Invariant tr ∧ res.label tr = Label.pub) where
  pf := by grind [encrypt.Invariant, encrypt.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [EncryptPred] [EncryptPredProof]
variable [BytesInvariants.Has Ciphertext.invariants]

public instance : SubAttackerKnowledgeTheorem encrypt.attackerKnowledge where
  pf := by
    simp [encrypt.attackerKnowledge, Bytes.Publishable]
    intro _ _ _ key nonce message associatedData _ _
    grind [encrypt.Invariant, encrypt.label]

public instance : SubAttackerKnowledgeTheorem decrypt.attackerKnowledge where
  pf := by
    simp [decrypt.attackerKnowledge]
    intro out tr htr key nonce ciphertext associatedData hdec hk hn hct had
    have hout := decrypt.Invariant key nonce ciphertext associatedData out tr
      hk.1 hn.1 hct.1 had.1 hdec
    rcases hout with ⟨houtInv, houtPred | houtPub⟩
    · have hflow := EncryptPredProof.pred_key_label (key.usage tr) key nonce out associatedData tr houtPred
      exact ⟨houtInv, canFlowTrans _ _ _ _ hflow hk.2⟩
    · exact houtPub.2

#combine [BytesFunctor.Has SubF] [EncryptPred] [EncryptPredProof]
  [BytesInvariants.Has Ciphertext.invariants]
into SubAttackerKnowledgeTheorem' from
  encrypt,
  decrypt,

end AttackerKnowledgeTheorem

end DY.AEAD
