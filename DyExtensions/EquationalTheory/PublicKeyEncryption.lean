module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation

namespace DY.PublicKeyEncryption

public class CanEncrypt (Bytes : Type u) where
  pk : Bytes → Bytes
  encrypt : Bytes → Bytes → Bytes → Bytes
  decrypt : Bytes → Bytes → Err Bytes

export CanEncrypt (pk encrypt decrypt)

section Constructors

namespace Pk

public structure SubF (Bytes : Type) where
  sk : Bytes

public instance : ALaCarte.FunctorSizeOf SubF where
  sizeOf | { sk } => sizeOf sk

public instance : ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }
  toRepr | { sk } => { id := (), data := (), as := #v[sk] }
  fromRepr | { as, .. } => { sk := as[0] }
  from_to | { sk } => by rfl
  to_from | { id, data, as } => by simp_all <;> grind
  sizeOf_eq | { sk } => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance : ALaCarte.RepresentableDecidableEq SubF where
public instance : ALaCarte.RepresentableOrd SubF where
public instance : SubBytesFunctor SubF where

public def SubF.length [BytesFunctor] : Bytes.PartialLength SubF := fun _ _ => 32

end Pk

namespace Ciphertext

public structure SubF (Bytes : Type) where
  publicKey : Bytes
  nonce : Bytes
  message : Bytes

public instance : ALaCarte.FunctorSizeOf SubF where
  sizeOf | { publicKey, nonce, message } => sizeOf publicKey + sizeOf nonce + sizeOf message

public instance : ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }
  toRepr | { publicKey, nonce, message } => {
    id := (), data := (), as := #v[publicKey, nonce, message]
  }
  fromRepr | { as, .. } => {
    publicKey := as[0], nonce := as[1], message := as[2]
  }
  from_to | { publicKey, nonce, message } => by rfl
  to_from | { id, data, as } => by simp_all <;> grind
  sizeOf_eq | { publicKey, nonce, message } => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance : ALaCarte.RepresentableDecidableEq SubF where
public instance : ALaCarte.RepresentableOrd SubF where
public instance : SubBytesFunctor SubF where

public def SubF.length [BytesFunctor] : Bytes.PartialLength SubF := fun _ _ => 64

end Ciphertext

#combine into BytesFunctor, BytesLength from
  Pk,
  Ciphertext,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Pk.SubF.pack (x : Pk.SubF Bytes) := BytesView.pack x
public abbrev Ciphertext.SubF.pack (x : Ciphertext.SubF Bytes) := BytesView.pack x

public instance : CanEncrypt Bytes where
  pk sk := ({ sk } : Pk.SubF Bytes).pack
  encrypt publicKey nonce message :=
    ({ publicKey, nonce, message } : Ciphertext.SubF Bytes).pack
  decrypt sk ciphertext :=
    match ciphertext.view? Ciphertext.SubF with
    | some c => if c.publicKey = ({ sk } : Pk.SubF Bytes).pack then some c.message else none
    | none => none

@[simp]
public theorem decrypt_encrypt (sk nonce message : Bytes) :
    decrypt sk (encrypt (pk sk) nonce message) = some message := by
  simp only [decrypt, encrypt, pk]
  grind

public theorem pk_injective : Function.Injective (pk : Bytes → Bytes) := by
  intro sk1 sk2 heq
  simp only [pk] at heq
  grind

end Constructors

section AttackerKnowledge

public def pk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ sk, out = pk sk ∧ p sk

public def encrypt.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ publicKey nonce message,
    out = encrypt publicKey nonce message ∧ p publicKey ∧ p nonce ∧ p message

public def decrypt.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] :
    SubAttackerKnowledge SubF where
  pred p out := ∃ sk ciphertext,
    decrypt sk ciphertext = some out ∧ p sk ∧ p ciphertext

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  pk,
  encrypt,
  decrypt,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public theorem attacker_knows_pk (sk : Bytes) (tr : ExecTrace) :
    sk.AttackerKnows tr → (pk sk).AttackerKnows tr := by
  intro h
  apply Bytes.AttackerKnows.prove pk.attackerKnowledge
  exact ⟨sk, rfl, h⟩

public theorem attacker_knows_encrypt (publicKey nonce message : Bytes) (tr : ExecTrace) :
    publicKey.AttackerKnows tr → nonce.AttackerKnows tr → message.AttackerKnows tr →
    (encrypt publicKey nonce message).AttackerKnows tr := by
  intro hpk hn hm
  apply Bytes.AttackerKnows.prove encrypt.attackerKnowledge
  refine ⟨publicKey, nonce, message, rfl, ?_⟩
  exact ⟨hpk, hn, hm⟩

public theorem attacker_knows_decrypt (sk ciphertext message : Bytes) (tr : ExecTrace) :
    sk.AttackerKnows tr → ciphertext.AttackerKnows tr →
    decrypt sk ciphertext = some message → message.AttackerKnows tr := by
  intro hsk hct hdec
  apply Bytes.AttackerKnows.prove decrypt.attackerKnowledge
  simp [decrypt.attackerKnowledge]
  exact ⟨sk, ciphertext, hdec, hsk, hct⟩

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor]

public class EncryptPred where
  pred : [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

public class EncryptPredProof
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesInvariants] [EncryptPred] where
  pred_later : [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ usage publicKey message tr1 tr2,
      publicKey.WellFormed tr1 → message.WellFormed tr1 → tr1 ≤ tr2 →
      EncryptPred.pred usage publicKey message tr1 → EncryptPred.pred usage publicKey message tr2
  pred_key_label : ∀ usage sk message tr,
    EncryptPred.pred usage (pk sk) message tr →
    (message.label tr).canFlow (sk.label tr) tr.erase

grind_pattern EncryptPredProof.pred_later => tr1 ≤ tr2, EncryptPred.pred usage publicKey message tr1

public def Pk.invariants : Bytes.PartialInvariants Pk.SubF where
  well_formed := fun { sk := sk } rec tr => (rec sk) tr
  usage := fun _ _ _ => Usage.nothing
  label := fun _ _ _ => Label.pub
  invariant := fun { sk := sk } rec tr => (rec sk) tr

public theorem Pk.invariantsProofs [BytesInvariants] :
    Bytes.PartialInvariantsProofs Pk.invariants where

/-- Recover the actual secret-key usage; non-public-key values have no key usage. -/
public def keyUsage
  [BytesFunctor.Has SubF] [GetUsage] (publicKey : Bytes) (tr : ProofTrace) :
  Usage
:=
  match publicKey.view? Pk.SubF with
  | some key => key.sk.usage tr
  | none => Usage.nothing

/-- Public-key encryption selects its policy using the secret key's usage. -/
@[simp] public theorem keyUsage_pk
  [BytesFunctor.Has SubF] [GetUsage] (sk : Bytes) (tr : ProofTrace) :
  keyUsage (pk sk) tr = sk.usage tr
:= by
  simp only [keyUsage, pk]
  grind

/-- Usage selection remains stable when a well-formed key's trace grows. -/
public theorem keyUsage_later
  [BytesFunctor.Has SubF] [BytesInvariants] [BytesInvariants.Has Pk.invariants] [GetUsageLater]
  (publicKey : Bytes) (tr1 tr2 : ProofTrace)
  (hw : publicKey.WellFormed tr1) (hle : tr1 ≤ tr2) :
  keyUsage publicKey tr1 = keyUsage publicKey tr2
:= by
  unfold keyUsage
  split
  · rename_i key hk
    have heq := Bytes.pack_view? Pk.SubF publicKey
    simp only [hk] at heq
    subst publicKey
    have hsk : key.sk.WellFormed tr1 := by
      simpa [Bytes.WellFormed.eq, Pk.invariants] using hw
    exact Bytes.usage_later _ _ _ hle hsk
  · rfl

public def Ciphertext.invariants [BytesFunctor.Has PublicKeyEncryption.SubF] [EncryptPred] : Bytes.PartialInvariants Ciphertext.SubF where
  well_formed := fun { publicKey, nonce, message } rec tr =>
    (rec publicKey) tr ∧ (rec nonce) tr ∧ (rec message) tr
  usage := fun _ _ _ => Usage.nothing
  label := fun _ _ _ => Label.pub
  invariant := fun { publicKey, nonce, message } rec tr =>
    (rec publicKey) tr ∧ (rec nonce) tr ∧ (rec message) tr ∧
    (EncryptPred.pred (keyUsage publicKey tr) publicKey message tr ∨
      (message.label tr).canFlow Label.pub tr.erase)

public theorem Ciphertext.invariantsProofs
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesInvariants] [BytesInvariants.Has Pk.invariants]
    [EncryptPred] [EncryptPredProof] :
    Bytes.PartialInvariantsProofs Ciphertext.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [Ciphertext.invariants, ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind [keyUsage_later]

set_option linter.unusedSectionVars false in
#combine [BytesFunctor.Has SubF] [EncryptPred] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Pk.invariants] [EncryptPredProof]
from
  Pk,
  Ciphertext,

variable [BytesFunctor.Has SubF]

@[simp]
public theorem pk.WellFormed [BytesInvariants] [BytesInvariants.Has Pk.invariants]
    (sk : Bytes) (tr : ProofTrace) : (pk sk).WellFormed tr = sk.WellFormed tr := by
  simp [pk, Bytes.WellFormed.eq, Pk.invariants]

@[simp]
public theorem pk.label [BytesInvariants] [BytesInvariants.Has Pk.invariants]
    (sk : Bytes) (tr : ProofTrace) : (pk sk).label tr = Label.pub := by
  simp [pk, Bytes.label.eq, Pk.invariants]

@[simp]
public theorem pk.Invariant [BytesInvariants] [BytesInvariants.Has Pk.invariants]
    (sk : Bytes) (tr : ProofTrace) : sk.Invariant tr → (pk sk).Invariant tr := by
  simp [pk, Bytes.Invariant.eq, Pk.invariants]

@[simp]
public theorem encrypt.WellFormed [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (publicKey nonce message : Bytes) (tr : ProofTrace) :
    (encrypt publicKey nonce message).WellFormed tr =
      (publicKey.WellFormed tr ∧ nonce.WellFormed tr ∧ message.WellFormed tr) := by
  simp [encrypt, Bytes.WellFormed.eq, Ciphertext.invariants]

@[simp]
public theorem encrypt.label [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (publicKey nonce message : Bytes) (tr : ProofTrace) :
    (encrypt publicKey nonce message).label tr = Label.pub := by
  simp [encrypt, Bytes.label.eq, Ciphertext.invariants]

public theorem encrypt.Invariant [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (publicKey nonce message : Bytes) (tr : ProofTrace) :
    publicKey.Invariant tr → nonce.Invariant tr → message.Invariant tr →
    (EncryptPred.pred (keyUsage publicKey tr) publicKey message tr ∨ message.Publishable tr) →
    (encrypt publicKey nonce message).Invariant tr := by
  simp [encrypt, Bytes.Invariant.eq, Ciphertext.invariants, Bytes.Publishable]
  grind

public theorem decrypt.Invariant [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (sk ciphertext message : Bytes) (tr : ProofTrace) :
    sk.Invariant tr → ciphertext.Invariant tr → decrypt sk ciphertext = some message →
    message.Invariant tr ∧
      (EncryptPred.pred (sk.usage tr) (pk sk) message tr ∨ message.Publishable tr) := by
  intro hsk hct hdec
  simp [decrypt] at hdec
  split at hdec <;> try contradiction
  rename_i c hc
  split at hdec <;> try contradiction
  rename_i hpk
  have hm : c.message = message := by grind
  subst message
  have hview := Bytes.pack_view? Ciphertext.SubF ciphertext
  simp only [hc] at hview
  subst hview
  simp [Bytes.Invariant.eq, Ciphertext.invariants] at hct
  change c.publicKey = pk sk at hpk
  rw [hpk, keyUsage_pk] at hct
  rcases hct with ⟨_, _, hmInv, hpred | hpub⟩
  · exact ⟨hmInv, Or.inl hpred⟩
  · exact ⟨hmInv, Or.inr ⟨hmInv, hpub⟩⟩

end Invariants

section HoareTriples

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes]

public instance [BytesInvariants] [BytesInvariants.Has Pk.invariants] (sk : Bytes) :
    HoareTriplePure (pk sk)
      (fun tr => sk.Invariant tr)
      (fun res tr => res.Invariant tr ∧ res.label tr = Label.pub) where
  pf := by grind [pk.Invariant, pk.label]

public instance [EncryptPred] [BytesInvariants]
    [BytesInvariants.Has Ciphertext.invariants]
    (publicKey nonce message : Bytes) :
    HoareTriplePure (encrypt publicKey nonce message)
      (fun tr => publicKey.Invariant tr ∧ nonce.Invariant tr ∧ message.Invariant tr ∧
        (EncryptPred.pred (keyUsage publicKey tr) publicKey message tr ∨ message.Publishable tr))
      (fun res tr => res.Invariant tr ∧ res.label tr = Label.pub) where
  pf := by grind [encrypt.Invariant, encrypt.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants] [EncryptPred] [EncryptPredProof]
variable [BytesInvariants.Has Pk.invariants] [BytesInvariants.Has Ciphertext.invariants]

public instance : SubAttackerKnowledgeTheorem pk.attackerKnowledge where
  pf := by
    simp [pk.attackerKnowledge, Bytes.Publishable]
    grind [pk.Invariant, pk.label]

public instance : SubAttackerKnowledgeTheorem encrypt.attackerKnowledge where
  pf := by
    simp [encrypt.attackerKnowledge, Bytes.Publishable]
    intro _ _ _ publicKey nonce message _ _
    grind [encrypt.Invariant, encrypt.label]

public instance : SubAttackerKnowledgeTheorem decrypt.attackerKnowledge where
  pf := by
    simp [decrypt.attackerKnowledge]
    intro out tr htr sk ciphertext hdec hsk hct
    have hout := decrypt.Invariant sk ciphertext out tr hsk.1 hct.1 hdec
    rcases hout with ⟨houtInv, houtPred | houtPub⟩
    · have hflow := EncryptPredProof.pred_key_label (sk.usage tr) sk out tr houtPred
      exact ⟨houtInv, canFlowTrans _ _ _ _ hflow hsk.2⟩
    · exact houtPub

#combine [BytesFunctor.Has SubF] [EncryptPred] [EncryptPredProof]
  [BytesInvariants.Has Pk.invariants] [BytesInvariants.Has Ciphertext.invariants]
into SubAttackerKnowledgeTheorem' from
  pk,
  encrypt,
  decrypt,

end AttackerKnowledgeTheorem

end DY.PublicKeyEncryption
