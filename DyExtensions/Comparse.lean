module

public import DY.Comparse
import all DY.Comparse

namespace DY.Comparse

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]

/-- Serialization preserves fieldwise knowability. -/
@[simp]
public theorem KnowableBy_serialize
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [ParseableSerializeable a]
  (label : Label) (x : a) (tr : ProofTrace) :
  (serialize x).KnowableBy label tr = IsWellFormed (Bytes.KnowableBy label) x tr
:=
  IsWellFormed_FormatRel _ _ _ _ (serialize_FormatRel x)

/-- Fieldwise knowability implies fieldwise well-formedness. -/
public theorem IsWellFormed_KnowableBy_implies_WellFormed
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  [ParseableSerializeable a]
  (label : Label) (x : a) (tr : ProofTrace) :
  IsWellFormed (Bytes.KnowableBy label) x tr → IsWellFormed Bytes.WellFormed x tr
:= by
  simp only [← KnowableBy_serialize, ← WellFormed_serialize, Bytes.KnowableBy]
  grind

grind_pattern [grind_later] IsWellFormed_KnowableBy_implies_WellFormed =>
  IsWellFormed (Bytes.KnowableBy label) x tr

/-- Fieldwise publishability persists under trace extension. -/
public theorem IsWellFormed_Publishable_later
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  [ParseableSerializeable a] (x : a) (tr1 tr2 : ProofTrace)
  (hle : tr1 ≤ tr2) (h : IsWellFormed Bytes.Publishable x tr1) :
  IsWellFormed Bytes.Publishable x tr2
:= by
  simp only [← Publishable_serialize] at h ⊢
  grind

grind_pattern [grind_later] IsWellFormed_Publishable_later =>
  tr1 ≤ tr2, IsWellFormed Bytes.Publishable x tr1

/-- Fieldwise well-formedness persists under trace extension. -/
public theorem IsWellFormed_WellFormed_later
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  [ParseableSerializeable a] (x : a) (tr1 tr2 : ProofTrace) :
  tr1 ≤ tr2 → IsWellFormed Bytes.WellFormed x tr1 → IsWellFormed Bytes.WellFormed x tr2
:= by
  simp only [← WellFormed_serialize]
  grind

grind_pattern [grind_later] IsWellFormed_WellFormed_later =>
  tr1 ≤ tr2, IsWellFormed Bytes.WellFormed x tr1

/-- Fieldwise knowability persists under trace extension. -/
public theorem IsWellFormed_KnowableBy_later
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  [ParseableSerializeable a]
  (label : Label) (x : a) (tr1 tr2 : ProofTrace) :
  tr1 ≤ tr2 → IsWellFormed (Bytes.KnowableBy label) x tr1 →
  IsWellFormed (Bytes.KnowableBy label) x tr2
:= by
  simp only [← KnowableBy_serialize, Bytes.KnowableBy]
  grind

grind_pattern [grind_later] IsWellFormed_KnowableBy_later =>
  tr1 ≤ tr2, IsWellFormed (Bytes.KnowableBy label) x tr1

/-- Fieldwise knowability follows permitted label flows. -/
public theorem IsWellFormed_KnowableBy_canFlow
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [ParseableSerializeable a]
  (source target : Label) (x : a) (tr : ProofTrace) :
  source.canFlow target tr.erase → IsWellFormed (Bytes.KnowableBy source) x tr →
  IsWellFormed (Bytes.KnowableBy target) x tr
:= by
  simp only [← KnowableBy_serialize, Bytes.KnowableBy]
  grind [canFlowTrans]

end DY.Comparse
