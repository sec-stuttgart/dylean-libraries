module

public import DY.Database.Specifications
public import DY.Database.Search
import all DY.Database.Basic
import all DY.Database.Invariants
import all DY.Database.Operations

namespace DY.Database
open PersistentLocalUpdateableState
public section

/-- In a complete table with a unique key, equal key values identify the same pointer and row. -/
theorem sessIdsInDb_sameKey_implies_sameId
  {RowT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT RowT)]
  (tr : ExecTrace) (p : Participant) (ptrs : List Nat) (ptr1 ptr2 : Nat) (row1 row2 : RowT) (key : Key RowT) :
  (getRows RowT tr p ptrs).length = ptrs.length → keyUnique (getRows RowT tr p ptrs) key = true →
    ptr1 ∈ ptrs → ptr2 ∈ ptrs → getRowOpt RowT tr p ptr1 = some row1 →
    getRowOpt RowT tr p ptr2 = some row2 → key.get row1 = key.get row2 →
    ptr1 = ptr2 ∧ row1 = row2
:= by
  induction ptrs with
  | nil => simp [getRows]
  | cons ptr ptrs ih =>
    intro hlen hk hm1 hm2 hr1 hr2 heq
    cases hr : getRowOpt RowT tr p ptr with
    | none =>
      have hb := List.length_filterMap_le (f := getRowOpt RowT tr p) (l := ptrs)
      simp [getRows, hr] at hlen
      omega
    | some row =>
      have hlen' : (getRows RowT tr p ptrs).length = ptrs.length := by simpa [getRows, hr] using hlen
      simp only [keyUnique, decide_eq_true_eq] at hk
      have hkeys : key.get row ∉ (getRows RowT tr p ptrs).map key.get ∧ ((getRows RowT tr p ptrs).map key.get).Nodup := by
        simpa [getRows, hr] using hk
      have htail : keyUnique (getRows RowT tr p ptrs) key = true := by
        simpa only [keyUnique, decide_eq_true_eq] using hkeys.2
      rcases List.mem_cons.mp hm1 with h1 | h1 <;> rcases List.mem_cons.mp hm2 with h2 | h2
      · subst ptr1; subst ptr2
        exact ⟨rfl, Option.some.inj (hr1.symm.trans hr2)⟩
      · subst ptr1
        have hrEq : row1 = row := Option.some.inj (hr1.symm.trans hr)
        have hm := mem_getRows tr p ptrs ptr2 row2 h2 hr2
        have hmem : key.get row2 ∈ (getRows RowT tr p ptrs).map key.get := List.mem_map.mpr ⟨row2, hm, rfl⟩
        exact False.elim (hkeys.1 (by simpa [← hrEq, heq] using hmem))
      · subst ptr2
        have hrEq : row2 = row := Option.some.inj (hr2.symm.trans hr)
        have hm := mem_getRows tr p ptrs ptr1 row1 h1 hr1
        have hmem : key.get row1 ∈ (getRows RowT tr p ptrs).map key.get := List.mem_map.mpr ⟨row1, hm, rfl⟩
        exact False.elim (hkeys.1 (by simpa [heq, hrEq] using hmem))
      · exact ih hlen' htail h1 h2 hr1 hr2 heq

section
variable {RowT : Type} [DbTypes RowT] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ProofTraceTypes.Has (State.ProofEntryT RowT)]
variable [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))] [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))]
variable [DbPredicate RowT]
local instance : LocalStateInv RowT := dbRowStateInvariant RowT
local instance : LocalStateInv (Db RowT) := dbStateInvariant RowT
local instance : ProtocolEvent.EventInv (DbEvent RowT) := dbEventInvariant RowT
variable [TraceInvariant.Has (State.ProofEntryT RowT)]
variable [TraceInvariant.Has (State.ProofEntryT (Db RowT))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))]

omit [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] [TraceInvariant.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] in
/-- Membership persists with a possibly updated row; table growth never removes a pointer. -/
theorem isRowInDb_hasLaterVersion
  (row : RowT) (ptr : Nat) (p : Participant) (sid : Nat) (a b : ProofTrace) :
  IsRowInDb row ptr p sid a.erase → a ≤ b → b.Invariant →
    ∃ later : RowT, IsRowInDb later ptr p sid b.erase
:= by
  rintro ⟨db, hdb, hptr, hr⟩ hab hinv
  obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p sid db a.erase hdb
  have hw' := stateWasSetAt_later p sid time db a.erase b.erase (Trace.erase_le a b hab) hw
  obtain ⟨_, current, hc, _, _⟩ := stateWasSetAt_has_mostRecentState b.erase time p sid db hw'
  have hu := mostRecentState_updatePred b p sid db current hinv ⟨time, hw'⟩ hc
  have hp : ptr ∈ current.rows := by
    change StrictSuffix db.rows current.rows ∨ db = current at hu
    rcases hu with ⟨added, _, heq⟩ | heq
    · rw [heq]; exact List.mem_append_right added hptr
    · simpa [← heq] using hptr
  obtain ⟨later, hl, _, _⟩ := getRowOpt_later p ptr row a b hab hinv hr
  exact ⟨later, current, hc, hp, hl⟩

omit [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))] [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] [TraceInvariant.Has (State.ProofEntryT (Db RowT))] [TraceInvariant.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] in
/-- Two versions at the same row ID preserve all keys and satisfy the update policy unless equal. -/
theorem isRowInDb_twice_implies_rowUpdatePred
  (row1 row2 : RowT) (ptr : Nat) (p : Participant) (sid : Nat) (a b : ProofTrace) :
  IsRowInDb row1 ptr p sid a.erase → IsRowInDb row2 ptr p sid b.erase →
    a ≤ b → b.Invariant →
    UpdatePreservesAllKeys row1 row2 ∧ (row1 = row2 ∨ DbPredicate.rowUpdatePred p row1 row2 b)
:= by
  rintro ⟨_, _, _, hr1⟩ ⟨_, _, _, hr2⟩ hab hinv
  obtain ⟨later, hl, hk, hu⟩ := getRowOpt_later p ptr row1 a b hab hinv hr1
  have heq := Option.some.inj (hl.symm.trans hr2)
  subst later
  exact ⟨hk, hu⟩

/-- Across invariant trace extensions, equal configured keys are equivalent to equal row IDs. -/
theorem isRowInDb_sameKeys_iff_sameId
  (row1 row2 : RowT) (ptr1 ptr2 : Nat) (p : Participant) (sid : Nat)
  (key : Key RowT) (a b : ProofTrace) :
  IsRowInDb row1 ptr1 p sid a.erase → IsRowInDb row2 ptr2 p sid b.erase →
    key ∈ DbTypes.keys → a ≤ b → b.Invariant →
    (ptr1 = ptr2 ↔ key.get row1 = key.get row2)
:= by
  intro h1 h2 hk hab hinv
  constructor
  · intro heq; subst ptr2
    exact (isRowInDb_twice_implies_rowUpdatePred row1 row2 ptr1 p sid a b h1 h2 hab hinv).1 key hk
  · intro heq
    obtain ⟨later, hl⟩ := isRowInDb_hasLaterVersion row1 ptr1 p sid a b h1 hab hinv
    have hkeys := (isRowInDb_twice_implies_rowUpdatePred row1 later ptr1 p sid a b h1 hl hab hinv).1 key hk
    rcases hl with ⟨db, hd, hp1, hr1⟩
    rcases h2 with ⟨db2, hd2, hp2, hr2⟩
    have hdb := Option.some.inj (hd.symm.trans hd2)
    subst db2
    obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p sid db b.erase hd
    have hevent : b.erase.EventLogged (DbEvent.mk (RowT := RowT) p sid db.rows) := stateWasSet_implies_pred b p sid db hinv ⟨time, hw⟩
    have hp := dbEventLogged_implies_predicate (DbEvent.mk (RowT := RowT) p sid db.rows) b hinv hevent
    have hunique : keyUnique (getRows RowT b.erase p db.rows) key = true := by
      have h := hp.2
      simp only [allDbKeysUnique, List.all_eq_true] at h
      exact h key hk
    exact (sessIdsInDb_sameKey_implies_sameId b.erase p db.rows ptr1 ptr2 later row2 key hp.1 hunique hp1 hp2 hr1 hr2 (hkeys.symm.trans heq)).1

/-- Rows found by the same configured key evolve according to the row-update policy. -/
theorem isRowInDb_sameKey_implies_rowUpdatePred
  (row1 row2 : RowT) (ptr1 ptr2 : Nat) (p : Participant) (sid : Nat)
  (key : Key RowT) (a b : ProofTrace) :
  IsRowInDb row1 ptr1 p sid a.erase → IsRowInDb row2 ptr2 p sid b.erase →
    key ∈ DbTypes.keys → key.get row1 = key.get row2 → a ≤ b → b.Invariant →
    UpdatePreservesAllKeys row1 row2 ∧ (row1 = row2 ∨ DbPredicate.rowUpdatePred p row1 row2 b)
:= by
  intro h1 h2 hk heq hab hinv
  have hid := (isRowInDb_sameKeys_iff_sameId row1 row2 ptr1 ptr2 p sid key a b h1 h2 hk hab hinv).mpr heq
  subst ptr2
  exact isRowInDb_twice_implies_rowUpdatePred row1 row2 ptr1 p sid a b h1 h2 hab hinv

end
end
end DY.Database
