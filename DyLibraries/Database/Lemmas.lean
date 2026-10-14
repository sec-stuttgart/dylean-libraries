module

public import DyLibraries.Database.Invariants
public import DyLibraries.Database.TraceLemmas
import all DyLibraries.Database.Basic
import all DyLibraries.Database.Invariants

namespace DY.Database
open PersistentLocalUpdateableState
public section

section Rows
variable {RowT : Type} [DbTypes RowT] [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ProofTraceTypes.Has (State.ProofEntryT RowT)]
variable [DbPredicate RowT]
local instance : LocalStateInv RowT := dbRowStateInvariant RowT
variable [TraceInvariant.Has (State.ProofEntryT RowT)]

/-- An existing row has a later version with identical keys, even after intervening updates. -/
theorem getRowOpt_later
  (p : Participant) (ptr : Nat) (row : RowT) (a b : ProofTrace) :
  a ≤ b → b.Invariant → getRowOpt RowT a.erase p ptr = some row →
    ∃ later, getRowOpt RowT b.erase p ptr = some later ∧ UpdatePreservesAllKeys row later ∧
      (row = later ∨ DbPredicate.rowUpdatePred p row later b)
:= by
  intro hab hinv hrow
  obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p ptr row a.erase hrow
  have hw' := stateWasSetAt_later p ptr time row a.erase b.erase (Trace.erase_le a b hab) hw
  obtain ⟨latest, value, hv, _, _⟩ := stateWasSetAt_has_mostRecentState b.erase time p ptr row hw'
  refine ⟨value, hv, ?_⟩
  have hu := mostRecentState_updatePred b p ptr row value hinv ⟨time, hw'⟩ hv
  change (DbPredicate.rowUpdatePred p row value b ∧ UpdatePreservesAllKeys row value) ∨ row = value at hu
  rcases hu with ⟨hu, hk⟩ | heq
  · exact ⟨hk, Or.inr hu⟩
  · subst value
    exact ⟨updatePreservesAllKeys_refl row, Or.inl rfl⟩

/-- Complete row-pointer lists remain complete and retain their key sequences. -/
theorem getRows_allKeysSame_later
  (p : Participant) (ptrs : List Nat) (a b : ProofTrace) :
  a ≤ b → b.Invariant → (getRows RowT a.erase p ptrs).length = ptrs.length →
    (getRows RowT b.erase p ptrs).length = ptrs.length ∧
      ∀ key ∈ DbTypes.keys (RowT := RowT),
        (getRows RowT a.erase p ptrs).map key.get = (getRows RowT b.erase p ptrs).map key.get
:= by
  intro hab hinv
  induction ptrs with
  | nil => simp [getRows]
  | cons ptr ptrs ih =>
    simp only [getRows, List.filterMap_cons]
    cases hrow : getRowOpt RowT a.erase p ptr with
    | none =>
      have hlen := List.length_filterMap_le (f := getRowOpt RowT a.erase p) (l := ptrs)
      simp only [List.length_cons]
      omega
    | some row =>
      obtain ⟨later, hlater, hkeys, _⟩ := getRowOpt_later p ptr row a b hab hinv hrow
      simp only [hlater, List.length_cons, Nat.add_right_cancel_iff]
      intro hlen
      obtain ⟨hlen', hmaps⟩ := ih hlen
      refine ⟨hlen', ?_⟩
      intro key hk
      simp only [List.map_cons]
      simp only [getRows] at hmaps
      rw [hkeys key hk, hmaps key hk]

/-- Event validity persists on invariant traces because row updates preserve keys. -/
theorem dbEventPredicate_later
  (event : DbEvent RowT) (a b : ProofTrace) :
  a ≤ b → b.Invariant → dbEventPredicate a.erase event → dbEventPredicate b.erase event
:= by
  rintro hab hinv ⟨hlen, hkeys⟩
  obtain ⟨hlen', hmaps⟩ := getRows_allKeysSame_later event.participant event.rows a b hab hinv hlen
  refine ⟨hlen', ?_⟩
  simp only [allDbKeysUnique, List.all_eq_true] at hkeys ⊢
  intro key hk
  have h := hkeys key hk
  unfold keyUnique at h ⊢
  rw [← hmaps key hk]
  exact h

end Rows

/-- A resolved row belongs to the collected rows whenever its pointer belongs to the table. -/
theorem mem_getRows
  {RowT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT RowT)]
  (tr : ExecTrace) (p : Participant) (ptrs : List Nat) (ptr : Nat) (row : RowT) :
  ptr ∈ ptrs → getRowOpt RowT tr p ptr = some row → row ∈ getRows RowT tr p ptrs
:= by
  intro hp hr
  exact List.mem_filterMap.mpr ⟨ptr, hp, hr⟩

end
end DY.Database
