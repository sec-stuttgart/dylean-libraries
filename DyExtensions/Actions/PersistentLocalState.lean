module

public import DY.Actions.PersistentLocalState
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Trace.Invariant
import all DY.Trace.Manipulation

namespace DY.PersistentLocalState

public section

variable {StateT : Type}
variable [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]

/-- A participant's immutable state was stored at this trace timestamp. -/
@[expose]
def StateWasSetAt
  (tr : ExecTrace) (time : Nat) (participant : Participant) (state : StateT) :
  Prop
:=
  tr.at? time = some (PersistentGlobalState.State.ExecEntryT.mk (⟨participant, state⟩ : LocalState StateT))

/-- A participant's immutable state was stored at some point in the execution trace. -/
@[expose]
def StateWasSet
  (tr : ExecTrace) (participant : Participant) (state : StateT) :
  Prop
:=
  ∃ time, StateWasSetAt tr time participant state

/-- A stored immutable state remains recorded on every extension of the trace. -/
theorem stateWasSet_later
  (participant : Participant) (state : StateT) (a b : ExecTrace) :
  a ≤ b → StateWasSet a participant state → StateWasSet b participant state
:= by
  rintro later ⟨time, stored⟩
  refine ⟨time, ?_⟩
  unfold StateWasSetAt at stored ⊢
  have := Trace.at?_le (EntryT := PersistentGlobalState.State.ExecEntryT (LocalState StateT)) a b time later
  simpa only [stored] using this

grind_pattern [grind_later] stateWasSet_later => a ≤ b, StateWasSet a participant state

/-- A previously stored immutable state satisfies its persistent invariant on the current proof trace. -/
theorem stateWasSet_implies_pred
  [ProofTraceTypes] [TraceInvariant] [LocalStateInv StateT]
  [ProofTraceTypes.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (tr : ProofTrace) (participant : Participant) (state : StateT) :
  tr.Invariant → StateWasSet tr.erase participant state → LocalStateInv.invariant participant state tr
:= by
  rintro invariant ⟨time, stored⟩
  unfold StateWasSetAt at stored
  cases entryAt : (tr.at? time : Option (PersistentGlobalState.State.ProofEntryT (LocalState StateT))) with
  | none =>
    rw [ProofTrace.Entry.at?_eq_none_erase] at entryAt
    simp [stored] at entryAt
  | some entry =>
    have erased := ProofTrace.Entry.at?_eq_some_erase tr time entry entryAt
    have same : entry = ⟨⟨participant, state⟩⟩ := by simpa [stored, ErasableProofEntry.erase] using erased.symm
    subst entry
    have valid : SubTraceInvariant.invariant (tr.prefix time) (PersistentGlobalState.State.ExecEntryT.mk (⟨participant, state⟩ : LocalState StateT)) := by
      rw [← TraceInvariant.Has.inv_commutes]
      grind [Trace.at?_eq_some, Trace.invariant_at]
    exact LocalStateInv.invariant_later participant state _ tr (Trace.prefix_le_self tr time) valid

end
end DY.PersistentLocalState
