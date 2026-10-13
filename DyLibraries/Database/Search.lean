module

public import DY.Database.Operations
import all DY.Database.Operations
import all DY.Database.Basic
import all DY.Actions.PersistentLocalUpdateableState
import all DY.Trace.Manipulation
import all DY.Trace.Monad

namespace DY.Database
open PersistentLocalUpdateableState
public section

/-- Search leaves the trace unchanged and successful results name a matching current row. -/
theorem dbFindAux_run
  {RowT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT RowT)]
  (query : RowT → Bool) (p : Participant) (ptrs : List Nat) (tr : ExecTrace) :
  ((dbFindAux query p ptrs).run tr).2.val = tr ∧
    ∀ ptr row, ((dbFindAux query p ptrs).run tr).1 = some (ptr, row) →
      ptr ∈ ptrs ∧ query row = true ∧ getRowOpt RowT tr p ptr = some row
:= by
  induction ptrs with
  | nil => simp [dbFindAux, Traceful.run_failure]
  | cons ptr ptrs ih =>
    simp only [dbFindAux, Traceful.run_bind, getLocalState, Traceful.run_mk]
    cases h : getMostRecentStateFor (StateT := RowT) tr p ptr with
    | none => simp
    | some row =>
      simp only
      split
      · simp_all [Traceful.run_pure, Traceful.run_mk, getRowOpt]
      · obtain ⟨htr, hs⟩ := ih
        refine ⟨htr, ?_⟩
        intro found value hf
        obtain ⟨hm, hq, hr⟩ := hs found value hf
        exact ⟨List.mem_cons_of_mem ptr hm, hq, hr⟩

/-- Database search is read-only, and success establishes membership and the query predicate. -/
theorem dbFind_run
  {RowT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  (p : Participant) (sid : Nat) (query : RowT → Bool) (tr : ExecTrace) :
  ((dbFind p sid query).run tr).2.val = tr ∧
    ∀ ptr row, ((dbFind p sid query).run tr).1 = some (ptr, row) →
      IsRowInDb row ptr p sid tr ∧ query row = true
:= by
  simp only [dbFind, Traceful.run_bind, getLocalState, Traceful.run_mk]
  cases h : getMostRecentStateFor (StateT := Db RowT) tr p sid with
  | none => simp
  | some db =>
    simp only
    obtain ⟨htr, hs⟩ := dbFindAux_run query p db.rows tr
    refine ⟨htr, ?_⟩
    intro ptr row hr
    obtain ⟨hp, hq, hrow⟩ := hs ptr row hr
    exact ⟨⟨db, h, hp, hrow⟩, hq⟩

/-- Successful search returns a current member satisfying the query; failure preserves the invariant too. -/
@[instance]
theorem dbFind.proof
  {RowT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  (p : Participant) (sid : Nat) (query : RowT → Bool) :
  HoareTriple (dbFind p sid query)
    (fun _ => True)
    (fun result tr => IsRowInDb result.2 result.1 p sid tr.erase ∧ query result.2 = true)
:= by
  apply HoareTriple.mk
  intro tr _ hinv
  obtain ⟨htr, hs⟩ := dbFind_run p sid query tr.erase
  simp only [wp]
  refine ⟨tr, ?_, hinv, htr, Trace.le_refl tr⟩
  cases h : ((dbFind p sid query).run tr.erase).1 with
  | none => trivial
  | some result => exact hs result.1 result.2 h

end
end DY.Database
