module

public import DY.Database.Execution
import all DY.Database.Execution
public import DY.Database.Lemmas
import all DY.Database.Operations
import all DY.Database.Invariants
import all DY.Database.Basic
import all DY.Actions.PersistentLocalUpdateableState
import all DY.Actions.ProtocolEvent
import all DY.Trace.Manipulation
import all DY.Trace.Monad
import all DY.Trace.Basic
import all DY.Trace.Invariant
import DY.Meta.Step

namespace DY.Database
open PersistentLocalUpdateableState
public section

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

omit [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))] [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))] [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] [TraceInvariant.Has (State.ProofEntryT (Db RowT))] [TraceInvariant.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] in
/-- Updating an existing row requires row validity, the application update policy, and immutable keys. -/
@[instance]
theorem updateRow.proof
  (p : Participant) (ptr : Nat) (row : RowT) :
  HoareTriple (updateRow p ptr row)
    (fun tr => DbPredicate.rowPred p row tr ∧
      ∃ old, getRowOpt RowT tr.erase p ptr = some old ∧
        DbPredicate.rowUpdatePred p old row tr ∧ UpdatePreservesAllKeys old row)
    (fun _ tr => IsMostRecentStateFor p ptr (some row) tr.erase)
:= by
  apply HoareTriple.mk
  unfold updateRow
  intro tr hpre hinv
  mark_non_monotone hpre
  step by
    simp only [LocalStateInv.invariant, LocalStateInv.updatePred]
    rcases hpre with ⟨hrow, old, hold, hu, hk⟩
    refine ⟨hrow, ?_⟩
    intro previous hp
    have heq : previous = old := by simpa [getRowOpt, hp] using hold
    subst previous
    exact ⟨hu, hk⟩
  simp only [wp, Traceful.run_pure]
  exact ⟨tr, by assumption, by assumption, rfl, Trace.le_refl tr⟩

omit [ProofTraceTypes.Has (State.ProofEntryT RowT)] [DbPredicate RowT] [TraceInvariant.Has (State.ProofEntryT RowT)] in
/-- Initialization logs a valid empty-table event and creates an unwritten table address. -/
theorem initializeDb.proof
  (disjoint : EntriesDisjoint (State.ExecEntryT (Db RowT)) (ProtocolEvent.ExecEntryT (DbEvent RowT)))
  (p : Participant) :
  HoareTriple (initializeDb RowT p)
    (fun _ => True)
    (fun sid tr => IsMostRecentStateFor p sid (some (Db.mk (RowT := RowT) [])) tr.erase)
:= by
  apply HoareTriple.mk
  intro tr _ hinv
  let sid := computeNewSessionId (Db RowT) p tr.erase
  let event := DbEvent.mk (RowT := RowT) p sid []
  let afterEvent := tr.append (ProtocolEvent.ExecEntryT.mk event)
  have hfresh : IsMostRecentStateFor (StateT := Db RowT) p sid none afterEvent.erase := by
    have h := isMostRecentStateFor_logEvent disjoint p sid none event tr.erase (computeNewSessionId_fresh (Db RowT) p tr.erase)
    simpa [ProtocolEvent.logEvent, Traceful.run_bind, appendEntry, Traceful.run_mk, Traceful.run_pure, afterEvent, Trace.append_erase, ErasableProofEntry.erase] using h
  have hev : afterEvent.Invariant := by
    rw [Trace.invariant_append]
    exact ⟨hinv, dbEventPredicate_empty tr.erase p sid⟩
  have hlogged : afterEvent.erase.EventLogged event := by
    refine ⟨tr.erase.length, ?_⟩
    simpa only [afterEvent, Trace.append_erase, ErasableProofEntry.erase, Trace.EventLoggedAt] using Trace.at?_append tr.erase (ProtocolEvent.ExecEntryT.mk event)
  have hstate : (afterEvent.append (State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) []))).Invariant := by
    rw [Trace.invariant_append]
    refine ⟨hev, hlogged, ?_⟩
    intro old hold
    change getMostRecentStateFor afterEvent.erase p sid = none at hfresh
    rw [hfresh] at hold
    contradiction
  change ∃ out : ProofTrace,
    IsMostRecentStateFor p sid (some (Db.mk (RowT := RowT) [])) out.erase ∧ out.Invariant ∧
    ((tr.erase.append (ProtocolEvent.ExecEntryT.mk event)).append (State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) []))) = out.erase ∧ tr ≤ out
  refine ⟨afterEvent.append (State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) [])), ?_, hstate, ?_, ?_⟩
  · simp [Trace.append_erase, ErasableProofEntry.erase, IsMostRecentStateFor, getMostRecentStateFor_append, sid]
  · simp [afterEvent, event, sid, Trace.append_erase, ErasableProofEntry.erase]
  · have h1 : tr ≤ afterEvent := Trace.append_le tr (ProtocolEvent.ExecEntryT.mk event)
    have h2 := Trace.append_le afterEvent (State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) []))
    exact Trace.le_trans _ _ _ h1 h2

omit [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))] [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] [TraceInvariant.Has (State.ProofEntryT (Db RowT))] [TraceInvariant.Has (ProtocolEvent.ProofEntryT (DbEvent RowT))] in
/-- Database membership implies the application's persistent row predicate. -/
theorem isRowInDb_rowPred
  (row : RowT) (ptr : Nat) (p : Participant) (sid : Nat) (tr : ProofTrace) :
  tr.Invariant → IsRowInDb row ptr p sid tr.erase → DbPredicate.rowPred p row tr
:= by
  rintro hinv ⟨db, _, _, hr⟩
  obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p ptr row tr.erase hr
  exact stateWasSet_implies_pred tr p ptr row hinv ⟨time, hw⟩

omit [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))] [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))] [TraceInvariant.Has (State.ProofEntryT (Db RowT))] in
/-- A logged database event certifies current completeness and uniqueness on an invariant trace. -/
theorem dbEventLogged_implies_predicate
  (event : DbEvent RowT) (tr : ProofTrace) :
  tr.Invariant → tr.erase.EventLogged event → dbEventPredicate tr.erase event
:= by
  intro hinv he
  obtain ⟨time, hp⟩ := Trace.EventLogged_imp_EventInv event tr hinv he
  exact dbEventPredicate_later event (tr.prefix time) tr (Trace.prefix_le_self tr time) hinv hp


omit [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))] [ProofTraceTypes.Has (State.ProofEntryT (Db RowT))] [TraceInvariant.Has (State.ProofEntryT (Db RowT))] in
/-- Adding a current row to a previously certified pointer list preserves completeness and uniqueness. -/
theorem addRow_eventPredicate
  (p : Participant) (sid ptr : Nat) (ptrs : List Nat) (row : RowT) (a b : ProofTrace) :
  a ≤ b → b.Invariant → a.erase.EventLogged (DbEvent.mk (RowT := RowT) p sid ptrs) →
    getRowOpt RowT b.erase p ptr = some row →
    allDbKeysUnique (row :: getRows RowT a.erase p ptrs) = true →
    dbEventPredicate b.erase (DbEvent.mk (RowT := RowT) p sid (ptr :: ptrs))
:= by
  intro hab hinv hev hr hk
  have hp := dbEventLogged_implies_predicate (DbEvent.mk (RowT := RowT) p sid ptrs) a (traceInvariant_before a b hab hinv) hev
  obtain ⟨hlen, hmaps⟩ := getRows_allKeysSame_later p ptrs a b hab hinv hp.1
  constructor
  · simpa [getRows, hr] using congrArg Nat.succ hlen
  · simp only [allDbKeysUnique, List.all_eq_true] at hk ⊢
    intro key hkey
    have h := hk key hkey
    unfold keyUnique at h ⊢
    simp only [decide_eq_true_eq] at h ⊢
    have hm := hmaps key hkey
    simp only [getRows, List.filterMap_cons, hr, List.map_cons] at h ⊢ hm
    rw [← hm]
    exact h


/-- Insertion preserves database invariants; key conflicts and absent tables fail without writes. -/
theorem addRow.proof
  (tableRow : EntriesDisjoint (State.ExecEntryT (Db RowT)) (State.ExecEntryT RowT))
  (tableEvent : EntriesDisjoint (State.ExecEntryT (Db RowT)) (ProtocolEvent.ExecEntryT (DbEvent RowT)))
  (rowEvent : EntriesDisjoint (State.ExecEntryT RowT) (ProtocolEvent.ExecEntryT (DbEvent RowT)))
  (p : Participant) (sid : Nat) (row : RowT) :
  HoareTriple (addRow p sid row)
    (fun tr => DbPredicate.rowPred p row tr)
    (fun ptr tr => IsRowInDb row ptr p sid tr.erase)
:= by
  apply HoareTriple.mk
  intro tr hrow hinv
  have hrun := addRow_run tr.erase p sid row
  simp only [wp]
  cases hd : getMostRecentStateFor (StateT := Db RowT) tr.erase p sid with
  | none =>
    rw [hd] at hrun
    obtain ⟨hres, htrace⟩ := Prod.mk.inj hrun
    exact ⟨tr, by simp [hres], hinv, htrace, Trace.le_refl tr⟩
  | some db =>
    rw [hd] at hrun
    by_cases hk : allDbKeysUnique (row :: getRows RowT tr.erase p db.rows) = true
    · simp only [hk, ite_true] at hrun
      obtain ⟨hres, htrace⟩ := Prod.mk.inj hrun
      let ptr := computeNewSessionId RowT p tr.erase
      let rowEntry := State.ExecEntryT.mk p ptr row
      let event := DbEvent.mk (RowT := RowT) p sid (ptr :: db.rows)
      let tableEntry := State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) (ptr :: db.rows))
      let afterRow := tr.append rowEntry
      let afterEvent := afterRow.append (ProtocolEvent.ExecEntryT.mk event)
      let out := afterEvent.append tableEntry
      have hleRow : tr ≤ afterRow := Trace.append_le tr rowEntry
      have hleEvent : afterRow ≤ afterEvent := Trace.append_le afterRow (ProtocolEvent.ExecEntryT.mk event)
      have hleOut : afterEvent ≤ out := Trace.append_le afterEvent tableEntry
      have hrowInv : afterRow.Invariant := by
        rw [Trace.invariant_append]
        refine ⟨hinv, hrow, ?_⟩
        intro old hold
        have hfresh := computeNewSessionId_fresh RowT p tr.erase
        change getMostRecentStateFor tr.erase p ptr = none at hfresh
        change getMostRecentStateFor tr.erase p ptr = some old at hold
        rw [hfresh] at hold
        contradiction
      have hcurrentRow : getRowOpt RowT afterRow.erase p ptr = some row := by
        simp [afterRow, rowEntry, Trace.append_erase, ErasableProofEntry.erase, getRowOpt, getMostRecentStateFor_append]
      obtain ⟨time, hwas, _⟩ := isMostRecentStateFor_spec p sid db tr.erase hd
      have hlogged : tr.erase.EventLogged (DbEvent.mk (RowT := RowT) p sid db.rows) :=
        stateWasSet_implies_pred tr p sid db hinv ⟨time, hwas⟩
      have heventPred := addRow_eventPredicate p sid ptr db.rows row tr afterRow hleRow hrowInv hlogged hcurrentRow hk
      have heventInv : afterEvent.Invariant := by
        rw [Trace.invariant_append]
        exact ⟨hrowInv, heventPred⟩
      have heventLogged : afterEvent.erase.EventLogged event := by
        refine ⟨afterRow.erase.length, ?_⟩
        simpa only [afterEvent, Trace.append_erase, ErasableProofEntry.erase, Trace.EventLoggedAt] using Trace.at?_append afterRow.erase (ProtocolEvent.ExecEntryT.mk event)
      have htableOld : getMostRecentStateFor afterEvent.erase p sid = some db := by
        simp only [afterEvent, afterRow, Trace.append_erase, ErasableProofEntry.erase]
        rw [getMostRecentStateFor_append_disjoint tableEvent, getMostRecentStateFor_append_disjoint tableRow]
        exact hd
      have houtInv : out.Invariant := by
        rw [Trace.invariant_append]
        refine ⟨heventInv, heventLogged, ?_⟩
        intro old hold
        change getMostRecentStateFor afterEvent.erase p sid = some old at hold
        rw [htableOld] at hold
        cases hold
        exact ⟨[ptr], by simp, rfl⟩
      refine ⟨out, ?_, houtInv, ?_, Trace.le_trans _ _ _ (Trace.le_trans _ _ _ hleRow hleEvent) hleOut⟩
      · rw [hres]
        refine ⟨Db.mk (RowT := RowT) (ptr :: db.rows), ?_, by simp [ptr], ?_⟩
        · simp [out, tableEntry, Trace.append_erase, ErasableProofEntry.erase, getMostRecentStateFor_append]
        · simp only [out, afterEvent, Trace.append_erase, ErasableProofEntry.erase, getRowOpt]
          rw [getMostRecentStateFor_append_disjoint tableRow.symm, getMostRecentStateFor_append_disjoint rowEvent]
          exact hcurrentRow
      · rw [htrace]
        simp [out, afterEvent, afterRow, rowEntry, tableEntry, event, ptr, insertionTrace, Trace.append_erase, ErasableProofEntry.erase]
    · simp only [hk] at hrun
      obtain ⟨hres, htrace⟩ := Prod.mk.inj hrun
      exact ⟨tr, by simp [hres], hinv, htrace, Trace.le_refl tr⟩

end
end
end DY.Database
