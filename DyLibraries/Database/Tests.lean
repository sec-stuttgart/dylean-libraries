module

public import DyLibraries.Database.All
import all DyLibraries.Database.Operations
import all DyLibraries.Database.Noninterference
import all DyLibraries.Database.Basic
import all DyLibraries.Database.Invariants
import all DyExtensions.Actions.PersistentLocalUpdateableState
import all DyExtensions.Actions.ProtocolEvent
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.Basic
import all DyExtensions.Trace.Search
import DY.Meta.Step

namespace DY.Database.Tests
open PersistentLocalUpdateableState
public section

#combine +toplevel into BytesFunctor, BytesLength from Literal, Concat

abbrev Row := Nat × Nat

instance : Comparse.ParseableSerializeable Row :=
  .make (.prod .slowNat (Comparse.NonExtensibleMessageFormat.toExtensible .slowNat))

instance : DbTypes Row where
  keys := [⟨Nat, inferInstance, Prod.fst⟩]

#combine +toplevel into ExecEntryT from
  PersistentLocalUpdateableState.CompromisableState (Db Row),
  PersistentLocalUpdateableState.CompromisableState Row,
  ProtocolEvent (DbEvent Row),
  Network

#combine +toplevel into ProofEntryT from
  PersistentLocalUpdateableState.CompromisableState (Db Row),
  PersistentLocalUpdateableState.CompromisableState Row,
  ProtocolEvent (DbEvent Row),
  Network

instance : DbPredicate Row where
  rowPred _ _ _ := True
  rowPred_later _ _ _ _ _ _ := trivial
  rowUpdatePred _ old new _ := old.2 < new.2
  rowUpdatePred_later _ _ _ _ _ _ h := h
  rowUpdatePred_trans _ _ _ _ _ := Nat.lt_trans

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from Literal, Concat

instance : DbKnowable Row where
  rowPred_knowable _ _ _ _ := by simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

instance : CompromisableLocalStateInv Row := dbRowCompromisableStateInvariant Row
instance : CompromisableLocalStateInv (Db Row) := dbCompromisableStateInvariant Row
instance : ProtocolEvent.EventInv (DbEvent Row) := dbEventInvariant Row

#combine +toplevel into SubTraceInvariant from
  PersistentLocalUpdateableState.CompromisableState (Db Row),
  PersistentLocalUpdateableState.CompromisableState Row,
  ProtocolEvent (DbEvent Row),
  Network

/-- The combined entry representation separates table writes from row writes. -/
theorem tableRow : EntriesDisjoint (State.ExecEntryT (Db Row)) (State.ExecEntryT Row) := by
  intro a b h
  have h' := congrArg ExecTraceTypes.combine.id h
  change (0 : Fin 4) = 1 at h'
  contradiction

/-- The combined entry representation separates table writes from events. -/
theorem tableEvent : EntriesDisjoint (State.ExecEntryT (Db Row)) (ProtocolEvent.ExecEntryT (DbEvent Row)) := by
  intro a b h
  have h' := congrArg ExecTraceTypes.combine.id h
  change (0 : Fin 4) = 2 at h'
  contradiction

/-- The combined entry representation separates row writes from events. -/
theorem rowEvent : EntriesDisjoint (State.ExecEntryT Row) (ProtocolEvent.ExecEntryT (DbEvent Row)) := by
  intro a b h
  have h' := congrArg ExecTraceTypes.combine.id h
  change (1 : Fin 4) = 2 at h'
  contradiction

/-- Network output and row-compromise events occupy different branches. -/
theorem compromiseNetwork : EntriesDisjoint (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent Row)) Network.ExecEntryT := by
  intro a b h
  have h' := congrArg ExecTraceTypes.combine.id h
  change (1 : Fin 4) = 3 at h'
  contradiction

-- Both rows and tables use the verified compromise operation.
example (p : Participant) (ptr : Nat) :
  HoareTriple (compromise Row p ptr)
    (fun _ => True)
    (fun _ _ => True)
:= compromise.spec p ptr

example (p : Participant) (sid : Nat) :
  HoareTriple (compromise (Db Row) p sid)
    (fun _ => True)
    (fun _ _ => True)
:= compromise.spec p sid

-- These checks instantiate the specifications with the concrete configured invariants.
example (p : Participant) :
  HoareTriple (initializeDb Row p)
    (fun _ => True)
    (fun sid tr => IsMostRecentStateFor p sid (some (Db.mk (RowT := Row) [])) tr.erase)
:= initializeDb.proof tableEvent p

example (p : Participant) (sid : Nat) (row : Row) :
  HoareTriple (addRow p sid row)
    (fun _ => True)
    (fun ptr tr => IsRowInDb row ptr p sid tr.erase)
:= addRow.proof tableRow tableEvent rowEvent p sid row

-- An explicit noninterference witness can install the specification for `step`.
example (p : Participant) (sid : Nat) (row : Row) :
  HoareTriple (addRow p sid row)
    (fun _ => True)
    (fun _ _ => True)
:= by
  letI := addRow.proof tableRow tableEvent rowEvent p sid row
  apply HoareTriple.mk
  step by trivial
  trivial

private def initialized : ExecTrace := ((initializeDb Row "alice").run .nil).2.val
private def inserted : ExecTrace := ((addRow "alice" 0 ((7, 1) : Row)).run initialized).2.val
private def updated : ExecTrace := ((updateRow "alice" 0 ((7, 2) : Row)).run inserted).2.val

-- Kernel-checked executions exercise a table and row sharing numeric ID zero.
example : ((initializeDb Row "alice").run .nil).1 = some 0 := by rfl
example : ((addRow "alice" 0 ((7, 1) : Row)).run initialized).1 = some 0 := by rfl
example : ((dbFind "alice" 0 (fun row : Row => row.1 == 7)).run inserted).1 = some (0, (7, 1)) := by rfl
example : ((dbFind "alice" 0 (fun row : Row => row.1 == 7)).run updated).1 = some (0, (7, 2)) := by rfl
example : ((dbFind "alice" 0 (fun row : Row => row.1 == 99)).run inserted).1 = none := by rfl
example : ((dbFind "bob" 0 (fun _ : Row => true)).run inserted).1 = none := by rfl
example : ((addRow "alice" 0 ((7, 9) : Row)).run inserted).1 = none := by rfl
example : ((addRow "alice" 99 ((8, 1) : Row)).run inserted).1 = none := by rfl

-- Searches follow newest-inserted-first pointer order.
private def twoRows : ExecTrace := ((addRow "alice" 0 ((8, 1) : Row)).run inserted).2.val
example : ((dbFind "alice" 0 (fun _ : Row => true)).run twoRows).1 = some (1, (8, 1)) := by rfl

-- Corrupt the first of two rows: its label changes, while the other row's label does not.
example : (stateLabel Row "alice" 0).isCorrupt ((compromise Row "alice" 0).run twoRows).2.val := by
  apply (compromiseRow_stateLabel_iff compromiseNetwork twoRows "alice" "alice" 0 0 ((7, 1) : Row) rfl).mpr
  exact Or.inr ⟨rfl, rfl⟩

example :
  (stateLabel Row "alice" 1).isCorrupt ((compromise Row "alice" 0).run twoRows).2.val ↔
    (stateLabel Row "alice" 1).isCorrupt twoRows
:= by
  rw [compromiseRow_stateLabel_iff compromiseNetwork twoRows "alice" "alice" 0 1 ((7, 1) : Row) rfl]
  simp

-- A missing row neither logs an exposure nor sends a message.
example : ((compromise Row "alice" 99).run twoRows).2.val = twoRows :=
  (compromiseRow_missing twoRows "alice" 99 rfl).2

-- A dangling pointer fails the search rather than silently skipping to a later row.
private def malformed : ExecTrace :=
  (Trace.nil.append (State.ExecEntryT.mk "alice" 0 ((7, 1) : Row))).append (State.ExecEntryT.mk "alice" 0 (Db.mk (RowT := Row) [99, 0]))
example : ((dbFind "alice" 0 (fun _ : Row => true)).run malformed).1 = none := by rfl

-- Failed insertions preserve the exact trace, not just the stored row values.
example : ((addRow "alice" 0 ((7, 9) : Row)).run inserted).2.val = inserted := by
  apply addRow_failure_sameTrace
  rfl

-- Incrementing a row is allowed, but changing a configured key is not.
example (tr : ProofTrace) : LocalStateInv.updatePred "alice" 0 ((7, 1) : Row) (7, 2) tr := by
  constructor
  · change (1 : Nat) < 2
    decide
  · intro key hk
    simp only [DbTypes.keys, List.mem_cons, List.mem_nil_iff, or_false] at hk
    subst key
    rfl

example (tr : ProofTrace) : ¬ LocalStateInv.updatePred "alice" 0 ((7, 1) : Row) (8, 2) tr := by
  intro h
  have hk := h.2 ⟨Nat, inferInstance, Prod.fst⟩ (by simp [DbTypes.keys])
  change (7 : Nat) = 8 at hk
  contradiction

end
end DY.Database.Tests
