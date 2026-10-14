module

import all DyLibraries.Database.Basic
import all DyLibraries.Database.Invariants

namespace DY.Database.BasicTests

private def nameKey : Key (String × Nat) := ⟨String, inferInstance, Prod.fst⟩
private def numberKey : Key (String × Nat) := ⟨Nat, inferInstance, Prod.snd⟩

private instance : DbTypes (String × Nat) where
  keys := [nameKey, numberKey]

-- Each configured key must be independently unique, rather than only the tuple.
example : allDbKeysUnique [("alice", 1), ("bob", 2)] = true := by rfl
example : allDbKeysUnique [("alice", 1), ("alice", 2)] = false := by rfl
example : allDbKeysUnique [("alice", 1), ("bob", 1)] = false := by rfl
example : allDbKeysUnique (RowT := String × Nat) [] = true := by rfl

-- Table updates must grow strictly at the front; an unchanged table is not an update.
example : StrictSuffix [1, 2] [3, 1, 2] := ⟨[3], by simp, rfl⟩
example (rows : List Nat) : ¬ StrictSuffix rows rows := by
  rintro ⟨added, hne, heq⟩
  have := congrArg List.length heq
  simp only [List.length_append] at this
  have : added.length = 0 := by omega
  cases added with
  | nil => exact hne rfl
  | cons head tail => simp at this

-- Version compromise implies participant compromise by the proved flow relation.
example (RowT : Type) [BytesFunctor] [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) (content : RowT) (tr : ExecTrace) :
  (stateContentLabel RowT p sid content).isCorrupt tr → (participantLabel RowT p).isCorrupt tr
:= by
  exact participantLabel_canFlow_stateContentLabel RowT p sid content tr tr (Trace.le_refl tr)

end DY.Database.BasicTests
