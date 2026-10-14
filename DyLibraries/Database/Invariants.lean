module

public import DyLibraries.Database.Basic
public import DyExtensions.Comparse
import all DyLibraries.Database.Labels

namespace DY.Database
public section

/-- Persistent row validity and a persistent, transitive row-update policy.
Key immutability is added by the database's state invariant. -/
class DbPredicate
  (RowT : Type) [ExecTraceTypes] [ProofTraceTypes]
where
  rowPred : Participant → RowT → ProofTrace → Prop
  rowPred_later : ∀ p row a b, a ≤ b → rowPred p row a → rowPred p row b
  rowUpdatePred : Participant → RowT → RowT → ProofTrace → Prop
  rowUpdatePred_later : ∀ p old new a b, a ≤ b → rowUpdatePred p old new a → rowUpdatePred p old new b
  rowUpdatePred_trans : ∀ p a b c tr, rowUpdatePred p a b tr → rowUpdatePred p b c tr → rowUpdatePred p a c tr

grind_pattern [grind_later] DbPredicate.rowPred_later => a ≤ b, DbPredicate.rowPred p row a
grind_pattern [grind_later] DbPredicate.rowUpdatePred_later => a ≤ b, DbPredicate.rowUpdatePred p old new a

/-- DY*'s `row_pred_knowable` obligation, separated from structural database invariants.
It is required when connecting database state to the compromise interface. -/
class DbKnowable
  (RowT : Type) [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable RowT]
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)] [DbPredicate RowT]
where
  rowPred_knowable : ∀ p (row : RowT) tr,
    DbPredicate.rowPred p row tr →
    Comparse.IsWellFormed (Bytes.KnowableBy (participantLabel RowT p)) row tr

/-- Row updates preserve application constraints and all database keys. -/
@[instance_reducible]
instance (priority := low) dbRowStateInvariant
  (RowT : Type) [DbTypes RowT] [ExecTraceTypes] [ProofTraceTypes] [DbPredicate RowT] :
  PersistentLocalUpdateableState.LocalStateInv RowT
:=
  { invariant := fun p _ row tr => DbPredicate.rowPred p row tr
    invariant_later := fun p _ row a b => DbPredicate.rowPred_later p row a b
    updatePred := fun p _ old new tr => DbPredicate.rowUpdatePred p old new tr ∧ UpdatePreservesAllKeys old new
    updatePred_later := by
      rintro p sid old new a b hab ⟨hu, hk⟩
      exact ⟨DbPredicate.rowUpdatePred_later p old new a b hab hu, hk⟩
    updatePred_trans := by
      rintro p sid a b c tr ⟨hab, hkab⟩ ⟨hbc, hkbc⟩
      exact ⟨DbPredicate.rowUpdatePred_trans p a b c tr hab hbc, updatePreservesAllKeys_trans a b c hkab hkbc⟩ }

/-- Valid rows can be exposed independently through the shared updateable-state compromise operation. -/
@[instance_reducible]
def dbRowCompromisableStateInvariant
  (RowT : Type) [DbTypes RowT] [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable RowT]
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  [DbPredicate RowT] [DbKnowable RowT] :
  PersistentLocalUpdateableState.CompromisableLocalStateInv RowT
:=
  { dbRowStateInvariant RowT with
    invariant_implies_KnowableBy := by
      intro p sid row tr h
      exact Comparse.IsWellFormed_KnowableBy_canFlow _ _ row tr (participantLabel_canFlow_stateContentLabel RowT p sid row tr.erase) (DbKnowable.rowPred_knowable p row tr h) }

/-- A table update prepends at least one pointer; deletion and reordering are forbidden. -/
def StrictSuffix
  (old new : List Nat) :
  Prop
:=
  ∃ added, added ≠ [] ∧ new = added ++ old

/-- Strict table growth is transitive, without requiring reflexivity. -/
theorem strictSuffix_trans
  (a b c : List Nat) :
  StrictSuffix a b → StrictSuffix b c → StrictSuffix a c
:= by
  rintro ⟨ab, hab, rfl⟩ ⟨bc, hbc, rfl⟩
  exact ⟨bc ++ ab, by simp_all, by simp [List.append_assoc]⟩

/-- Table state is justified by a logged uniqueness event and grows by strict suffix extension. -/
@[instance_reducible]
def dbStateInvariant
  (RowT : Type) [ExecTraceTypes] [ProofTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))] :
  PersistentLocalUpdateableState.LocalStateInv (Db RowT)
:=
  { invariant := fun p sid db tr => tr.erase.EventLogged (DbEvent.mk (RowT := RowT) p sid db.rows)
    invariant_later := by
      intro p sid db a b hab he
      exact Trace.EventLogged_le (DbEvent.mk (RowT := RowT) p sid db.rows) _ _ (Trace.erase_le a b hab) he
    updatePred := fun _ _ old new _ => StrictSuffix old.rows new.rows
    updatePred_later := fun _ _ _ _ _ _ _ h => h
    updatePred_trans := fun _ _ a b c _ => strictSuffix_trans a.rows b.rows c.rows }

/-- Tables contain only public numeric pointers and can be compromised without exposing row contents. -/
@[instance_reducible]
def dbCompromisableStateInvariant
  (RowT : Type) [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT (Db RowT))] :
  PersistentLocalUpdateableState.CompromisableLocalStateInv (Db RowT)
:=
  { dbStateInvariant RowT with
    invariant_implies_KnowableBy := by
      intro p sid db tr _
      exact Db.isWellFormed _ db tr }

/-- Database events record uniqueness on their own prefix; later uniqueness needs the row-update invariant. -/
@[instance_reducible]
def dbEventInvariant
  (RowT : Type) [DbTypes RowT] [ExecTraceTypes] [ProofTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT RowT)] :
  ProtocolEvent.EventInv (DbEvent RowT)
:=
  { invariant := fun tr event => dbEventPredicate tr.erase event }

end
end DY.Database
