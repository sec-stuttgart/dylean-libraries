module

public import DyLibraries.Database.Noninterference
public import DyLibraries.Database.Labels

namespace DY.Database
public section

/-- A database key has a decidable value type; the row type need not have decidable equality. -/
structure Key (RowT : Type) where
  Value : Type
  decEq : DecidableEq Value
  get : RowT → Value

/-- Database identity is supplied by the row type; use a wrapper type for independent families. -/
class DbTypes (RowT : Type) where
  keys : List (Key RowT)

/-- The table stores row addresses, while row contents live in separate updateable states. -/
structure Db (RowT : Type) where
  rows : List Nat

/-- Serialize the table's numeric pointers without serializing its separately stored rows. -/
instance
  (RowT : Type) [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] :
  Comparse.ParseableSerializeable (Db RowT)
:=
  .make (.triviallyIsomorphic (.list .slowNat) Db.mk Db.rows)

/-- A table's numeric pointers satisfy every compatible byte predicate. -/
theorem Db.isWellFormed
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (pre : Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (db : Db RowT) (tr : τ) :
  Comparse.IsWellFormed pre db tr
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

/-- A witness that the table's row pointers were complete and its keys unique when logged. -/
structure DbEvent (RowT : Type) where
  participant : Participant
  stateId : Nat
  rows : List Nat

/-- A key's value is unchanged by an update. -/
def UpdatePreservesKey
  (old new : RowT) (key : Key RowT) :
  Prop
:=
  key.get old = key.get new

/-- Every configured key remains immutable across an update. -/
def UpdatePreservesAllKeys
  [DbTypes RowT] (old new : RowT) :
  Prop
:=
  ∀ key ∈ DbTypes.keys (RowT := RowT), UpdatePreservesKey old new key

/-- Key preservation includes the unchanged-row case. -/
theorem updatePreservesAllKeys_refl
  [DbTypes RowT] (row : RowT) :
  UpdatePreservesAllKeys row row
:= by
  intro key _
  rfl

/-- Key preservation composes across any number of updates. -/
theorem updatePreservesAllKeys_trans
  [DbTypes RowT] (a b c : RowT) :
  UpdatePreservesAllKeys a b → UpdatePreservesAllKeys b c → UpdatePreservesAllKeys a c
:= by
  intro hab hbc key hk
  exact (hab key hk).trans (hbc key hk)

/-- Test that a key occurs at most once in the list of rows. -/
def keyUnique
  (rows : List RowT) (key : Key RowT) :
  Bool
:=
  letI := key.decEq
  decide ((rows.map key.get).Nodup)

/-- Check uniqueness for every configured key before performing any writes. -/
def allDbKeysUnique
  [DbTypes RowT] (rows : List RowT) :
  Bool
:=
  (DbTypes.keys (RowT := RowT)).all (keyUnique rows)

/-- Lookup of a row's most recent value is shared by execution and the event predicate. -/
def getRowOpt
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT RowT)]
  (tr : ExecTrace) (p : Participant) (ptr : Nat) :
  Option RowT
:=
  PersistentLocalUpdateableState.getMostRecentStateFor tr p ptr

/-- Collect existing rows in pointer order, omitting missing rows as in DY*'s `choose`. -/
def getRows
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT RowT)]
  (tr : ExecTrace) (p : Participant) (ptrs : List Nat) :
  List RowT
:=
  ptrs.filterMap (getRowOpt RowT tr p)

/-- A table event certifies complete pointers and uniqueness of every configured key. -/
def dbEventPredicate
  [DbTypes RowT] [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT RowT)]
  (tr : ExecTrace) (event : DbEvent RowT) :
  Prop
:=
  (getRows RowT tr event.participant event.rows).length = event.rows.length ∧
  allDbKeysUnique (getRows RowT tr event.participant event.rows) = true

/-- An empty database satisfies the event predicate for any key configuration. -/
theorem dbEventPredicate_empty
  [DbTypes RowT] [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT RowT)]
  (tr : ExecTrace) (p : Participant) (sid : Nat) :
  dbEventPredicate tr (DbEvent.mk (RowT := RowT) p sid [])
:= by
  simp [dbEventPredicate, getRows, allDbKeysUnique, keyUnique]

end
end DY.Database
