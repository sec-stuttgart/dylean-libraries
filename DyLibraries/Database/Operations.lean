module

public import DyLibraries.Database.Basic

namespace DY.Database
open PersistentLocalUpdateableState
public section

section
variable {RowT : Type} [ExecTraceTypes]
variable [ExecTraceTypes.Has (State.ExecEntryT RowT)]
variable [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]

/-- Initialize an empty database and return its stable table ID. -/
def initializeDb
  (RowT : Type) [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
  (p : Participant) :
  Traceful Nat
:= do
  let sid ← newSessionId (Db RowT) p
  ProtocolEvent.logEvent (DbEvent.mk (RowT := RowT) p sid [])
  let _ ← setLocalState p sid (Db.mk (RowT := RowT) [])
  return sid

/-- Insert a row after checking every key; failed checks leave the trace unchanged.
IDs are scoped by state type, so row IDs may equal table IDs. -/
def addRow
  [DbTypes RowT] (p : Participant) (sid : Nat) (row : RowT) :
  Traceful Nat
:= do
  let db : Db RowT ← getLocalState p sid
  let oldRows ← Traceful.mk (fun tr => (some (getRows RowT tr p db.rows), ⟨tr, Trace.le_refl tr⟩))
  let ptr ← newSessionId RowT p
  guard (allDbKeysUnique (row :: oldRows))
  let rows := ptr :: db.rows
  let _ ← setLocalState p ptr row
  ProtocolEvent.logEvent (DbEvent.mk (RowT := RowT) p sid rows)
  let _ ← setLocalState p sid (Db.mk (RowT := RowT) rows)
  return ptr

/-- Update a row at its stable ID; validity and immutable keys are proof obligations. -/
def updateRow
  (p : Participant) (ptr : Nat) (row : RowT) :
  Traceful Unit
:= do
  let _ ← setLocalState p ptr row
  return ()

/-- Search in pointer order, failing if no match exists or an encountered pointer is missing. -/
def dbFindAux
  (query : RowT → Bool) (p : Participant) (ptrs : List Nat) :
  Traceful (Nat × RowT)
:= do
  match ptrs with
  | [] => failure
  | ptr :: rest =>
    let row : RowT ← getLocalState p ptr
    if query row then return (ptr, row)
    else dbFindAux query p rest

/-- Find the newest inserted matching row in the current database. -/
def dbFind
  (p : Participant) (sid : Nat) (query : RowT → Bool) :
  Traceful (Nat × RowT)
:= do
  let db : Db RowT ← getLocalState p sid
  dbFindAux query p db.rows

end

/-- The current table contains the pointer and the pointer currently resolves to this row. -/
def IsRowInDb
  {RowT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  (row : RowT) (ptr : Nat) (p : Participant) (sid : Nat) (tr : ExecTrace) :
  Prop
:=
  ∃ db : Db RowT, getMostRecentStateFor tr p sid = some db ∧ ptr ∈ db.rows ∧ getRowOpt RowT tr p ptr = some row

end
end DY.Database
