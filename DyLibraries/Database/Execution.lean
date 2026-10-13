module

public import DY.Database.Operations
import all DY.Database.Operations
import all DY.Actions.PersistentLocalUpdateableState
import all DY.Actions.ProtocolEvent
import all DY.Trace.Manipulation
import all DY.Trace.Monad
import all DY.Trace.Basic

namespace DY.Database
open PersistentLocalUpdateableState
public section

/-- The successful insertion trace writes the row, records the event, then updates the table. -/
def insertionTrace
  {RowT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
  (tr : ExecTrace) (p : Participant) (sid ptr : Nat) (row : RowT) (ptrs : List Nat) :
  ExecTrace
:=
  ((tr.append (State.ExecEntryT.mk p ptr row)).append (ProtocolEvent.ExecEntryT.mk (DbEvent.mk (RowT := RowT) p sid (ptr :: ptrs)))).append (State.ExecEntryT.mk p sid (Db.mk (RowT := RowT) (ptr :: ptrs)))

/-- Insertion checks the table and keys before producing any writes. -/
theorem addRow_run
  {RowT : Type} [DbTypes RowT] [ExecTraceTypes]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
  (tr : ExecTrace) (p : Participant) (sid : Nat) (row : RowT) :
  let result := (addRow p sid row).run tr
  (result.1, result.2.val) =
    match getMostRecentStateFor (StateT := Db RowT) tr p sid with
    | none => (none, tr)
    | some db =>
      if allDbKeysUnique (row :: getRows RowT tr p db.rows) then
        let ptr := computeNewSessionId RowT p tr
        (some ptr, insertionTrace tr p sid ptr row db.rows)
      else (none, tr)
:= by
  cases hd : getMostRecentStateFor (StateT := Db RowT) tr p sid with
  | none => simp [addRow, Traceful.run_bind, getLocalState, Traceful.run_mk, hd]
  | some db =>
    cases hk : allDbKeysUnique (row :: getRows RowT tr p db.rows) <;>
      simp [addRow, Traceful.run_bind, getLocalState, newSessionId, Traceful.run_mk, hd, hk, guard,
        ProtocolEvent.logEvent, setLocalState, appendEntry, Traceful.run_pure, Traceful.run_failure, insertionTrace]

/-- Failed insertions leave the trace unchanged. -/
theorem addRow_failure_sameTrace
  {RowT : Type} [DbTypes RowT] [ExecTraceTypes]
  [ExecTraceTypes.Has (State.ExecEntryT RowT)] [ExecTraceTypes.Has (State.ExecEntryT (Db RowT))]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (DbEvent RowT))]
  (tr : ExecTrace) (p : Participant) (sid : Nat) (row : RowT) :
  ((addRow p sid row).run tr).1 = none → ((addRow p sid row).run tr).2.val = tr
:= by
  have h := addRow_run tr p sid row
  cases hd : getMostRecentStateFor (StateT := Db RowT) tr p sid <;> simp only [hd] at h
  · intro _; exact (Prod.mk.inj h).2
  · split at h
    · intro hf; have := (Prod.mk.inj h).1; simp_all
    · intro _; exact (Prod.mk.inj h).2

end
end DY.Database
