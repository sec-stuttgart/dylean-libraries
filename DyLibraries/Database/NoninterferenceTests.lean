module

public import DyLibraries.Database.Noninterference
import all DY.Trace.Basic

namespace DY.Database.NoninterferenceTests
public section

#combine +toplevel into ExecEntryT from
  PersistentLocalUpdateableState.State (List Nat),
  PersistentLocalUpdateableState.State Nat,
  ProtocolEvent Nat

/-- Distinct branches of the database entry sum establish row/table separation. -/
theorem tableRowDisjoint :
  EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT (List Nat)) (PersistentLocalUpdateableState.State.ExecEntryT Nat)
:= by
  apply entriesDisjoint_of_hasStep (Combined := ExecEntryT)
  intro left right heq
  have := congrArg ExecTraceTypes.combine.id heq
  change (0 : Fin 3) = 1 at this
  contradiction

/-- Events occupy a different branch from database state. -/
theorem tableEventDisjoint :
  EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT (List Nat)) (ProtocolEvent.ExecEntryT Nat)
:= by
  apply entriesDisjoint_of_hasStep (Combined := ExecEntryT)
  intro left right heq
  have := congrArg ExecTraceTypes.combine.id heq
  change (0 : Fin 3) = 2 at this
  contradiction

/-- A row may use the same numeric ID without changing the table's latest value. -/
example (tr : ExecTrace) (p : Participant) (sid row : Nat) (table : Option (List Nat)) :
  PersistentLocalUpdateableState.IsMostRecentStateFor p sid table tr →
    PersistentLocalUpdateableState.IsMostRecentStateFor p sid table ((PersistentLocalUpdateableState.setLocalState p sid row).run tr).2.val
:= by
  exact isMostRecentStateFor_setLocalState_other tableRowDisjoint p p sid sid table row tr

/-- Logging the initialization event preserves a fresh table ID. -/
example (tr : ExecTrace) (p : Participant) (sid event : Nat) :
  PersistentLocalUpdateableState.IsMostRecentStateFor (StateT := List Nat) p sid none tr →
    PersistentLocalUpdateableState.IsMostRecentStateFor (StateT := List Nat) p sid none ((ProtocolEvent.logEvent event).run tr).2.val
:= by
  exact isMostRecentStateFor_logEvent tableEventDisjoint p sid none event tr

/-- The disjointness witness also protects row addresses from table writes. -/
example (tr : ExecTrace) (p : Participant) (sid : Nat) (table : List Nat) (address : Participant × Nat) :
  ¬ Traceful.modifies (PersistentLocalUpdateableState.addressOf Nat) (PersistentLocalUpdateableState.setLocalState p sid table) tr address
:= by
  exact modifies_setLocalState_other tableRowDisjoint.symm p sid table tr address

end
end DY.Database.NoninterferenceTests
