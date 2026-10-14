module

public import DyExtensions.Actions.PersistentLocalUpdateableState

namespace DY.Database
public section

/-- Compromise of any state version owned by this participant in this database family. -/
def participantLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) :
  Label
:=
  { isCorrupt := fun tr => ∃ sid, ∃ content : RowT, PersistentLocalUpdateableState.LocalStateCompromised p sid content tr
    isCorruptLater := by
      rintro a b hab ⟨sid, content, h⟩
      exact ⟨sid, content, PersistentLocalUpdateableState.LocalStateCompromised_le _ _ _ a b hab h⟩ }

/-- Compromise of any content version at a database state address. -/
def stateLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) :
  Label
:=
  { isCorrupt := fun tr => ∃ content : RowT, PersistentLocalUpdateableState.LocalStateCompromised p sid content tr
    isCorruptLater := by
      rintro a b hab ⟨content, h⟩
      exact ⟨content, PersistentLocalUpdateableState.LocalStateCompromised_le _ _ _ a b hab h⟩ }

/-- Compromise of one specific typed state version, retaining row-wise compromise. -/
def stateContentLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) (content : RowT) :
  Label
:=
  PersistentLocalUpdateableState.label p sid content

/-- A participant label flows to each of that participant's state-address labels. -/
theorem participantLabel_canFlow_stateLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) (tr : ExecTrace) :
  (participantLabel RowT p).canFlow (stateLabel RowT p sid) tr
:= by
  intro later _ ⟨content, h⟩
  exact ⟨sid, content, h⟩

/-- An address label flows to each of its content-version labels. -/
theorem stateLabel_canFlow_stateContentLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) (content : RowT) (tr : ExecTrace) :
  (stateLabel RowT p sid).canFlow (stateContentLabel RowT p sid content) tr
:= by
  intro later _ h
  exact ⟨content, (PersistentLocalUpdateableState.label_isCorrupt _ _ _ later).mp h⟩

/-- Participant-knowable content is also knowable under its particular version label. -/
theorem participantLabel_canFlow_stateContentLabel
  (RowT : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (p : Participant) (sid : Nat) (content : RowT) (tr : ExecTrace) :
  (participantLabel RowT p).canFlow (stateContentLabel RowT p sid content) tr
:= by
  exact canFlowTrans _ _ _ tr (participantLabel_canFlow_stateLabel RowT p sid tr) (stateLabel_canFlow_stateContentLabel RowT p sid content tr)

end
end DY.Database
