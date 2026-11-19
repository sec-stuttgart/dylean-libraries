module

public import DyExtensions.Actions.PersistentLocalUpdateableState

namespace DY.Database
public section

/-- A value is exposed when any compromised row version contains it in the selected field. -/
def valueCompromised
  {RowT ValueT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (field : RowT → ValueT) (value : ValueT) (tr : ExecTrace) :
  Prop
:=
  ∃ holder rowId, ∃ row : RowT, field row = value ∧ PersistentLocalUpdateableState.LocalStateCompromised holder rowId row tr

/-- Exposure of a selected field value persists on every extension of the trace. -/
theorem valueCompromised.later
  {RowT ValueT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (field : RowT → ValueT) (value : ValueT) (a b : ExecTrace) :
  a ≤ b → valueCompromised field value a → valueCompromised field value b
:= by
  rintro later ⟨holder, rowId, row, same, compromised⟩
  exact ⟨holder, rowId, row, same, PersistentLocalUpdateableState.LocalStateCompromised_le _ _ _ a b later compromised⟩

grind_pattern [grind_later] valueCompromised.later => a ≤ b, valueCompromised field value a

/-- A value label accounts for every compromised row version sharing the selected field value. -/
def valueLabel
  {RowT ValueT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (field : RowT → ValueT) (value : ValueT) :
  Label
:=
  { isCorrupt := valueCompromised field value
    isCorruptLater := valueCompromised.later field value }

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

/-- A value label flows to the label for any exact row version containing that value. -/
theorem valueLabel_canFlow_stateContentLabel
  {RowT ValueT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.Compromise.ExecEntryT RowT)]
  (field : RowT → ValueT) (p : Participant) (sid : Nat) (content : RowT) (tr : ExecTrace) :
  (valueLabel field (field content)).canFlow (stateContentLabel RowT p sid content) tr
:= by
  intro later _ compromised
  exact ⟨p, sid, content, rfl, (PersistentLocalUpdateableState.label_isCorrupt _ _ _ later).mp compromised⟩

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
