module

public import DY.Database.Invariants
import all DY.Database.Labels
import all DY.Database.Noninterference
import all DY.Actions.PersistentLocalUpdateableState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Network
import all DY.Trace.Basic
import all DY.Trace.Manipulation
import all DY.Trace.Monad

namespace DY.Database
open PersistentLocalUpdateableState
public section

/-- Appending an entry adds exactly its matching event to the logged events. -/
theorem eventLogged_append_iff
  {EventT EntryT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)] [ExecTraceTypes.Has EntryT]
  (tr : ExecTrace) (event : EventT) (entry : EntryT) :
  (tr.append entry).EventLogged event ↔
    tr.EventLogged event ∨ (TraceEntryHas.inj entry : ExecTrace.Entry) = TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk event)
:= by
  constructor
  · rintro ⟨time, ht⟩
    obtain ⟨hi, he⟩ := (Trace.at?_eq_some _ _ _).mp ht
    by_cases htime : time = tr.length
    · right
      subst time
      simpa [Trace.append, Trace.at] using he
    · left
      have hi' : time < tr.length := by simp only [Trace.append, Trace.length] at hi; omega
      exact ⟨time, (Trace.at?_eq_some _ _ _).mpr ⟨hi', by simpa [Trace.append, Trace.at, htime] using he⟩⟩
  · rintro (h | h)
    · exact Trace.EventLogged_le event tr _ (Trace.append_le _ _) h
    · exact ⟨tr.length, (Trace.at?_eq_some _ _ _).mpr ⟨by simp [Trace.append, Trace.length], by simpa [Trace.append, Trace.at] using h⟩⟩

section
variable {RowT : Type} [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [Comparse.ParseableSerializeable RowT] [ExecTraceTypes]
variable [ExecTraceTypes.Has (State.ExecEntryT RowT)]
variable [ExecTraceTypes.Has (Compromise.ExecEntryT RowT)] [ExecTraceTypes.Has Network.ExecEntryT]

/-- Row compromise reads one address, logs its current typed value, and publishes only that value. -/
theorem compromiseRow_run
  (tr : ExecTrace) (p : Participant) (ptr : Nat) (row : RowT)
  (hrow : getMostRecentStateFor tr p ptr = some row) :
  ((compromise RowT p ptr).run tr).1 = some (tr.length + 1) ∧
    ((compromise RowT p ptr).run tr).2.val =
      (tr.append (ProtocolEvent.ExecEntryT.mk (Compromise.CompromiseEvent.mk p ptr row))).append (Network.ExecEntryT.mk (Comparse.serialize row))
:= by
  simp [compromise, getLocalState, Traceful.run_bind, Traceful.run_mk, hrow, ProtocolEvent.logEvent, appendEntry, Traceful.run_pure, Network.sendMessage, Trace.append, Trace.length]

/-- Exposing a row corrupts exactly its value label; other labels change only if already compromised. -/
theorem compromiseRow_localStateCompromised_iff
  (separate : EntriesDisjoint (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent RowT)) Network.ExecEntryT)
  (tr : ExecTrace) (p q : Participant) (ptr otherPtr : Nat) (row otherRow : RowT)
  (hrow : getMostRecentStateFor tr p ptr = some row) :
  LocalStateCompromised q otherPtr otherRow ((compromise RowT p ptr).run tr).2.val ↔
    LocalStateCompromised q otherPtr otherRow tr ∨ (q = p ∧ otherPtr = ptr ∧ otherRow = row)
:= by
  rw [(compromiseRow_run tr p ptr row hrow).2]
  simp only [LocalStateCompromised, eventLogged_append_iff]
  have hn := separate (ProtocolEvent.ExecEntryT.mk (Compromise.CompromiseEvent.mk q otherPtr otherRow)) (Network.ExecEntryT.mk (Comparse.serialize row))
  rw [or_iff_left (Ne.symm hn)]
  have heq : (TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk (Compromise.CompromiseEvent.mk p ptr row)) : ExecTrace.Entry) = TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk (Compromise.CompromiseEvent.mk q otherPtr otherRow)) ↔ p = q ∧ ptr = otherPtr ∧ row = otherRow := by
    constructor
    · intro h
      have := TraceEntryHas.inj_injective (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent RowT)) ExecTrace.Entry h
      cases this
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  rw [heq]
  simp only [eq_comm]

/-- A selected row address becomes corrupt without corrupting any other participant/address label. -/
theorem compromiseRow_stateLabel_iff
  (separate : EntriesDisjoint (ProtocolEvent.ExecEntryT (Compromise.CompromiseEvent RowT)) Network.ExecEntryT)
  (tr : ExecTrace) (p q : Participant) (ptr otherPtr : Nat) (row : RowT)
  (hrow : getMostRecentStateFor tr p ptr = some row) :
  (stateLabel RowT q otherPtr).isCorrupt ((compromise RowT p ptr).run tr).2.val ↔
    (stateLabel RowT q otherPtr).isCorrupt tr ∨ (q = p ∧ otherPtr = ptr)
:= by
  simp only [stateLabel, compromiseRow_localStateCompromised_iff separate tr p q ptr otherPtr row _ hrow]
  constructor
  · rintro ⟨value, h | ⟨hp, hid, _⟩⟩
    · exact Or.inl ⟨value, h⟩
    · exact Or.inr ⟨hp, hid⟩
  · rintro (⟨value, h⟩ | ⟨hp, hid⟩)
    · exact ⟨value, Or.inl h⟩
    · exact ⟨row, Or.inr ⟨hp, hid, rfl⟩⟩

/-- Compromising an unwritten row fails and leaves the trace unchanged. -/
theorem compromiseRow_missing
  (tr : ExecTrace) (p : Participant) (ptr : Nat)
  (hrow : getMostRecentStateFor (StateT := RowT) tr p ptr = none) :
  ((compromise RowT p ptr).run tr).1 = none ∧ ((compromise RowT p ptr).run tr).2.val = tr
:= by
  simp [compromise, getLocalState, Traceful.run_bind, Traceful.run_mk, hrow]

end
end
end DY.Database
