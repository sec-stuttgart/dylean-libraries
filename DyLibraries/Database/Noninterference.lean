module

public import DyExtensions.Actions.PersistentLocalUpdateableState
public import DyExtensions.Actions.ProtocolEvent
import all DyExtensions.Actions.PersistentLocalUpdateableState
import all DyExtensions.Actions.ProtocolEvent
import all DY.Trace.Basic
import all DY.Trace.Manipulation

namespace DY.Database
public section

/-- Two entry families have disjoint images in the execution trace.
Distinct Lean types alone do not establish this property. -/
def EntriesDisjoint
  (Left Right : Type) [ExecTraceTypes]
  [ExecTraceTypes.Has Left] [ExecTraceTypes.Has Right] :
  Prop
:=
  ∀ (left : Left) (right : Right),
    (TraceEntryHas.inj left : ExecTrace.Entry) ≠ TraceEntryHas.inj right

/-- Disjointness is symmetric. -/
theorem EntriesDisjoint.symm
  {Left Right : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has Left] [ExecTraceTypes.Has Right]
  (h : EntriesDisjoint Left Right) :
  EntriesDisjoint Right Left
:= by
  intro right left heq
  exact h left right heq.symm

/-- An entry from a disjoint family cannot project to the protected family. -/
theorem EntriesDisjoint.proj_inj_eq_none
  {Left Right : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has Left] [ExecTraceTypes.Has Right]
  (h : EntriesDisjoint Left Right) (right : Right) :
  (TraceEntryHas.proj (TraceEntryHas.inj right : ExecTrace.Entry) : Option Left) = none
:= by
  cases hp : (TraceEntryHas.proj (TraceEntryHas.inj right : ExecTrace.Entry) : Option Left) with
  | none => rfl
  | some left =>
    have heq := (TraceEntryHas.inj_proj_eq (TraceEntryHas.inj right : ExecTrace.Entry) left).mp hp
    exact False.elim (h left right heq.symm)

/-- Disjoint injections into a shared entry sum remain disjoint in the ambient trace. -/
theorem entriesDisjoint_of_hasStep
  {Left Right Combined : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has Combined]
  [ExecTraceTypes.HasStep Left Combined] [ExecTraceTypes.HasStep Right Combined]
  (h : ∀ (left : Left) (right : Right),
    ExecTraceTypes.HasStep.inj (ExecEntryT2 := Combined) left ≠ ExecTraceTypes.HasStep.inj right) :
  EntriesDisjoint Left Right
:= by
  intro left right heq
  apply h left right
  exact TraceEntryHas.inj_injective Combined ExecTrace.Entry heq

/-- Appending an entry modifies an address exactly when the entry names that address. -/
theorem modifies_appendEntry
  {EntryT Address : Type} [ExecTraceTypes] [ExecTraceTypes.Has EntryT]
  (addressOf : ExecTrace.Entry → Option Address) (entry : EntryT)
  (tr : ExecTrace) (address : Address) :
  Traceful.modifies addressOf (appendEntry entry) tr address ↔
    addressOf (TraceEntryHas.inj entry) = some address
:= by
  simp [Traceful.modifies, appendEntry, Traceful.run_mk, Trace.append,
    Trace.subtract_snoc _ _ _ (Trace.le_refl tr), Trace.modifies, Trace.nil]

/-- Logging an event does not modify a state family with disjoint trace entries. -/
theorem modifies_logEvent
  {StateT EventT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (h : EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT StateT) (ProtocolEvent.ExecEntryT EventT))
  (event : EventT) (tr : ExecTrace) (address : Participant × Nat) :
  ¬ Traceful.modifies (PersistentLocalUpdateableState.addressOf StateT) (ProtocolEvent.logEvent event) tr address
:= by
  unfold ProtocolEvent.logEvent
  rw [Traceful.modifies_bind]
  simp only [modifies_appendEntry]
  have hp := h.proj_inj_eq_none (ProtocolEvent.ExecEntryT.mk event)
  simp [PersistentLocalUpdateableState.addressOf, hp, Traceful.modifies_pure, appendEntry, Traceful.run_mk]

/-- A write to a disjoint state family cannot modify any address in the protected family. -/
theorem modifies_setLocalState_other
  {StateT OtherStateT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT OtherStateT)]
  (h : EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT StateT) (PersistentLocalUpdateableState.State.ExecEntryT OtherStateT))
  (p : Participant) (sid : Nat) (state : OtherStateT) (tr : ExecTrace) (address : Participant × Nat) :
  ¬ Traceful.modifies (PersistentLocalUpdateableState.addressOf StateT) (PersistentLocalUpdateableState.setLocalState p sid state) tr address
:= by
  unfold PersistentLocalUpdateableState.setLocalState
  rw [modifies_appendEntry]
  have hp := h.proj_inj_eq_none (PersistentLocalUpdateableState.State.ExecEntryT.mk p sid state)
  simp [PersistentLocalUpdateableState.addressOf, hp]

/-- Appending a disjoint entry leaves a protected state's lookup unchanged. -/
theorem getMostRecentStateFor_append_disjoint
  {StateT EntryT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT StateT)] [ExecTraceTypes.Has EntryT]
  (h : EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT StateT) EntryT)
  (tr : ExecTrace) (p : Participant) (sid : Nat) (entry : EntryT) :
  PersistentLocalUpdateableState.getMostRecentStateFor (tr.append entry) p sid =
    PersistentLocalUpdateableState.getMostRecentStateFor (StateT := StateT) tr p sid
:= by
  have hm : ¬ Traceful.modifies (PersistentLocalUpdateableState.addressOf StateT) (appendEntry entry) tr (p, sid) := by
    rw [modifies_appendEntry]
    simp [PersistentLocalUpdateableState.addressOf, h.proj_inj_eq_none entry]
  have hs := PersistentLocalUpdateableState.traceful_isMostRecentStateFor_later p sid (PersistentLocalUpdateableState.getMostRecentStateFor (StateT := StateT) tr p sid) (appendEntry entry) tr rfl hm
  simpa [appendEntry, Traceful.run_mk, PersistentLocalUpdateableState.IsMostRecentStateFor] using hs

/-- Event logging preserves exact latest-state knowledge, including freshness (`none`). -/
theorem isMostRecentStateFor_logEvent
  {StateT EventT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (h : EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT StateT) (ProtocolEvent.ExecEntryT EventT))
  (p : Participant) (sid : Nat) (state : Option StateT) (event : EventT) (tr : ExecTrace) :
  PersistentLocalUpdateableState.IsMostRecentStateFor p sid state tr →
    PersistentLocalUpdateableState.IsMostRecentStateFor p sid state ((ProtocolEvent.logEvent event).run tr).2.val
:= by
  intro hs
  exact PersistentLocalUpdateableState.traceful_isMostRecentStateFor_later p sid state (ProtocolEvent.logEvent event) tr hs (modifies_logEvent h event tr (p, sid))

/-- Writing a disjoint state family preserves the protected address's latest value. -/
theorem isMostRecentStateFor_setLocalState_other
  {StateT OtherStateT : Type} [ExecTraceTypes]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT StateT)]
  [ExecTraceTypes.Has (PersistentLocalUpdateableState.State.ExecEntryT OtherStateT)]
  (h : EntriesDisjoint (PersistentLocalUpdateableState.State.ExecEntryT StateT) (PersistentLocalUpdateableState.State.ExecEntryT OtherStateT))
  (p writer : Participant) (sid writtenSid : Nat) (state : Option StateT) (writtenState : OtherStateT) (tr : ExecTrace) :
  PersistentLocalUpdateableState.IsMostRecentStateFor p sid state tr →
    PersistentLocalUpdateableState.IsMostRecentStateFor p sid state ((PersistentLocalUpdateableState.setLocalState writer writtenSid writtenState).run tr).2.val
:= by
  intro hs
  exact PersistentLocalUpdateableState.traceful_isMostRecentStateFor_later p sid state (PersistentLocalUpdateableState.setLocalState writer writtenSid writtenState) tr hs (modifies_setLocalState_other h writer writtenSid writtenState tr (p, sid))

end
end DY.Database
