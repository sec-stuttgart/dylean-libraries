module

public import DY.Actions.ProtocolEvent
import all DY.Actions.ProtocolEvent
public import DyExtensions.Trace.Search

namespace DY.ProtocolEvent

/-- Every logged event has an earliest occurrence, even if it is logged repeatedly. -/
public theorem _root_.DY.Trace.exists_findEventTriggeredAtTimestamp
  {EventT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (tr : ExecTrace) (ev : EventT) :
  tr.EventLogged ev → ∃ i, tr.EventLoggedAt ev i ∧ ∀ j, tr.EventLoggedAt ev j → i ≤ j
:= by
  classical
  intro ⟨j, hj⟩
  let project := fun (entry : ExecTrace.Entry) => if entry = TraceEntryHas.inj (ExecEntryT.mk ev) then some () else none
  have hm : ∃ hj : j < tr.length, project (tr.at j hj) = some () := by
    simpa [Trace.EventLoggedAt, Trace.at?_eq_some, project] using hj
  cases hs : tr.searchFirstWith project with
  | none =>
    obtain ⟨hj, hm⟩ := hm
    have hn := (Trace.searchFirstWith_none tr project).mp hs j hj
    simp [hm] at hn
  | some result =>
    rcases result with ⟨i, v⟩
    obtain ⟨hi, hv, hmin⟩ := Trace.searchFirstWith_some tr project i v hs
    refine ⟨i, ?_, ?_⟩
    · simp only [Trace.EventLoggedAt, Trace.at?_eq_some]
      exact ⟨hi, by simpa [project] using hv⟩
    · intro k hk
      obtain ⟨hk, he⟩ := (Trace.at?_eq_some tr k (ExecEntryT.mk ev)).mp hk
      exact hmin k hk (by simp [project, he])

/-- The first occurrence timestamp of a logged event, independent of the witness. -/
public noncomputable def _root_.DY.Trace.findEventTriggeredAtTimestamp
  {EventT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (tr : ExecTrace) (ev : EventT) (h : tr.EventLogged ev) :
  Nat
:=
  Classical.choose (tr.exists_findEventTriggeredAtTimestamp ev h)

/-- The selected timestamp is an occurrence and precedes all other occurrences. -/
public theorem _root_.DY.Trace.findEventTriggeredAtTimestamp_spec
  {EventT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (tr : ExecTrace) (ev : EventT) (h : tr.EventLogged ev) :
  tr.EventLoggedAt ev (tr.findEventTriggeredAtTimestamp ev h) ∧
    ∀ j, tr.EventLoggedAt ev j → tr.findEventTriggeredAtTimestamp ev h ≤ j
:=
  Classical.choose_spec (tr.exists_findEventTriggeredAtTimestamp ev h)

/-- The prefix strictly before the first timestamp contains no occurrence. -/
public theorem _root_.DY.Trace.findEventTriggeredAtTimestamp_prefix
  {EventT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (tr : ExecTrace) (ev : EventT) (h : tr.EventLogged ev) :
  ¬ (tr.prefix (tr.findEventTriggeredAtTimestamp ev h)).EventLogged ev
:= by
  intro ⟨j, hj⟩
  have hlt := Trace.EventLoggedAt_implies_i_le_length ev j _ hj
  have hp := Trace.prefix_length tr (tr.findEventTriggeredAtTimestamp ev h)
  have hm := (tr.findEventTriggeredAtTimestamp_spec ev h).2 j (Trace.EventLoggedAt_le ev j _ _ (Trace.prefix_le_self _ _) hj)
  omega

/-- Trace extension preserves an event's first timestamp once it has occurred. -/
public theorem _root_.DY.Trace.findEventTriggeredAtTimestamp_later
  {EventT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT EventT)]
  (a b : ExecTrace) (ev : EventT) (ha : a.EventLogged ev) (hb : b.EventLogged ev) :
  a ≤ b → a.findEventTriggeredAtTimestamp ev ha = b.findEventTriggeredAtTimestamp ev hb
:= by
  intro hab
  obtain ⟨haAt, haMin⟩ := a.findEventTriggeredAtTimestamp_spec ev ha
  obtain ⟨hbAt, hbMin⟩ := b.findEventTriggeredAtTimestamp_spec ev hb
  have hba := hbMin _ (Trace.EventLoggedAt_le ev _ a b hab haAt)
  have hlt := Trace.EventLoggedAt_implies_i_le_length ev _ a haAt
  have hab' := haMin _ (Trace.EventLoggedAt_le' ev _ a b (by omega) hab hbAt)
  omega

end DY.ProtocolEvent
