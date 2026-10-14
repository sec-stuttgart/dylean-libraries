module

public import DY.Actions.PersistentLocalState
public import DyExtensions.Trace.Modifies
import all DY.Trace.Basic
import all DY.Trace.Invariant
import all DY.Trace.Manipulation
import DY.Meta.Step

namespace DY.PersistentLocalUpdateableState
public section

namespace State

/-- A write to a stable participant/state-ID address. -/
structure ExecEntryT (StateT : Type) where
  participant : Participant
  stateId : Nat
  state : StateT

abbrev ProofEntryT (StateT : Type) := ExecEntryT StateT

instance (StateT : Type) : ErasableProofEntry (ExecEntryT StateT) (ProofEntryT StateT) :=
  ErasableProofEntry.default (ExecEntryT StateT)

instance (StateT : Type) : ExecEntryAssociatedWithProofEntry (ExecEntryT StateT) (ProofEntryT StateT) where

/-- Storing state does not itself reveal its contents to the attacker. -/
def baseAttackerKnowledge
  [BytesFunctor] [ExecTraceTypes] (StateT : Type) :
  SubBaseAttackerKnowledge (ExecEntryT StateT)
:=
  { attackerKnows := fun _ _ _ => False }

end State

/-- Extract a write's address, ignoring entries belonging to other libraries. -/
@[expose]
def addressOf
  (StateT : Type) [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (entry : ExecTrace.Entry) : Option (Participant × Nat)
:=
  (TraceEntryHas.proj (EntryT := State.ExecEntryT StateT) entry).map (fun e => (e.participant, e.stateId))

/-- Select the contents of writes to a particular typed state address. -/
@[expose]
def stateFor
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (entry : ExecTrace.Entry) : Option StateT
:= do
  let e : State.ExecEntryT StateT ← TraceEntryHas.proj entry
  if e.participant = participant ∧ e.stateId = stateId then some e.state else none

/-- The latest state value at an address, or `none` if it has never been written. -/
@[expose]
def getMostRecentStateFor
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (participant : Participant) (stateId : Nat) : Option StateT
:=
  tr.lastValue (stateFor participant stateId)

/-- An exact assertion about the current state, including an unwritten address. -/
@[expose]
def IsMostRecentStateFor
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : Option StateT) (tr : ExecTrace) : Prop
:=
  getMostRecentStateFor tr participant stateId = state

/-- A particular value was written at the given timestamp. -/
@[expose]
def StateWasSetAt
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (time : Nat) (participant : Participant) (stateId : Nat) (state : StateT) : Prop
:=
  tr.at? time = some (State.ExecEntryT.mk participant stateId state)

/-- A historical write, which remains true after further updates. -/
@[expose]
def StateWasSet
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (participant : Participant) (stateId : Nat) (state : StateT) : Prop
:=
  ∃ time, StateWasSetAt tr time participant stateId state

/-- Filtering an entry is equivalent to projecting the corresponding typed write. -/
theorem stateFor_eq_some
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (e : ExecTrace.Entry) (s : StateT) :
  stateFor p sid e = some s ↔ e = TraceEntryHas.inj (State.ExecEntryT.mk p sid s)
:= by
  rw [← TraceEntryHas.inj_proj_eq]
  unfold stateFor
  cases h : (TraceEntryHas.proj e : Option (State.ExecEntryT StateT)) with
  | none => simp
  | some st =>
    cases st with
    | mk participant stateId state =>
      dsimp
      split <;> simp_all <;> grind

/-- The latest value is a historical write and is at least as recent as every matching write. -/
theorem isMostRecentStateFor_spec
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (s : StateT) (tr : ExecTrace) :
  IsMostRecentStateFor p sid (some s) tr →
    ∃ time, StateWasSetAt tr time p sid s ∧
      ∀ t (value : StateT), StateWasSetAt tr t p sid value → t ≤ time
:= by
  unfold IsMostRecentStateFor getMostRecentStateFor Trace.lastValue
  cases hs : tr.searchLastWith (stateFor (StateT := StateT) p sid) with
  | none => simp
  | some result =>
    rcases result with ⟨time, value⟩
    simp only [Option.map_some, Option.some.injEq]
    intro h; subst value
    obtain ⟨hi, hv, hm⟩ := Trace.searchLastWith_some tr _ time s hs
    refine ⟨time, ?_, ?_⟩
    · exact (Trace.at?_eq_some tr time _).mpr ⟨hi, (stateFor_eq_some p sid _ s).mp hv⟩
    · intro t value hw
      obtain ⟨ht, he⟩ := (Trace.at?_eq_some tr t _).mp hw
      apply hm t ht
      rw [(stateFor_eq_some p sid _ value).mpr he]
      simp

/-- Historical writes persist under trace extension. -/
theorem stateWasSet_later
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (s : StateT) (a b : ExecTrace) :
  a ≤ b → StateWasSet a p sid s → StateWasSet b p sid s
:= by
  rintro h ⟨t, ht⟩
  exact ⟨t, by have := Trace.at?_le (EntryT := State.ExecEntryT StateT) a b t h; simp_all [StateWasSetAt]⟩

grind_pattern [grind_later] stateWasSet_later => a ≤ b, StateWasSet a p sid s

/-- Latest-state facts persist when the extension does not write their address. -/
theorem isMostRecentStateFor_later
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (s : Option StateT) (a b : ExecTrace) :
  a ≤ b → IsMostRecentStateFor p sid s a →
    ¬ Trace.modifies (addressOf StateT) (b.subtract a) (p, sid) →
    IsMostRecentStateFor p sid s b
:= by
  intro h hs hm
  unfold IsMostRecentStateFor getMostRecentStateFor at *
  rw [Trace.lastValue_of_not_modifies (addressOf StateT) (stateFor p sid) (p, sid) ?_ a b h hm]
  · exact hs
  · intro e he
    unfold addressOf stateFor at *
    cases hp : (TraceEntryHas.proj e : Option (State.ExecEntryT StateT)) <;> simp_all

/-- Write a value at a stable address; update constraints are proof obligations. -/
def setLocalState
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : StateT) : Traceful Nat
:= do
  appendEntry (State.ExecEntryT.mk participant stateId state)

/-- Read the latest value, failing when the address has not been written. -/
def getLocalState
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) : Traceful StateT
:=
  Traceful.mk (fun tr => (getMostRecentStateFor tr participant stateId, ⟨tr, Trace.le_refl tr⟩))

/-- State validity and a persistent, transitive update constraint. Reflexivity is not required. -/
class LocalStateInv
  [ExecTraceTypes] [ProofTraceTypes] (StateT : Type)
where
  invariant : Participant → Nat → StateT → ProofTrace → Prop
  invariant_later : ∀ p sid s a b, a ≤ b → invariant p sid s a → invariant p sid s b
  updatePred : Participant → Nat → StateT → StateT → ProofTrace → Prop
  updatePred_later : ∀ p sid old new a b, a ≤ b → updatePred p sid old new a → updatePred p sid old new b
  updatePred_trans : ∀ p sid a b c tr, updatePred p sid a b tr → updatePred p sid b c tr → updatePred p sid a c tr

grind_pattern [grind_later] LocalStateInv.invariant_later => a ≤ b, LocalStateInv.invariant p sid s a
grind_pattern [grind_later] LocalStateInv.updatePred_later => a ≤ b, LocalStateInv.updatePred p sid old new a

namespace State

instance
  [ExecTraceTypes] [ProofTraceTypes] (StateT : Type)
  [ExecTraceTypes.Has (ExecEntryT StateT)] [LocalStateInv StateT] :
  SubTraceInvariant (ProofEntryT StateT)
where
  invariant tr e :=
    LocalStateInv.invariant e.participant e.stateId e.state tr ∧
    ∀ old, getMostRecentStateFor tr.erase e.participant e.stateId = some old →
      LocalStateInv.updatePred e.participant e.stateId old e.state tr

instance baseAttackerKnowledgeTheorem
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant] [BytesFunctor] [BytesInvariants]
  (StateT : Type) [ExecTraceTypes.Has (ExecEntryT StateT)]
  [ProofTraceTypes.Has (ProofEntryT StateT)] [LocalStateInv StateT]
  [TraceInvariant.Has (ProofEntryT StateT)] :
  SubBaseAttackerKnowledgeTheorem (ProofEntryT StateT) (baseAttackerKnowledge StateT)
where
  pf _ _ _ := by simp [baseAttackerKnowledge]

end State

/-- Appending a write makes its value the latest value at that address. -/
theorem getMostRecentStateFor_append
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (p : Participant) (sid : Nat) (s : StateT) :
  getMostRecentStateFor (tr.append (State.ExecEntryT.mk p sid s)) p sid = some s
:= by
  have h := (stateFor_eq_some p sid (TraceEntryHas.inj (State.ExecEntryT.mk p sid s)) s).mpr rfl
  simp [getMostRecentStateFor, Trace.lastValue, Trace.append, Trace.searchLastWith, h]

/-- A write preserves validity when its new value is valid and its latest predecessor permits the update. -/
@[instance]
theorem setLocalState.spec
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (p : Participant) (sid : Nat) (s : StateT) :
  HoareTriple (setLocalState p sid s)
    (fun tr => LocalStateInv.invariant p sid s tr ∧
      ∀ old, getMostRecentStateFor tr.erase p sid = some old → LocalStateInv.updatePred p sid old s tr)
    (fun time tr => StateWasSetAt tr.erase time p sid s ∧ IsMostRecentStateFor p sid (some s) tr.erase)
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, setLocalState, appendEntry, Traceful.run_mk]
  intro tr hpre hinv
  refine ⟨tr.append (State.ExecEntryT.mk p sid s), ?_⟩
  simp [Trace.append_erase, ErasableProofEntry.erase, Trace.invariant_append, SubTraceInvariant.invariant,
    hpre, hinv, Trace.append_le, StateWasSetAt, IsMostRecentStateFor, getMostRecentStateFor_append]
  exact ⟨by simpa using Trace.at?_append tr.erase (State.ExecEntryT.mk p sid s), hpre.2⟩


/-- A logged write satisfies both constraints at its original prefix. -/
theorem stateWasSetAt_invariant
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (tr : ProofTrace) (time : Nat) (p : Participant) (sid : Nat) (s : StateT) :
  tr.Invariant → StateWasSetAt tr.erase time p sid s →
    LocalStateInv.invariant p sid s (tr.prefix time) ∧
    ∀ old, getMostRecentStateFor (tr.prefix time).erase p sid = some old →
      LocalStateInv.updatePred p sid old s (tr.prefix time)
:= by
  intro hinv hw
  obtain ⟨hi, he⟩ := (Trace.at?_eq_some tr.erase time _).mp hw
  rw [Trace.erase_at] at he
  obtain ⟨entry, hentry, herase⟩ := ProofTrace.Entry.erase_eq_imp_exists.mp he
  have hi' : time < tr.length := by simpa using hi
  have hv := Trace.invariant_at tr time hi' hinv
  rw [hentry, TraceInvariant.Has.inv_commutes] at hv
  change entry = State.ExecEntryT.mk p sid s at herase
  subst entry
  exact hv

/-- Every historical value satisfies the state invariant on the current trace. -/
theorem stateWasSet_implies_pred
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (tr : ProofTrace) (p : Participant) (sid : Nat) (s : StateT) :
  tr.Invariant → StateWasSet tr.erase p sid s → LocalStateInv.invariant p sid s tr
:= by
  rintro hinv ⟨time, hw⟩
  exact LocalStateInv.invariant_later p sid s _ tr (Trace.prefix_le_self tr time) (stateWasSetAt_invariant tr time p sid s hinv hw).1

/-- A successful read returns the current value and its persistent invariant. -/
@[instance]
theorem getLocalState.spec
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (p : Participant) (sid : Nat) :
  HoareTriple (getLocalState (StateT := StateT) p sid)
    (fun _ => True)
    (fun s tr => IsMostRecentStateFor p sid (some s) tr.erase ∧ LocalStateInv.invariant p sid s tr)
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, getLocalState, Traceful.run_mk]
  intro tr _ hinv
  refine ⟨tr, ?_, hinv, rfl, Trace.le_refl tr⟩
  cases h : getMostRecentStateFor (StateT := StateT) tr.erase p sid with
  | none => trivial
  | some s =>
    refine ⟨h, stateWasSet_implies_pred tr p sid s hinv ?_⟩
    obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p sid s tr.erase h
    exact ⟨time, hw⟩

/-- Reads leave the trace unchanged, including failed reads. -/
theorem getLocalState_same_trace
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (tr : ExecTrace) :
  ((getLocalState (StateT := StateT) p sid).run tr).2.val = tr
:= by
  simp [getLocalState, Traceful.run_mk]

/-- A constrained-state write modifies precisely its own typed address. -/
theorem modifies_setLocalState
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (s : StateT) (tr : ExecTrace) (address : Participant × Nat) :
  Traceful.modifies (addressOf StateT) (setLocalState p sid s) tr address ↔ address = (p, sid)
:= by
  have hp := (TraceEntryHas.inj_proj_eq (α := ExecTrace.Entry) (TraceEntryHas.inj (State.ExecEntryT.mk p sid s)) (State.ExecEntryT.mk p sid s)).mpr rfl
  simp [Traceful.modifies, setLocalState, appendEntry, Traceful.run_mk, Trace.append,
    Trace.subtract_snoc _ _ _ (Trace.le_refl tr), Trace.modifies, addressOf, hp, eq_comm]

/-- Reading state modifies no address. -/
theorem modifies_getLocalState
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (tr : ExecTrace) (address : Participant × Nat) :
  ¬ Traceful.modifies (addressOf StateT) (getLocalState (StateT := StateT) p sid) tr address
:= by
  simp [Traceful.modifies, getLocalState_same_trace, Trace.modifies]


/-- Historical writes within a prefix can be recovered from the full trace. -/
theorem stateWasSetAt_prefix
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (time limit : Nat) (p : Participant) (sid : Nat) (s : StateT)
  (hlt : time < limit) :
  StateWasSetAt tr time p sid s → StateWasSetAt (tr.prefix limit) time p sid s
:= by
  intro hw
  obtain ⟨hi, he⟩ := (Trace.at?_eq_some tr time _).mp hw
  have hip : time < (tr.prefix limit).length := by rw [Trace.prefix_length]; omega
  apply (Trace.at?_eq_some _ _ _).mpr
  exact ⟨hip, by rw [Trace.at_le _ tr time hip (Trace.prefix_le_self tr limit)]; exact he⟩

/-- A historical write guarantees a latest value, with a timestamp no earlier than that write. -/
theorem stateWasSetAt_has_mostRecentState
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (tr : ExecTrace) (time : Nat) (p : Participant) (sid : Nat) (s : StateT) :
  StateWasSetAt tr time p sid s →
    ∃ latest, ∃ value : StateT, IsMostRecentStateFor p sid (some value) tr ∧
      StateWasSetAt tr latest p sid value ∧ time ≤ latest
:= by
  intro hw
  obtain ⟨hi, he⟩ := (Trace.at?_eq_some tr time _).mp hw
  have hf := (stateFor_eq_some p sid _ s).mpr he
  cases hs : tr.searchLastWith (stateFor (StateT := StateT) p sid) with
  | none =>
    have := (Trace.searchLastWith_none _ _).mp hs time hi
    rw [hf] at this
    contradiction
  | some result =>
    rcases result with ⟨latest, value⟩
    obtain ⟨hl, hv, hm⟩ := Trace.searchLastWith_some tr _ latest value hs
    refine ⟨latest, value, ?_, ?_, hm time hi (by simp [hf])⟩
    · simp [IsMostRecentStateFor, getMostRecentStateFor, Trace.lastValue, hs]
    · exact (Trace.at?_eq_some tr latest _).mpr ⟨hl, (stateFor_eq_some p sid _ value).mp hv⟩

/-- Two chronologically ordered writes satisfy the update constraint, even with intervening updates. -/
theorem stateWasSetTwice_implies_updatePred
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (tr : ProofTrace) (time1 time2 : Nat) (p : Participant) (sid : Nat) (s1 s2 : StateT) :
  tr.Invariant → StateWasSetAt tr.erase time1 p sid s1 →
    StateWasSetAt tr.erase time2 p sid s2 → time1 < time2 →
    LocalStateInv.updatePred p sid s1 s2 tr
:= by
  induction time2 using Nat.strongRecOn generalizing s2 with
  | ind time2 ih =>
    intro hinv h1 h2 hlt
    have hprefix := stateWasSetAt_prefix tr.erase time1 time2 p sid s1 hlt h1
    obtain ⟨latest, prev, hrecent, hprev, hle⟩ := stateWasSetAt_has_mostRecentState (tr.erase.prefix time2) time1 p sid s1 hprefix
    have hprevFull : StateWasSetAt tr.erase latest p sid prev := by
      have := Trace.at?_le (EntryT := State.ExecEntryT StateT) (tr.erase.prefix time2) tr.erase latest (Trace.prefix_le_self _ _)
      simp_all [StateWasSetAt]
    have hlatest : latest < time2 := by
      obtain ⟨hl, _⟩ := (Trace.at?_eq_some _ latest _).mp hprev
      rw [Trace.prefix_length] at hl
      omega
    have hupdate := (stateWasSetAt_invariant tr time2 p sid s2 hinv h2).2 prev (by simpa [IsMostRecentStateFor] using hrecent)
    have hupdateNow := LocalStateInv.updatePred_later p sid prev s2 _ tr (Trace.prefix_le_self tr time2) hupdate
    by_cases heq : time1 = latest
    · have hvalues : s1 = prev := by
        unfold StateWasSetAt at h1 hprevFull
        rw [heq, hprevFull] at h1
        cases h1
        rfl
      simpa [hvalues] using hupdateNow
    · exact LocalStateInv.updatePred_trans p sid s1 prev s2 tr (ih latest hlatest prev hinv h1 hprevFull (by omega)) hupdateNow

/-- A historical value either equals the latest value or is related to it by an allowed update. -/
theorem mostRecentState_updatePred
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [LocalStateInv StateT] [TraceInvariant.Has (State.ProofEntryT StateT)]
  (tr : ProofTrace) (p : Participant) (sid : Nat) (old latest : StateT) :
  tr.Invariant → StateWasSet tr.erase p sid old → IsMostRecentStateFor p sid (some latest) tr.erase →
    LocalStateInv.updatePred p sid old latest tr ∨ old = latest
:= by
  rintro hinv ⟨time, hw⟩ hlatest
  obtain ⟨last, hl, hm⟩ := isMostRecentStateFor_spec p sid latest tr.erase hlatest
  have hle := hm time old hw
  by_cases heq : time = last
  · right
    unfold StateWasSetAt at hw hl
    rw [heq, hl] at hw
    cases hw
    rfl
  · left
    exact stateWasSetTwice_implies_updatePred tr time last p sid old latest hinv hw hl (by omega)


/-- Choose an ID above every ID written by this participant in this state library. -/
@[expose]
def computeNewSessionId
  (StateT : Type) [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (tr : ExecTrace) : Nat
:=
  match tr with
  | .nil => 0
  | .snoc before entry =>
    match addressOf StateT entry with
    | some (owner, sid) =>
      if owner = p then max (computeNewSessionId StateT p before) (sid + 1)
      else computeNewSessionId StateT p before
    | none => computeNewSessionId StateT p before

/-- Fresh ID computation exceeds all previously written IDs for the participant. -/
theorem computeNewSessionId_bound
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (tr : ExecTrace) (sid : Nat) (s : StateT) (time : Nat) :
  StateWasSetAt tr time p sid s → sid < computeNewSessionId StateT p tr
:= by
  intro hw
  obtain ⟨hi, he⟩ := (Trace.at?_eq_some tr time _).mp hw
  have haddr : addressOf StateT (tr.at time hi) = some (p, sid) := by
    have hp := (TraceEntryHas.inj_proj_eq (tr.at time hi) (State.ExecEntryT.mk p sid s)).mpr he
    simp [addressOf, hp]
  clear he hw
  induction tr with
  | nil => simp [Trace.length] at hi
  | snoc tr e ih =>
    by_cases ht : time = tr.length
    · subst time
      simp only [Trace.at, dite_true] at haddr
      simp [computeNewSessionId, haddr]; omega
    · have hit : time < tr.length := by simp only [Trace.length] at hi; omega
      have haddr' : addressOf StateT (tr.at time hit) = some (p, sid) := by simpa [Trace.at, ht] using haddr
      have hb := ih hit haddr'
      unfold computeNewSessionId
      split
      · split <;> omega
      · exact hb

/-- A freshly computed ID has no current or historical value. -/
theorem computeNewSessionId_fresh
  (StateT : Type) [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (tr : ExecTrace) :
  IsMostRecentStateFor (StateT := StateT) p (computeNewSessionId StateT p tr) none tr
:= by
  cases h : getMostRecentStateFor (StateT := StateT) tr p (computeNewSessionId StateT p tr) with
  | none => exact h
  | some s =>
    obtain ⟨time, hw, _⟩ := isMostRecentStateFor_spec p _ s tr h
    have := computeNewSessionId_bound p tr _ s time hw
    omega

/-- Obtain an unwritten ID without modifying the trace. The ID is not reserved until a write. -/
def newSessionId
  (StateT : Type) [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) : Traceful Nat
:=
  Traceful.mk (fun tr => (some (computeNewSessionId StateT p tr), ⟨tr, Trace.le_refl tr⟩))

/-- Fresh-ID allocation establishes an unwritten address. -/
@[instance]
theorem newSessionId.spec
  (StateT : Type) [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] (p : Participant) :
  HoareTriple (newSessionId StateT p)
    (fun _ => True)
    (fun sid tr => IsMostRecentStateFor (StateT := StateT) p sid none tr.erase)
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, newSessionId, Traceful.run_mk]
  intro tr _ hinv
  exact ⟨tr, computeNewSessionId_fresh StateT p tr.erase, hinv, rfl, Trace.le_refl tr⟩

/-- A traceful computation preserves the current state if it does not write that address. -/
theorem traceful_isMostRecentStateFor_later
  {StateT α : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (s : Option StateT) (f : Traceful α) (tr : ExecTrace) :
  IsMostRecentStateFor p sid s tr →
    ¬ Traceful.modifies (addressOf StateT) f tr (p, sid) →
    IsMostRecentStateFor p sid s (f.run tr).2.val
:= by
  exact isMostRecentStateFor_later p sid s tr (f.run tr).2.val (f.run tr).2.property


/-- Timestamped historical writes persist under trace extension. -/
theorem stateWasSetAt_later
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid time : Nat) (s : StateT) (a b : ExecTrace) :
  a ≤ b → StateWasSetAt a time p sid s → StateWasSetAt b time p sid s
:= by
  intro h hw
  have := Trace.at?_le (EntryT := State.ExecEntryT StateT) a b time h
  unfold StateWasSetAt at hw ⊢
  simpa [hw] using this

grind_pattern [grind_later] stateWasSetAt_later => a ≤ b, StateWasSetAt a time p sid s

/-- The read result describes the exact current state, including an absent address. -/
theorem getLocalState_isMostRecentStateFor
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (sid : Nat) (tr : ExecTrace) :
  IsMostRecentStateFor p sid ((getLocalState (StateT := StateT) p sid).run tr).1 tr
:= by
  simp [getLocalState, Traceful.run_mk, IsMostRecentStateFor]

/-- Fresh-ID computation modifies no state address. -/
theorem modifies_newSessionId
  (StateT : Type) [ExecTraceTypes] [ExecTraceTypes.Has (State.ExecEntryT StateT)]
  (p : Participant) (tr : ExecTrace) (address : Participant × Nat) :
  ¬ Traceful.modifies (addressOf StateT) (newSessionId StateT p) tr address
:= by
  simp [Traceful.modifies, newSessionId, Traceful.run_mk, Trace.modifies]

namespace Compromise

/-- Exposure of a particular value at a participant's stable state address. -/
structure CompromiseEvent (StateT : Type) where
  participant : Participant
  stateId : Nat
  state : StateT

#combine (StateT : Type) into ExecEntryT, baseAttackerKnowledge from ProtocolEvent (CompromiseEvent StateT)

instance
  {StateT : Type} [ExecTraceTypes] [ProofTraceTypes] :
  ProtocolEvent.EventInv (CompromiseEvent StateT)
where
  invariant _ _ := True

#combine (StateT : Type) into
  ProofEntryT,
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem,
from
  ProtocolEvent (CompromiseEvent StateT)

end Compromise

/-- Log compromise of the current value and publish it; fail if the address is unwritten. -/
def compromise
  (StateT : Type)
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes] [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) :
  Traceful Nat
:= do
  let state ← getLocalState (StateT := StateT) participant stateId
  ProtocolEvent.logEvent ({ participant, stateId, state } : Compromise.CompromiseEvent StateT)
  Network.sendMessage (Comparse.serialize state)

/-- This value at this address has a logged compromise event. -/
def LocalStateCompromised
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : StateT) (tr : ExecTrace) :
  Prop
:=
  tr.EventLogged ({ participant, stateId, state } : Compromise.CompromiseEvent StateT)

/-- A recorded compromise persists even when the state is subsequently updated. -/
theorem LocalStateCompromised_le
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : StateT) (tr1 tr2 : ExecTrace) :
  tr1 ≤ tr2 →
    LocalStateCompromised participant stateId state tr1 →
    LocalStateCompromised participant stateId state tr2
:= by
  simp [LocalStateCompromised]
  grind

grind_pattern LocalStateCompromised_le => tr1 ≤ tr2, LocalStateCompromised participant stateId state tr1
grind_pattern [grind_later] LocalStateCompromised_le => tr1 ≤ tr2, LocalStateCompromised participant stateId state tr1

/-- The secrecy label becomes corrupt when this address and value are compromised. -/
def label
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : StateT) :
  Label
:=
  ProtocolEvent.label ({ participant, stateId, state } : Compromise.CompromiseEvent StateT)

/-- Corruption of the label is exactly the presence of its compromise event. -/
theorem label_isCorrupt
  {StateT : Type} [ExecTraceTypes] [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
  (participant : Participant) (stateId : Nat) (state : StateT) (tr : ExecTrace) :
  (label participant stateId state).isCorrupt tr = LocalStateCompromised participant stateId state tr
:= by
  grind [label, LocalStateCompromised]

grind_pattern label_isCorrupt => (label participant stateId state).isCorrupt tr

/-- Valid states can be disclosed under their address- and value-specific compromise label. -/
class CompromisableLocalStateInv
  (StateT : Type) [ExecTraceTypes] [ProofTraceTypes]
  [BytesFunctor] [BytesLength] [BytesInvariants]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)]
extends LocalStateInv StateT where
  invariant_implies_KnowableBy :
    ∀ (participant : Participant) (stateId : Nat) (state : StateT) tr,
      LocalStateInv.invariant participant stateId state tr →
      Comparse.IsWellFormed (Bytes.KnowableBy (label participant stateId state)) state tr

/-- Compromise preserves the trace invariant by logging exposure before publishing the current value. -/
@[instance]
theorem compromise.spec
  {StateT : Type} [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [ExecTraceTypes.Has Network.ExecEntryT] [ProofTraceTypes.Has Network.ProofEntryT]
  [ExecTraceTypes.Has (State.ExecEntryT StateT)] [ProofTraceTypes.Has (State.ProofEntryT StateT)]
  [ExecTraceTypes.Has (Compromise.ExecEntryT StateT)] [ProofTraceTypes.Has (Compromise.ProofEntryT StateT)]
  [BytesInvariants] [BytesInvariantsProofs] [CompromisableLocalStateInv StateT]
  [TraceInvariant.Has Network.ProofEntryT]
  [TraceInvariant.Has (State.ProofEntryT StateT)] [TraceInvariant.Has (Compromise.ProofEntryT StateT)]
  (participant : Participant) (stateId : Nat) :
  HoareTriple (compromise StateT participant stateId)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold compromise
  step
  rename_i hrecent hstate
  clear hrecent
  step by simp [ProtocolEvent.EventInv.invariant]
  step by
    have := CompromisableLocalStateInv.invariant_implies_KnowableBy participant stateId state tr
    have : (label participant stateId state).isCorrupt tr.erase := by simp_all [label, ProtocolEvent.label_isCorrupt]
    grind [Comparse.IsWellFormed, canFlowTrans]
  trivial

namespace CompromisableState

#combine (StateT : Type) into ExecEntryT, baseAttackerKnowledge from
  State StateT,
  Compromise StateT

#combine (StateT : Type) into ProofEntryT from
  State StateT,
  Compromise StateT

-- State and compromise-event entries reveal no bytes; only compromise.spec needs disclosure obligations.
#combine
  (StateT : Type)
  [ExecTraceTypes.Has (ExecEntryT StateT)] [LocalStateInv StateT]
into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem__noExecHas,
from
  State StateT,
  Compromise StateT

end CompromisableState

end
end DY.PersistentLocalUpdateableState
