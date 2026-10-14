module

public import DyExtensions.Trace.Arithmetic
import all DY.Trace.Basic

namespace DY.Trace
public section

/-- Find the oldest entry accepted by a partial projection, retaining its timestamp. -/
@[expose]
def searchFirstWith
  (tr : Trace α) (project : α → Option β) :
  Option (Nat × β)
:=
  (tr.toArray.mapIdx (fun i e => (project e).map (i, ·))).foldl Option.or none

@[simp]
theorem searchFirstWith_nil (project : α → Option β) : searchFirstWith .nil project = none := by
  simp [searchFirstWith, nil]

/-- An appended entry supplies the first match only when earlier entries do not match. -/
@[simp]
theorem searchFirstWith_push
  (tr : Trace α) (e : α) (project : α → Option β) :
  searchFirstWith ⟨tr.toArray.push e⟩ project = (searchFirstWith tr project).or ((project e).map (tr.length, ·))
:= by
  simp [searchFirstWith, Array.mapIdx_push, length]

/-- Find the timestamp of the first entry satisfying a Boolean predicate. -/
@[expose]
def searchFirst
  (tr : Trace α) (p : α → Bool) :
  Option Nat
:=
  (searchFirstWith tr (fun e => if p e then some () else none)).map Prod.fst

/-- First-search failure means that no entry matches. -/
theorem searchFirstWith_none
  (tr : Trace α) (project : α → Option β) :
  searchFirstWith tr project = none ↔ ∀ i h, project (tr.at i h) = none
:= by
  induction tr using inductionOn with
  | nil => simp [searchFirstWith, length, nil]
  | snoc tr e ih =>
    constructor
    · intro h i hi
      have hb : searchFirstWith tr project = none := by
        cases hb : searchFirstWith tr project <;> simp_all [searchFirstWith_push]
      have he : project e = none := by
        simpa [searchFirstWith_nil, searchFirstWith_push, hb] using h
      simp only [at_rawPush]
      split
      · exact he
      · exact ih.mp hb _ _
    · intro h
      have hb : searchFirstWith tr project = none := ih.mpr (by
        intro i hi
        have := h i (by simp only [rawPush_length]; omega)
        simpa [at_rawPush, show i ≠ tr.length by omega] using this)
      have he := h tr.length (by simp [rawPush_length])
      simpa [searchFirstWith_nil, searchFirstWith_push, hb, at_rawPush] using he

/-- First search identifies an actual match and precedes every other match. -/
theorem searchFirstWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchFirstWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → i ≤ j
:= by
  induction tr using inductionOn with
  | nil => simp [searchFirstWith_nil]
  | snoc tr e ih =>
    cases hb : searchFirstWith tr project with
    | some result =>
      intro h
      have hh : result = (i, v) := by simpa [searchFirstWith_nil, searchFirstWith_push, hb] using h
      subst result
      obtain ⟨hi, hv, hm⟩ := ih hb
      refine ⟨by simp only [rawPush_length]; omega, ?_, ?_⟩
      · simpa [at_rawPush, show i ≠ tr.length by omega] using hv
      · intro j hj hjm
        by_cases he : j = tr.length
        · omega
        · apply hm j (by simp only [rawPush_length] at hj; omega)
          simpa [at_rawPush, he] using hjm
    | none =>
      intro h
      cases he : project e with
      | none => simp [searchFirstWith_push, hb, he] at h
      | some value =>
        simp only [searchFirstWith_push, hb, he, Option.map_some, Option.none_or, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨by simp [rawPush_length], by simpa [at_rawPush] using he, ?_⟩
        intro j hj hjm
        by_cases hn : tr.length ≤ j
        · exact hn
        apply False.elim
        have hjlt : j < tr.length := by omega
        have hh := (searchFirstWith_none tr project).mp hb j hjlt
        exact hjm (by simpa [at_rawPush, show j ≠ tr.length by omega] using hh)

/-- Once found, the first match is unchanged by any extension of the trace. -/
theorem searchFirstWith_later
  (a b : Trace α) (project : α → Option β) (result : Nat × β) :
  a ≤ b → searchFirstWith a project = some result → searchFirstWith b project = some result
:= by
  intro h hab
  have he := subtract_concat a b h
  rw [← he]
  induction subtract b a using inductionOn with
  | nil => simpa using hab
  | snoc suffix e ih =>
    rw [concat_rawPush, searchFirstWith_push, ih]
    rfl

/-- Find the newest entry accepted by a partial projection, retaining its timestamp. -/
@[expose]
def searchLastWith
  (tr : Trace α) (project : α → Option β) :
  Option (Nat × β)
:=
  (tr.toArray.mapIdx (fun i e => (project e).map (i, ·))).foldl (fun acc value => value.or acc) none

@[simp]
theorem searchLastWith_nil (project : α → Option β) : searchLastWith .nil project = none := by
  simp [searchLastWith, nil]

/-- A matching appended entry replaces the previous last match. -/
@[simp]
theorem searchLastWith_push
  (tr : Trace α) (e : α) (project : α → Option β) :
  searchLastWith ⟨tr.toArray.push e⟩ project = ((project e).map (tr.length, ·)).or (searchLastWith tr project)
:= by
  simp [searchLastWith, Array.mapIdx_push, length]

/-- Find the timestamp of the last entry satisfying a Boolean predicate. -/
@[expose]
def searchLast
  (tr : Trace α) (p : α → Bool) :
  Option Nat
:=
  (searchLastWith tr (fun e => if p e then some () else none)).map Prod.fst

/-- Retrieve the value of the newest matching entry. -/
@[expose]
def lastValue
  (tr : Trace α) (project : α → Option β) :
  Option β
:=
  (searchLastWith tr project).map Prod.snd

/-- Search failure means that no entry matches. -/
theorem searchLastWith_none
  (tr : Trace α) (project : α → Option β) :
  searchLastWith tr project = none ↔ ∀ i h, project (tr.at i h) = none
:= by
  induction tr using inductionOn with
  | nil => simp [searchLastWith, length, nil]
  | snoc tr e ih =>
    simp only [searchLastWith_push]
    cases he : project e with
    | none =>
      simp only [Option.map_none, Option.none_or, ih]
      constructor
      · intro h i hi
        simp only [at_rawPush]
        split
        · exact he
        · apply h
      · intro h i hi
        have := h i (by simp only [rawPush_length]; omega)
        simpa [at_rawPush, show i ≠ tr.length by omega] using this
    | some v =>
      simp only [Option.map_some, Option.some_or, Option.some_ne_none, false_iff]
      intro h
      have := h tr.length (by simp [rawPush_length])
      simp [at_rawPush, he] at this

/-- A successful search identifies an actual match and bounds every other match. -/
theorem searchLastWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchLastWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → j ≤ i
:= by
  induction tr using inductionOn with
  | nil => simp [searchLastWith_nil]
  | snoc tr e ih =>
    simp only [searchLastWith_push]
    cases he : project e with
    | some value =>
      intro h
      cases h
      refine ⟨by simp [rawPush_length], ?_, ?_⟩
      · simpa [at_rawPush] using he
      · intro j hj _; simp only [rawPush_length] at hj; omega
    | none =>
      intro h
      obtain ⟨hi, hv, hm⟩ := ih h
      refine ⟨by simp only [rawPush_length]; omega, ?_, ?_⟩
      · simpa [at_rawPush, show i ≠ tr.length by omega] using hv
      · intro j hj hmatch
        by_cases hj' : j = tr.length
        · simp [at_rawPush, hj', he] at hmatch
        · have hjlt : j < tr.length := by simp only [rawPush_length] at hj; omega
          apply hm j hjlt
          simpa [at_rawPush, hj'] using hmatch

/-- The last value on a concatenation comes from the suffix when it has a match. -/
theorem lastValue_concat
  (a b : Trace α) (project : α → Option β) :
  lastValue (concat a b) project = (lastValue b project).or (lastValue a project)
:= by
  induction b using inductionOn with
  | nil => simp [lastValue]
  | snoc b e ih =>
    rw [concat_rawPush]
    cases he : project e <;> simp_all [lastValue, searchLastWith_push]

/-- The last value on an extension changes only if its suffix contains a match. -/
theorem lastValue_subtract
  (a b : Trace α) (project : α → Option β) (h : a ≤ b) :
  lastValue b project = (lastValue (subtract b a) project).or (lastValue a project)
:= by
  rw [← lastValue_concat, subtract_concat _ _ h]

end
end DY.Trace
