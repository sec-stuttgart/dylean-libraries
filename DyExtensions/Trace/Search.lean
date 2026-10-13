module

public import DY.Trace.Arithmetic
import all DY.Trace.Basic

namespace DY.Trace
public section

/-- Find the oldest entry accepted by a partial projection, retaining its timestamp. -/
@[expose]
def searchFirstWith
  (tr : Trace α) (project : α → Option β) :
  Option (Nat × β)
:=
  match tr with
  | .nil => none
  | .snoc before entry =>
    match searchFirstWith before project with
    | some result => some result
    | none => (project entry).map (before.length, ·)

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
  induction tr with
  | nil => simp [searchFirstWith, length]
  | snoc tr e ih =>
    constructor
    · intro h i hi
      have hb : searchFirstWith tr project = none := by
        cases hb : searchFirstWith tr project <;> simp_all [searchFirstWith]
      have he : project e = none := by
        simpa [searchFirstWith, hb] using h
      simp only [Trace.at]
      split
      · exact he
      · exact ih.mp hb _ _
    · intro h
      have hb : searchFirstWith tr project = none := ih.mpr (by
        intro i hi
        have := h i (by simp only [length]; omega)
        simpa [Trace.at, show i ≠ tr.length by omega] using this)
      have he := h tr.length (by simp [length])
      simpa [searchFirstWith, hb, Trace.at] using he

/-- First search identifies an actual match and precedes every other match. -/
theorem searchFirstWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchFirstWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → i ≤ j
:= by
  induction tr with
  | nil => simp [searchFirstWith]
  | snoc tr e ih =>
    cases hb : searchFirstWith tr project with
    | some result =>
      intro h
      have hh : result = (i, v) := by simpa [searchFirstWith, hb] using h
      subst result
      obtain ⟨hi, hv, hm⟩ := ih hb
      refine ⟨by simp only [length]; omega, ?_, ?_⟩
      · simpa [Trace.at, show i ≠ tr.length by omega] using hv
      · intro j hj hjm
        by_cases he : j = tr.length
        · omega
        · apply hm j (by simp only [length] at hj; omega)
          simpa [Trace.at, he] using hjm
    | none =>
      intro h
      cases he : project e with
      | none => simp [searchFirstWith, hb, he] at h
      | some value =>
        simp only [searchFirstWith, hb, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨by simp [length], by simpa [Trace.at] using he, ?_⟩
        intro j hj hjm
        by_cases hn : tr.length ≤ j
        · exact hn
        apply False.elim
        have hjlt : j < tr.length := by omega
        have hh := (searchFirstWith_none tr project).mp hb j hjlt
        exact hjm (by simpa [Trace.at, show j ≠ tr.length by omega] using hh)

/-- Once found, the first match is unchanged by any extension of the trace. -/
theorem searchFirstWith_later
  (a b : Trace α) (project : α → Option β) (result : Nat × β) :
  a ≤ b → searchFirstWith a project = some result → searchFirstWith b project = some result
:= by
  intro h hab
  induction h with
  | equal => exact hab
  | extend b e _ ih => simp [searchFirstWith, ih]

/-- Find the newest entry accepted by a partial projection, retaining its timestamp. -/
@[expose]
def searchLastWith
  (tr : Trace α) (project : α → Option β) :
  Option (Nat × β)
:=
  match tr with
  | .nil => none
  | .snoc before entry =>
    match project entry with
    | some value => some (before.length, value)
    | none => searchLastWith before project

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
  induction tr with
  | nil => simp [searchLastWith, length]
  | snoc tr e ih =>
    simp only [searchLastWith]
    cases he : project e with
    | none =>
      simp only [ih]
      constructor
      · intro h i hi
        simp only [Trace.at]
        split
        · exact he
        · apply h
      · intro h i hi
        have := h i (by simp only [length]; omega)
        simpa [Trace.at, show i ≠ tr.length by omega] using this
    | some v =>
      simp only [Option.some_ne_none, false_iff]
      intro h
      have := h tr.length (by simp [length])
      simp [Trace.at, he] at this

/-- A successful search identifies an actual match and bounds every other match. -/
theorem searchLastWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchLastWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → j ≤ i
:= by
  induction tr with
  | nil => simp [searchLastWith]
  | snoc tr e ih =>
    simp only [searchLastWith]
    cases he : project e with
    | some value =>
      intro h
      cases h
      refine ⟨by simp [length], ?_, ?_⟩
      · simpa [Trace.at] using he
      · intro j hj _; simp only [length] at hj; omega
    | none =>
      intro h
      obtain ⟨hi, hv, hm⟩ := ih h
      refine ⟨by simp only [length]; omega, ?_, ?_⟩
      · simpa [Trace.at, show i ≠ tr.length by omega] using hv
      · intro j hj hmatch
        by_cases hj' : j = tr.length
        · simp [Trace.at, hj', he] at hmatch
        · have hjlt : j < tr.length := by simp only [length] at hj; omega
          apply hm j hjlt
          simpa [Trace.at, hj'] using hmatch

/-- The last value on a concatenation comes from the suffix when it has a match. -/
theorem lastValue_concat
  (a b : Trace α) (project : α → Option β) :
  lastValue (concat a b) project = (lastValue b project).or (lastValue a project)
:= by
  induction b with
  | nil => simp [concat, lastValue, searchLastWith]
  | snoc b e ih =>
    cases he : project e <;> simp_all [concat, lastValue, searchLastWith]

/-- The last value on an extension changes only if its suffix contains a match. -/
theorem lastValue_subtract
  (a b : Trace α) (project : α → Option β) (h : a ≤ b) :
  lastValue b project = (lastValue (subtract b a) project).or (lastValue a project)
:= by
  rw [← lastValue_concat, subtract_concat _ _ h]

end
end DY.Trace
