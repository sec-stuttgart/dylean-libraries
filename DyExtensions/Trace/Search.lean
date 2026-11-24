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
  tr.fold none (fun result time entry => result.or ((project entry).map (time, ·)))

/-- The first search on an empty trace has no match. -/
@[simp] theorem searchFirstWith_empty (project : α → Option β) : searchFirstWith .empty project = none := by simp [searchFirstWith]

/-- A first search keeps an earlier match before considering the appended entry. -/
@[simp]
theorem searchFirstWith_push
  (tr : Trace α) (e : α) (project : α → Option β) :
  searchFirstWith (tr.push e) project =
    match searchFirstWith tr project with
    | some result => some result
    | none => (project e).map (tr.length, ·)
:= by
  unfold searchFirstWith
  rw [fold_push]
  cases tr.fold none (fun result time entry => result.or ((project entry).map (time, ·))) <;> rfl

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
  induction tr using snocInduction with
  | empty => rw [searchFirstWith_empty]; simp [length, Trace.empty]
  | snoc tr e ih =>
    constructor
    · intro h i hi
      have hb : searchFirstWith tr project = none := by
        cases hb : searchFirstWith tr project <;> simp_all [searchFirstWith_push]
      have he : project e = none := by
        simpa [searchFirstWith_push, searchFirstWith_empty, hb] using h
      simp only [at_push]
      split
      · exact he
      · exact ih.mp hb _ _
    · intro h
      have hb : searchFirstWith tr project = none := ih.mpr (by
        intro i hi
        have := h i (by simp only [push_length]; omega)
        simpa [at_push, show i ≠ tr.length by omega] using this)
      have he := h tr.length (by simp [push_length])
      simpa [searchFirstWith_push, searchFirstWith_empty, hb, at_push] using he

/-- First search identifies an actual match and precedes every other match. -/
theorem searchFirstWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchFirstWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → i ≤ j
:= by
  induction tr using snocInduction with
  | empty => simp
  | snoc tr e ih =>
    cases hb : searchFirstWith tr project with
    | some result =>
      intro h
      have hh : result = (i, v) := by simpa [searchFirstWith_push, searchFirstWith_empty, hb] using h
      subst result
      obtain ⟨hi, hv, hm⟩ := ih hb
      refine ⟨by simp only [push_length]; omega, ?_, ?_⟩
      · simpa [at_push, show i ≠ tr.length by omega] using hv
      · intro j hj hjm
        by_cases he : j = tr.length
        · omega
        · apply hm j (by simp only [push_length] at hj; omega)
          simpa [at_push, he] using hjm
    | none =>
      intro h
      cases he : project e with
      | none => simp [searchFirstWith_push, hb, he] at h
      | some value =>
        simp only [searchFirstWith_push, hb, he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨by simp [push_length], by simpa [at_push] using he, ?_⟩
        intro j hj hjm
        by_cases hn : tr.length ≤ j
        · exact hn
        apply False.elim
        have hjlt : j < tr.length := by omega
        have hh := (searchFirstWith_none tr project).mp hb j hjlt
        exact hjm (by simpa [at_push, show j ≠ tr.length by omega] using hh)

/-- Once found, the first match is unchanged by any extension of the trace. -/
theorem searchFirstWith_later
  (a b : Trace α) (project : α → Option β) (result : Nat × β) :
  a ≤ b → searchFirstWith a project = some result → searchFirstWith b project = some result
:= by
  intro h hab
  obtain ⟨hi, hv, hm⟩ := searchFirstWith_some a project result.1 result.2 hab
  cases hb : searchFirstWith b project with
  | none =>
    have hn := (searchFirstWith_none b project).mp hb result.1 (by have := length_le a b h; omega)
    rw [← Trace.at_le a b result.1 hi h] at hn
    simp_all
  | some found =>
    obtain ⟨hj, hw, hmin⟩ := searchFirstWith_some b project found.1 found.2 hb
    have hle := hmin result.1 (by have := length_le a b h; omega) (by rw [← Trace.at_le a b result.1 hi h, hv]; simp)
    have hj' : found.1 < a.length := by omega
    have he := Trace.at_le a b found.1 hj' h
    have hge := hm found.1 hj' (by rw [he, hw]; simp)
    have ht : found.1 = result.1 := by omega
    have hv' : found.2 = result.2 := by
      have he' := Trace.at_le a b result.1 hi h
      have hw' : project (b.at result.1 (by omega)) = some found.2 := by simpa only [ht] using hw
      rw [← he', hv] at hw'
      exact Option.some.inj hw'.symm
    have : found = result := Prod.ext ht hv'
    simp [this]

/-- Find the newest entry accepted by a partial projection, retaining its timestamp. -/
@[expose]
def searchLastWith
  (tr : Trace α) (project : α → Option β) :
  Option (Nat × β)
:=
  tr.fold none (fun result time entry => ((project entry).map (time, ·)).or result)

/-- The last search on an empty trace has no match. -/
@[simp] theorem searchLastWith_empty (project : α → Option β) : searchLastWith .empty project = none := by simp [searchLastWith]

/-- A last search prefers the appended entry when it matches. -/
@[simp]
theorem searchLastWith_push
  (tr : Trace α) (e : α) (project : α → Option β) :
  searchLastWith (tr.push e) project =
    match project e with
    | some value => some (tr.length, value)
    | none => searchLastWith tr project
:= by
  unfold searchLastWith
  rw [fold_push]
  cases project e <;> rfl

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
  induction tr using snocInduction with
  | empty => rw [searchLastWith_empty]; simp [length, Trace.empty]
  | snoc tr e ih =>
    simp only [searchLastWith_push]
    cases he : project e with
    | none =>
      simp only [ih]
      constructor
      · intro h i hi
        simp only [at_push]
        split
        · exact he
        · apply h
      · intro h i hi
        have := h i (by simp only [push_length]; omega)
        simpa [at_push, show i ≠ tr.length by omega] using this
    | some v =>
      simp only [Option.some_ne_none, false_iff]
      intro h
      have := h tr.length (by simp [push_length])
      simp [at_push, he] at this

/-- A successful search identifies an actual match and bounds every other match. -/
theorem searchLastWith_some
  (tr : Trace α) (project : α → Option β) (i : Nat) (v : β) :
  searchLastWith tr project = some (i, v) →
    ∃ hi : i < tr.length, project (tr.at i hi) = some v ∧
      ∀ j hj, project (tr.at j hj) ≠ none → j ≤ i
:= by
  induction tr using snocInduction with
  | empty => simp
  | snoc tr e ih =>
    simp only [searchLastWith_push]
    cases he : project e with
    | some value =>
      intro h
      cases h
      refine ⟨by simp [push_length], ?_, ?_⟩
      · simpa [at_push] using he
      · intro j hj _; simp only [push_length] at hj; omega
    | none =>
      intro h
      obtain ⟨hi, hv, hm⟩ := ih h
      refine ⟨by simp only [push_length]; omega, ?_, ?_⟩
      · simpa [at_push, show i ≠ tr.length by omega] using hv
      · intro j hj hmatch
        by_cases hj' : j = tr.length
        · simp [at_push, hj', he] at hmatch
        · have hjlt : j < tr.length := by simp only [push_length] at hj; omega
          apply hm j hjlt
          simpa [at_push, hj'] using hmatch

/-- The last value on a concatenation comes from the suffix when it has a match. -/
theorem lastValue_concat
  (a b : Trace α) (project : α → Option β) :
  lastValue (concat a b) project = (lastValue b project).or (lastValue a project)
:= by
  induction b using snocInduction with
  | empty => simp [lastValue]
  | snoc b e ih =>
    cases he : project e <;> simp_all [lastValue]

/-- The last value on an extension changes only if its suffix contains a match. -/
theorem lastValue_subtract
  (a b : Trace α) (project : α → Option β) (h : a ≤ b) :
  lastValue b project = (lastValue (subtract b a) project).or (lastValue a project)
:= by
  rw [← lastValue_concat, subtract_concat _ _ h]

end
end DY.Trace
