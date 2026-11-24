module

public import DY.Trace.Basic
import all DY.Trace.Basic

namespace DY.Trace
public section

/-- Append an entry already in the trace's combined entry representation. -/
@[expose]
def push (tr : Trace α) (entry : α) : Trace α := ⟨tr.toArray.push entry⟩

/-- Typed append is a raw push after injecting the entry. -/
theorem append_eq_push
  [TraceEntryHas EntryT α] (tr : Trace α) (entry : EntryT) :
  tr.append entry = tr.push (TraceEntryHas.inj entry)
:= by rfl

/-- Prove a trace property by adding entries in chronological order. -/
theorem snocInduction
  {motive : Trace α → Prop} (empty : motive .empty)
  (snoc : ∀ tr entry, motive tr → motive (tr.push entry)) (tr : Trace α) :
  motive tr
:= by
  suffices ∀ n tr, tr.length = n → motive tr from this tr.length tr rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro tr hn
    by_cases h : tr.toArray.size = 0
    · have : tr = .empty := by cases tr; simp_all [Trace.empty]
      simpa [this] using empty
    · have hp : 0 < tr.toArray.size := by omega
      have he : (push ⟨tr.toArray.pop⟩ (tr.toArray.back hp)) = tr := by
        cases tr
        simp only [push, Trace.mk.injEq]
        grind
      rw [← he]
      apply snoc
      apply ih (tr.toArray.pop.size) (by simp [length] at hn; simp [Array.size_pop]; omega)
      rfl

/-- Fold over entries with their chronological timestamps. -/
@[expose]
def fold (tr : Trace α) (initial : β) (step : β → Nat → α → β) : β :=
  (tr.toArray.foldl (fun (i, acc) e => (i + 1, step acc i e)) (0, initial)).2

/-- An indexed fold increments its counter once per entry. -/
private theorem fold_index
  (tr : Trace α) (initial : β) (step : β → Nat → α → β) :
  (tr.toArray.foldl (fun (i, acc) e => (i + 1, step acc i e)) (0, initial)).1 = tr.length
:= by
  induction tr using snocInduction with
  | empty => rfl
  | snoc tr e ih => simp [push, length, ih]

/-- Folding an empty trace returns the initial accumulator. -/
@[simp] theorem fold_empty (initial : β) (step : β → Nat → α → β) : fold .empty initial step = initial := by simp [fold, Trace.empty]

/-- Folding an appended entry performs one more step at the previous length. -/
@[simp]
theorem fold_push
  (tr : Trace α) (entry : α) (initial : β) (step : β → Nat → α → β) :
  fold (tr.push entry) initial step = step (fold tr initial step) tr.length entry
:= by
  simp [fold, push, fold_index]

/-- A raw push increases the trace length by one. -/
@[simp] theorem push_length (tr : Trace α) (e : α) : (tr.push e).length = tr.length + 1 := by simp [push, length]

/-- An appended entry occupies the old length; earlier entries retain their indices. -/
theorem at_push
  (tr : Trace α) (e : α) (i : Nat) (h : i < (tr.push e).length) :
  (tr.push e).at i h = if hi : i = tr.length then e else tr.at i (by simp [push_length] at h; omega)
:= by
  by_cases hi : i = tr.length
  · subst i
    simp [Trace.at, push, length]
  · have hl : i < tr.toArray.size := by simp [push_length] at h; change i < tr.length; omega
    simp [Trace.at, push, Array.getElem_push_lt hl, hi]
    rfl

end
end DY.Trace
