module

public import DyExtensions.Trace.Basic
import all DY.Trace.Basic

namespace DY.Trace

public section

/-- Concatenate traces in chronological order. -/
@[expose]
def concat (left right : Trace α) : Trace α := ⟨left.toArray ++ right.toArray⟩

/-- Remove the first `n` entries, retaining chronological order. -/
@[expose]
def drop (tr : Trace α) (n : Nat) : Trace α := ⟨tr.toArray.extract n⟩

/-- The suffix after a prefix; reconstruction requires `before ≤ tr`. -/
@[expose]
def subtract (tr before : Trace α) : Trace α := tr.drop before.length

/-- Appending an empty trace leaves the trace unchanged. -/
@[simp]
theorem concat_nil (tr : Trace α) : concat tr .empty = tr := by cases tr; simp [concat, Trace.empty]

/-- Prepending an empty trace leaves the trace unchanged. -/
@[simp]
theorem nil_concat (tr : Trace α) : concat .empty tr = tr := by cases tr; simp [concat, Trace.empty]

/-- Concatenation is associative. -/
theorem concat_assoc (a b c : Trace α) : concat (concat a b) c = concat a (concat b c) := by simp [concat, Array.append_assoc]

/-- Concatenation adds trace lengths. -/
@[simp]
theorem concat_length (a b : Trace α) : (concat a b).length = a.length + b.length := by simp [concat, length]

/-- Concatenating an appended suffix appends its final entry. -/
@[simp]
theorem concat_push (a b : Trace α) (e : α) : concat a (b.push e) = (concat a b).push e := by
  simp only [concat, push, Array.append_push]

/-- Concatenation extends its left argument. -/
theorem concat_le (a b : Trace α) : a ≤ concat a b := by
  dsimp only [LE.le, concat]
  grind

/-- Dropping every entry gives the empty trace. -/
@[simp]
theorem drop_length (tr : Trace α) : tr.drop tr.length = .empty := by simp [drop, length, Trace.empty]

/-- A trace has no suffix after itself. -/
@[simp]
theorem subtract_self (tr : Trace α) : subtract tr tr = .empty := drop_length tr

/-- Removing a prefix commutes with appending a later entry. -/
theorem subtract_snoc
  (a b : Trace α) (e : α) (h : a ≤ b) :
  subtract (b.push e) a = (subtract b a).push e
:= by
  have hl := length_le a b h
  change a.toArray.size ≤ b.toArray.size at hl
  simp [subtract, drop, push, length, Array.extract_push, hl, Nat.not_succ_le_self]

/-- A trace is its prefix followed by the remaining suffix. -/
theorem subtract_concat
  (a b : Trace α) (h : a ≤ b) :
  concat a (subtract b a) = b
:= by
  cases a; cases b
  dsimp only [LE.le] at h
  simp only [concat, subtract, drop, length, Trace.mk.injEq]
  grind

/-- Removing the left part of a concatenation recovers the right part. -/
theorem concat_subtract (a b : Trace α) : subtract (concat a b) a = b := by
  cases a; cases b
  simp only [concat, subtract, drop, length, Trace.mk.injEq]
  grind

/-- Successive extension suffixes concatenate to the complete extension. -/
theorem subtract_concat_slices
  (a b c : Trace α) (hab : a ≤ b) (hbc : b ≤ c) :
  subtract c a = concat (subtract b a) (subtract c b)
:= by
  have h := subtract_concat a b hab
  have h' := subtract_concat b c hbc
  calc
    subtract c a = subtract (concat (concat a (subtract b a)) (subtract c b)) a := by rw [h, h']
    _ = concat (subtract b a) (subtract c b) := by rw [concat_assoc, concat_subtract]

end
end DY.Trace
