module

public import DY.Trace.Basic
import all DY.Trace.Basic

namespace DY.Trace

public section

/-- Concatenate traces in chronological order. -/
@[expose]
def concat
  (left right : Trace α) :
  Trace α
:=
  match right with
  | .nil => left
  | .snoc before entry => .snoc (concat left before) entry

/-- Remove the first `n` entries, retaining chronological order. -/
@[expose]
def drop
  (tr : Trace α) (n : Nat) :
  Trace α
:=
  match tr with
  | .nil => .nil
  | .snoc before entry => if n ≤ before.length then .snoc (drop before n) entry else .nil

/-- The suffix after a prefix; reconstruction requires `before ≤ tr`. -/
@[expose]
def subtract (tr before : Trace α) : Trace α := tr.drop before.length

@[simp]
theorem concat_nil (tr : Trace α) : concat tr .nil = tr := rfl

@[simp]
theorem nil_concat (tr : Trace α) : concat .nil tr = tr := by
  induction tr <;> simp_all [concat]

/-- Concatenation is associative. -/
theorem concat_assoc (a b c : Trace α) : concat (concat a b) c = concat a (concat b c) := by
  induction c <;> simp_all [concat]

@[simp]
theorem concat_length (a b : Trace α) : (concat a b).length = a.length + b.length := by
  induction b <;> simp_all [concat, length, Nat.add_assoc]

/-- Concatenation extends its left argument. -/
theorem concat_le (a b : Trace α) : a ≤ concat a b := by
  induction b with
  | nil => exact le_refl a
  | snoc b e ih => exact le.extend _ _ _ ih

@[simp]
theorem drop_length (tr : Trace α) : tr.drop tr.length = .nil := by
  cases tr <;> simp [drop, length, Nat.not_succ_le_self]

@[simp]
theorem subtract_self (tr : Trace α) : subtract tr tr = .nil := drop_length tr

/-- Removing a prefix commutes with appending a later entry. -/
theorem subtract_snoc
  (a b : Trace α) (e : α) (h : a ≤ b) :
  subtract (.snoc b e) a = .snoc (subtract b a) e
:= by
  simp [subtract, drop, length_le a b h]

/-- A trace is its prefix followed by the remaining suffix. -/
theorem subtract_concat
  (a b : Trace α) (h : a ≤ b) :
  concat a (subtract b a) = b
:= by
  induction h with
  | equal => simp
  | extend b e h ih => rw [subtract_snoc _ _ _ h]; simp [concat, ih]

/-- Removing the left part of a concatenation recovers the right part. -/
theorem concat_subtract (a b : Trace α) : subtract (concat a b) a = b := by
  induction b with
  | nil => simp
  | snoc b e ih => rw [concat, subtract_snoc _ _ _ (concat_le a b), ih]

/-- Successive extension suffixes concatenate to the complete extension. -/
theorem subtract_concat_slices
  (a b c : Trace α) (hab : a ≤ b) (hbc : b ≤ c) :
  subtract c a = concat (subtract b a) (subtract c b)
:= by
  induction hbc with
  | equal => simp
  | extend c e h ih =>
    rw [subtract_snoc _ _ _ (le_trans _ _ _ hab h), subtract_snoc _ _ _ h, ih]
    rfl

end
end DY.Trace
