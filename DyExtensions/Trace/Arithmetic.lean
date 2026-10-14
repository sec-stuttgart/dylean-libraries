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
  ⟨left.toArray ++ right.toArray⟩

/-- Remove the first `n` entries, retaining chronological order. -/
@[expose]
def drop
  (tr : Trace α) (n : Nat) :
  Trace α
:=
  ⟨tr.toArray.extract n tr.length⟩

/-- The suffix after a prefix; reconstruction requires `before ≤ tr`. -/
@[expose]
def subtract (tr before : Trace α) : Trace α := tr.drop before.length

/-- Induct over a trace by appending one raw array entry at a time. -/
theorem inductionOn
  {motive : Trace α → Prop} (tr : Trace α)
  (nil : motive .nil) (snoc : ∀ tr e, motive tr → motive ⟨tr.toArray.push e⟩) :
  motive tr
:= by
  rcases tr with ⟨⟨entries⟩⟩
  have h : ∀ entries : List α, motive ⟨entries.reverse.toArray⟩ := by
    intro entries
    induction entries with
    | nil => exact nil
    | cons e entries ih => simpa using snoc ⟨entries.reverse.toArray⟩ e ih
  simpa using h entries.reverse

@[simp]
theorem rawPush_length (tr : Trace α) (e : α) : (Trace.mk (tr.toArray.push e)).length = tr.length + 1 := by
  simp [length]

/-- Reading an appended raw entry preserves all earlier indices. -/
theorem at_rawPush
  (tr : Trace α) (e : α) (i : Nat) (hi : i < (Trace.mk (tr.toArray.push e)).length) :
  (Trace.mk (tr.toArray.push e)).at i hi = if h : i = tr.length then e else tr.at i (by simp only [rawPush_length] at hi; omega)
:= by
  split
  · rename_i h
    subst i
    simp [Trace.at, length]
  · rename_i h
    dsimp only [Trace.at]
    apply Array.getElem_push_lt

/-- Concatenation commutes with appending a raw entry to its right argument. -/
@[simp]
theorem concat_rawPush
  (a b : Trace α) (e : α) :
  concat a ⟨b.toArray.push e⟩ = ⟨(concat a b).toArray.push e⟩
:= by
  simp only [concat, Array.append_push]

@[simp]
theorem concat_nil (tr : Trace α) : concat tr .nil = tr := by
  cases tr; simp [concat, nil]

@[simp]
theorem nil_concat (tr : Trace α) : concat .nil tr = tr := by
  cases tr; simp [concat, nil]

/-- Concatenation is associative. -/
theorem concat_assoc (a b c : Trace α) : concat (concat a b) c = concat a (concat b c) := by
  simp [concat, Array.append_assoc]

@[simp]
theorem concat_length (a b : Trace α) : (concat a b).length = a.length + b.length := by
  simp [concat, length]

/-- Concatenation extends its left argument. -/
theorem concat_le (a b : Trace α) : a ≤ concat a b := by
  dsimp [LE.le, concat]
  grind

@[simp]
theorem drop_length (tr : Trace α) : tr.drop tr.length = .nil := by
  simp [drop, length, nil]

@[simp]
theorem subtract_self (tr : Trace α) : subtract tr tr = .nil := drop_length tr

/-- Removing a prefix commutes with appending a later entry. -/
theorem subtract_snoc
  (a b : Trace α) (e : α) (h : a ≤ b) :
  subtract ⟨b.toArray.push e⟩ a = ⟨(subtract b a).toArray.push e⟩
:= by
  have hl : a.toArray.size ≤ b.toArray.size := length_le a b h
  simp [subtract, drop, length, Array.extract_push, hl]

/-- A trace is its prefix followed by the remaining suffix. -/
theorem subtract_concat
  (a b : Trace α) (h : a ≤ b) :
  concat a (subtract b a) = b
:= by
  rcases a with ⟨aa⟩
  rcases b with ⟨bb⟩
  dsimp [LE.le] at h
  apply congrArg Trace.mk
  dsimp [concat, subtract, drop, length]
  conv => lhs; lhs; rw [h]
  rw [Array.extract_append_extract]
  have hl : aa.size ≤ bb.size := by
    have := congrArg Array.size h
    simp at this
    omega
  simp [Nat.max_eq_right hl]

/-- Removing the left part of a concatenation recovers the right part. -/
theorem concat_subtract (a b : Trace α) : subtract (concat a b) a = b := by
  cases b
  simp [subtract, concat, drop, length, Array.extract_append]

/-- Successive extension suffixes concatenate to the complete extension. -/
theorem subtract_concat_slices
  (a b c : Trace α) (hab : a ≤ b) (hbc : b ≤ c) :
  subtract c a = concat (subtract b a) (subtract c b)
:= by
  have hb := subtract_concat a b hab
  have hc := subtract_concat b c hbc
  calc
    subtract c a = subtract (concat a (concat (subtract b a) (subtract c b))) a := by rw [← concat_assoc, hb, hc]
    _ = concat (subtract b a) (subtract c b) := concat_subtract _ _

end
end DY.Trace
