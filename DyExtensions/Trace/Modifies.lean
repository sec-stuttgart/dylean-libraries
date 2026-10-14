module

public import DyExtensions.Trace.Search
public import DY.Trace.Monad
import all DY.Trace.Basic

namespace DY.Trace
public section

/-- Addresses written by a trace, parameterized by the entry representation. -/
@[expose]
def modifies (addressOf : α → Option δ) (tr : Trace α) (address : δ) : Prop :=
  match tr with
  | .nil => False
  | .snoc before entry => addressOf entry = some address ∨ modifies addressOf before address

/-- An address is modified exactly when a write to it occurs on the trace. -/
theorem modifies_spec
  (addressOf : α → Option δ) (tr : Trace α) (address : δ) :
  modifies addressOf tr address ↔ ∃ i h, addressOf (tr.at i h) = some address
:= by
  induction tr with
  | nil => simp [modifies, length]
  | snoc tr e ih =>
    simp only [modifies, ih]
    constructor
    · intro h
      rcases h with h | ⟨i, hi, h⟩
      · exact ⟨tr.length, by simp [length], by simpa [Trace.at] using h⟩
      · exact ⟨i, by simp only [length]; omega, by simpa [Trace.at, show i ≠ tr.length by omega] using h⟩
    · rintro ⟨i, hi, h⟩
      by_cases he : i = tr.length
      · left; simpa [Trace.at, he] using h
      · right
        have hi' : i < tr.length := by simp only [length] at hi; omega
        exact ⟨i, hi', by simpa [Trace.at, he] using h⟩

/-- Concatenation takes the union of the modified addresses. -/
theorem modifies_concat
  (addressOf : α → Option δ) (a b : Trace α) (address : δ) :
  modifies addressOf (concat a b) address ↔ modifies addressOf a address ∨ modifies addressOf b address
:= by
  induction b <;> simp_all [concat, modifies] <;> grind

/-- A suffix that does not write an address cannot change a lookup for that address. -/
theorem lastValue_of_not_modifies
  (addressOf : α → Option δ) (project : α → Option β) (address : δ)
  (compatible : ∀ e, addressOf e ≠ some address → project e = none)
  (a b : Trace α) (h : a ≤ b) (unmodified : ¬ modifies addressOf (subtract b a) address) :
  lastValue b project = lastValue a project
:= by
  rw [lastValue_subtract a b project h]
  have hn : lastValue (subtract b a) project = none := by
    unfold lastValue
    rw [(searchLastWith_none _ _).mpr]
    · rfl
    · intro i hi
      apply compatible
      intro he
      exact unmodified ((modifies_spec _ _ _).mpr ⟨i, hi, he⟩)
  simp [hn]

end
end DY.Trace

namespace DY.Traceful
public section

/-- Addresses written during a computation, including writes before failure. -/
@[expose]
def modifies
  [ExecTraceTypes] (addressOf : ExecTrace.Entry → Option δ)
  (f : Traceful α) (tr : ExecTrace) (address : δ) : Prop
:=
  Trace.modifies addressOf (Trace.subtract (f.run tr).2.val tr) address

/-- Returning a value does not modify any address. -/
theorem modifies_pure
  [ExecTraceTypes] (addressOf : ExecTrace.Entry → Option δ)
  (value : α) (tr : ExecTrace) (address : δ) :
  ¬ modifies addressOf (pure value) tr address
:= by
  simp [modifies, run_pure, Trace.modifies]

/-- Bind unions writes from both stages; failure retains the first stage's writes. -/
theorem modifies_bind
  [ExecTraceTypes] (addressOf : ExecTrace.Entry → Option δ)
  (f : Traceful α) (g : α → Traceful β) (tr : ExecTrace) (address : δ) :
  modifies addressOf (f >>= g) tr address ↔
    modifies addressOf f tr address ∨
      match (f.run tr).1 with
      | none => False
      | some value => modifies addressOf (g value) (f.run tr).2.val address
:= by
  simp only [modifies, run_bind]
  cases hf : f.run tr with
  | mk result mid =>
    cases result with
    | none => simp
    | some value =>
      simp only
      rw [Trace.subtract_concat_slices tr mid.val ((g value).run mid.val).2.val mid.property ((g value).run mid.val).2.property]
      exact Trace.modifies_concat _ _ _ _

end
end DY.Traceful
