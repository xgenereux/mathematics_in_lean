import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

/- `left` and `right` reminder -/
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

/- terms -/
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

#check le_or_gt 0 y
/- Notation for patterns `_ | _ `-/
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

/- cases + case -/
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

/- cases + next -/
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

/- match -/
example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

/- Usual definitions of absolute value -/
#check le_or_gt 0 x
#check abs_eq_max_neg

/- let's try to use le_or_gt -/

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry
  /- Sol:
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · linarith [abs_of_neg h]
  -/

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry
  /-
    rcases le_or_gt 0 x with h | h
    · linarith [abs_of_nonneg h]
    · linarith [abs_of_neg h]
  -/


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
  /-
    rcases le_or_gt 0 (x + y) with h | h
    · rw [abs_of_nonneg h]
      apply add_le_add (le_abs_self _) (le_abs_self _)
    rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]
  -/

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry
  /-
    constructor
    · intro h
      rcases le_or_gt 0 y with h' | h'
      · rw [abs_of_nonneg h'] at h
        left
        exact h
      rw [abs_of_neg h'] at h
      right
      exact h
    rintro (h | h)
    · apply lt_of_lt_of_le h (le_abs_self y)
    linarith [neg_le_abs_self y]
  -/

end MyAbs

end

/- two disjunction -/
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

/- Another example of the use of `rfl` -/
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

/- Let's skip this and go directly to general case -/
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
/- Look at what it means to be a `Domain`. -/
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

/- Let's use the fact that there are no zero divisors -/
/- x * y = 0 → x = 0 ∨ y = 0 -/
#check mul_eq_zero
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry
  /-
    have : x ^ 2 - 1 = 0 := by rw [h]; ring
    have : (x + 1) * (x - 1) = 0 := by rw [← this]; ring
    rw [mul_eq_zero] at this
    rw [or_comm, ← sub_eq_zero, ← sub_eq_zero (a := x)]
    simp [this]
  -/


end

/- The 3 following show how to use by_cases -/
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry

/- Look at cheatsheet-/
