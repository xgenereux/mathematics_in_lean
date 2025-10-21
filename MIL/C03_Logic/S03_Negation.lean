import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

/- Remember: `¬ A "=" A → False `-/

/- Typical use -/
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl _ this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

/- similar -/
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

/- choose the right witness-/
example : ¬FnHasUb fun x ↦ x := by
  intro hf
  unfold FnHasUb at hf
  obtain ⟨u, hu⟩ := hf
  unfold FnUb at hu
  dsimp at hu
  specialize hu (u + 1)
  simp at hu
  norm_num at hu

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
#check not_le
#check not_lt

/- `lt_iff_not_ge` or `not_le`, `not_lt`
Let's look at `absurd` and `contrapose(!)`
-/
example (h : Monotone f) (h' : f a < f b) : a < b := by
  unfold Monotone at h
  contrapose h'
  rw [not_lt] at ⊢ h'
  apply h h'
  /- Sol:
    contrapose h'
    simp only [not_lt] at *
    exact h h'
  -/

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry

/- The second the last example is not true for ≤.-/
/- local definitions -/
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by intro a b hab; exact le_refl _
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  specialize @h f monof 1 0 h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx
  specialize h (x / 2) (by simp [hx])
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

-- !
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  --show P x
  by_contra h''
  apply h'
  exact ⟨x, h''⟩

-- ¬¬Q ↔ Q

example (h : ¬¬Q) : Q := by
  push_neg at h

example (h : Q) : ¬¬Q := by
  sorry

end

-- push_neg
section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  unfold FnHasUb at h
  unfold FnUb at h
  push_neg at h
  exact h

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

-- `exflaso` and `False.elim`

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h


example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
