import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

/- Remember: `¬ A ":=" A → False `-/

/- First example. Notice the name of the hypothesis
created by have. -/
example (h : a < b) : ¬b < a := by
  -- rw [Not]
  intro h'
  have : a < a :=
    -- by linarith
    lt_trans h h'
  #check lt_irrefl a
  apply lt_irrefl a this

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
  rw [FnHasUb] at fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  rw [FnUb] at fnuba
  have : f x ≤ a := fnuba x
  linarith

/- similar -/
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro hlb
  rw [FnHasLb] at hlb
  obtain ⟨a, ha⟩ := hlb
  rw [FnLb] at ha
  have h := h a
  obtain ⟨x, hx⟩ := h
  have ha := ha x
  linarith

/- choose the right witness-/
example : ¬FnHasUb fun x ↦ x := by
  intro h
  rw [FnHasUb] at h
  obtain ⟨a, ha⟩ := h
  rw [FnUb] at ha
  have ha := ha (a + 1)
  linarith

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
  rw [Monotone] at h
  -- have h := @h b a
  contrapose h'
  rw [not_lt] at *
  apply h h'

  /- Sol:
    contrapose h'
    simp only [not_lt] at *
    exact h h'
  -/

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hM
  rw [Monotone] at hM
  have hM := hM h
  rw [← not_lt] at hM
  exact hM h'

/- The second the last example is not true for ≤. -/
/- local definitions -/
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b},
    f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b hab
    unfold f
    -- linarith
    exact le_refl _
  have h' : f 1 ≤ f 0 := le_refl _
  have h : 1 ≤ (0 : ℝ) := h monof h'
  linarith

/-
New tactic called `let`.
-/

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx
  specialize h (x / 2) (by linarith)
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x hP
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro hP
  obtain ⟨x, hx⟩ := hP
  specialize h x
  exact h hx

-- !!
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  obtain ⟨x, hx⟩ := h
  intro h
  apply hx (h x)


/-
What do we need to prove the third problem?
-/
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  -- show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra
  apply h this

example (h : Q) : ¬¬Q := by
  intro hQ
  absurd hQ h
  simp

end

-- Resume here for lecture 3

-- push Not
-- Note: Not available in Homework 1.
section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push Not at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push Not at h
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

-- `exfalso` and `False.elim`s
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
