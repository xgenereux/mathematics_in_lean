import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

#check fun B ↦ preimage f B
#check fun B ↦ f ⁻¹' B
#check fun B ↦ {x : α | f x ∈ B}

example (x : α) :  x ∈ f ⁻¹' u ↔ f x ∈ u :=
  Iff.rfl
  -- by rfl
  -- by simp only [mem_preimage]

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  rfl

#check fun B ↦ image f B
#check fun B ↦ f '' B
#check {y | ∃ x, x ∈ s ∧ f x = y}
--  y ∈ f '' s decomposes to a triple ⟨x, xs, xeq⟩

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

/- Notice that use close the goal since it tries `rfl`. -/
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

-- We could have used:
#check fun x s f (xs : x ∈ s) ↦ mem_image_of_mem f xs
-- But since we know how the image is defined, we can provide the proof directly.

attribute [-simp] image_subset_iff
/- What do each side of this equivalence unfold to?
Which one is the most convenient? -/
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro hf
    intro x hx
    simp
    apply hf
    exact ⟨x , hx, rfl⟩
  · intro hf x hx
    simp at hx
    sorry
  /-
    constructor
    · intro hf
      intro x hx
      apply hf
      exact ⟨x, hx, rfl⟩
    · intro hf x hx
      --obtain : ∀ x ∈ s, f x ∈ v := hf
      obtain ⟨y, hy, rfl⟩ := hx
      apply hf hy
  -/



/- Another example. -/
example : f '' (f ⁻¹' u) ⊆ u := by
  sorry
  /-
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    --simp at hy
    exact hy
  -/

end

section

open Set Real

/- More concrete example. -/
example : sqrt '' { x | 0 ≤ x } = { y | 0 ≤ y } := by
  sorry
  /-
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp
    · intro hnn
      use x ^ 2, sq_nonneg x
      -- exact? apply?
      exact sqrt_sq hnn
  -/


end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h
#check Classical.choose_spec h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  rw [LeftInverse]
  constructor
  · intro hinj x
    rw [inverse]
    have : ∃ y , f y = f x := ⟨x , rfl⟩
    rw [dif_pos this]
    apply hinj
    rw [choose_spec this]
  · intro heq a₁ a₂ ha
    obtain ha₁ := heq a₁
    obtain ha₂ := heq a₂
    rw [ha] at ha₁
    rw [← ha₂, ← ha₁]

  /-
    constructor
    · intro hinj
      --unfold LeftInverse
      intro x
      have hex : ∃ y, f y = f x := by use x
      rw [inverse, dif_pos hex]
      apply hinj
      exact choose_spec hex
    · intro hinv
      simp [LeftInverse] at hinv
      intro x y hxy
      rw [← hinv x, ← hinv y, hxy]
  -/

example : Surjective f ↔ RightInverse (inverse f) f := by
  rw [RightInverse, LeftInverse]
  constructor
  · intro h y
    apply inverse_spec
    apply h
  · intro h y
    use inverse f y
    apply h

  /-
    constructor
    · intro hsur
      unfold RightInverse LeftInverse
      unfold Surjective at hsur
      intro x
      exact inverse_spec x (hsur _)
    · intro hinv
      unfold RightInverse LeftInverse at hinv
      unfold Surjective
      intro y
      use inverse f y
      simp [hinv]
  -/


end

section
variable {α : Type*}
open Function

/-
No surjective function from a set to its power set. (Type-theoretic statement)
-/
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ f j := by sorry
    /-
      rw [h]; simp [S, h₁]
    -/
  contradiction

end
