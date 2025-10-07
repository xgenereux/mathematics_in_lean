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
  --ext
  rfl

#check fun B ↦ image f B
#check fun B ↦ f '' B
#check {y | ∃ x, x ∈ s ∧ f x = y}

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

-- Note that we could have used:
#check fun x s f (xs : x ∈ s) ↦ mem_image_of_mem f xs

attribute [-simp] image_subset_iff
/- What do these unfold to? Which one is the most convenient? -/
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry


/- Another example. -/
example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

end

section

open Set Real

/- More concrete example. -/
example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

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

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

end
