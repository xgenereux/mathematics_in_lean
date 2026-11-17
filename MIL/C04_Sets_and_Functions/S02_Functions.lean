import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

/-
**Image and Preimage of functions**
**Injectivity and Surjectivity**

-/

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
--  y ∈ f '' s decomposes to a triple ⟨x, xs, xeq⟩

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      rw [image]
      simp only [mem_setOf_eq]
      use x
    · right
      use x, xt
  · rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    · use x, Or.inl xs
    · use x, Or.inr xt

/- Notice that use close the goal since it tries `rfl`. -/
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  -- simp only [preimage, image, mem_setOf]
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
  · intro h x hx
    simp only [preimage, mem_setOf]
    simp [image] at h
    rw [subset_def] at h
    simp only [mem_setOf] at h
    apply h
    use x
    -- have := h (f x)
  · intro h
    simp [image]
    simp [preimage] at h
    intro x hx
    simp only [mem_setOf] at hx
    simp only [subset_def, mem_setOf] at h
    obtain ⟨a, ha, rfl⟩ := hx
    apply h _ ha
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

-- resume here with recap

section

open Set Real

#check sqrt
/- More concrete example. -/
example : sqrt '' { x | 0 ≤ x } = { y | 0 ≤ y } := by
  simp [image]
  ext x
  constructor
  · intro h
    simp at *
    obtain ⟨a, h₁, rfl⟩ := h
    apply sqrt_nonneg
  · intro h
    simp at *
    use x ^ 2
    constructor
    · exact sq_nonneg x
    · exact sqrt_sq h
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

#check (fun (n : Nat) ↦ 7 ≤ n)

variable (P : α → Prop) (h : ∃ x, P x)

section nonexample

-- def myEl : α := by
--   obtain ⟨x, h⟩ := h
--   use x

end nonexample














#check Classical.choose h
#check Classical.choose_spec h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} {y : β} (h : ∃ x, f x = y) :
    f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro hinj
    unfold LeftInverse
    intro x
    have hex : ∃ y, f y = f x := by use x
    rw [inverse, dif_pos hex]
    apply hinj
    exact choose_spec hex
  · intro hinv
    simp [LeftInverse] at hinv
    intro x y hxy
    rw [← hinv x, ← hinv y, hxy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  unfold RightInverse LeftInverse Surjective
  constructor
  · intro h y
    specialize h y
    apply inverse_spec h
  · intro h y
    specialize h y
    use inverse f y

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
No surjective function from a set to its power set.
(Type-theoretic statement)
-/
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  obtain ⟨j, hj⟩ := surjf S
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [hj] at h'
    contradiction
  have h₂ : j ∈ f j := by
    rw [hj]
    simp [S, h₁]
    /-
      rwa [hj, Set.mem_setOf_eq]
    -/
  contradiction

end
