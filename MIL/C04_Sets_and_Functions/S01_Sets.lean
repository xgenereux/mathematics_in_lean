import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
/- Opening namespace -/
open Set

/- Usual set operations -/
#check s ⊆ t
#check s ∩ t
#check {a | a ∈ s ∧ a ∈ t}
#check s ∪ t
#check fun a ↦ a ∈ s
#check fun a ↦ a ∉ s
#check fun a ↦ ¬ a ∈ s
#check (∅ : Set α)
#check (univ : Set α)


example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  specialize h x xs
  exact ⟨h, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

/-
Definitional reduction example :
  to make sense of the intro command and the anonymous
  constructors Lean is forced to expand the definitions."
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  rw [mem_inter_iff]
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

lemma t1 : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  obtain xs := hx.1
  obtain xtu := hx.2
  /- definitional reduction on `∪` using `rcases`-/
  -- rw [union_def, mem_setOf] at xtu
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

/- Nice example using anonymous constructor-/
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

/- Let's try it out. -/
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

#check Set.diff_eq
#check Set.mem_diff

/- Another comparison with definitional reduction. -/
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def]
  intro x xstu
  rw [Set.diff_eq, Set.diff_eq, Set.inter_def, Set.inter_def] at xstu
  simp only [mem_setOf] at xstu
  have xs : x ∈ s := xstu.left.left
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  rw [Set.diff_eq, inter_def, mem_setOf]
  constructor
  · exact xs
  rw [Set.compl_def, mem_setOf]
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  refine ⟨xs, ?_⟩
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry

/- Set `ext`. -/
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

/- Another way to prove equality : `Subset.antisymm`. -/
#check Subset.antisymm

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

/- Same thing in term mode -/
example : s ∩ t = t ∩ s :=
    Subset.antisymm
      (fun x ⟨xs, xt⟩  ↦ ⟨xt, xs⟩)
      (fun x ⟨xt, xs⟩  ↦ ⟨xs, xt⟩)

/- **Start here** -/

/-
**Some details about Sets**
In the library, `Set α` is defined to be `α → Prop` and `x ∈ s`
is defined to be `s x`.
In other words, sets are really properties, treated as objects.

The library also defines set-builder notation :
The expression `{ y | P y }` unfolds to `(fun y ↦ P y)`,
so `x ∈ { y | P y }` reduces to `P x`.
-/
#check eq_mem_setOf

/- 
For example,
We can turn the property of being even into the set of even numbers:
-/
def evens : Set ℕ :=
  { n | Even n }

def evens' : Set ℕ := Even

example : evens = evens' := rfl

/- { y | P y } --> (fun y ↦ P y) --> P -/

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [- Nat.not_even_iff_odd]
  apply Classical.em

/- Set builder notation in definitions -/
example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : ∅ = {x : α | False} := rfl
example : univ = {x : α| True} := rfl

/- Here the membership means that`fun x ↦ x ∈ s ↔ fun x ↦ False`-/
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

/- We can see it more clearly by unfolding definitions-/
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  rw [Set.empty_def] at h
  -- @ to show the explicit instanciation of the theorem.
  rw [@Set.mem_setOf_eq ℕ x (fun _ ↦ False)] at h
  assumption

example : True :=
  trivial

/- Here the membership means that `fun x ↦ x ∈ s ↔ fun x ↦ True`-/
example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

/-
Show this using `Nat.Prime.eq_two_or_odd` and `Nat.odd_iff`.
-/
#check Nat.Prime.eq_two_or_odd
example : { n | Nat.Prime n } ∩ { n | n > 2 }
    ⊆ { n | ¬Even n } := by
  intro x ⟨hp, h2⟩
  simp_all
  rw [Nat.odd_iff]
  obtain h | h := Nat.Prime.eq_two_or_odd hp <;> simp_all


/- General notion of primality-/
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end


--------------------------------------------------



section

variable (s t : Set ℕ)
/- Bounded quantifiers. Small differences but behave roughly the same
as you would expect: ∀ x ∈ s, ... = ∀ x, x ∈ s → ...  -/
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set
/- Indexed union and intersection. -/
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

#check mem_iUnion₂
#check mem_iInter₂

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

/-
Let's start by typing `eq_univ`, tab completion will tell you that
`rw [← eq_univ_of_forall]` is a good way to start the proof.
We'll also need `Nat.exists_infinite_primes`.
(We will prove this ourselves eventually.)

hint: use simp to simplify the big union.
-/
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

/- Definition of the **Union of a set of sets.** -/
#check fun {α} (S : Set (Set α)) ↦ sorry -- fill

#print Set.sUnion
#check fun {α} (S : Set (Set α)) ↦ sSup S
#check sSup
#print Set.instSupSet

/-
The supremum relates to some order.
As it turns out, the supremem of sets relates to the partial order
by inclusion.

So `sSup S` is such that `∀ s ∈ S, s ⊆ sSup S` and it's the smallest set
with such property.
-/

/- Same for intersection -/
#print Set.sInter


example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
