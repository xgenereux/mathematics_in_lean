import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sort

section
-- Note the `DecidableEq`. We usually have this for the data you expect to be able to compute.
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end

open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

-- Note the definition may not be what you think.
-- Why would Mathlib do this?
#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

#eval ({1} : Finset ℕ) ∪ {2}

-- The proof uses lemmas.
example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp only [mem_inter, mem_union]; tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by rw [inter_union_distrib_left]

#check ({0, 2, 5} : Finset Nat)

def example1 : Finset ℕ := {0, 1, 2}

example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide

example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp [or_comm, or_left_comm]

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp; tauto

-- To add / remove elements

example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h

-- In fact...

set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)

-- Set builder notation for `Finset`.
-- We need to specify some `Finset`, say `s` to write `{_ ∈ s | _}`. Why?
#check {m ∈ range n | Even m}

-- It is defined as a filter
example : {m ∈ range n | Even m} = (range n).filter Even := rfl
example : {m ∈ range n | Even m ∧ m ≠ 3} = (range n).filter (fun m ↦ Even m ∧ m ≠ 3) := rfl

example : {m ∈ range 10 | Even m} = {0, 2, 4, 6, 8} := by decide

#check (range 5).image (fun x ↦ x * 2)
#eval (range 5).image (fun x ↦ x * 2)
#eval {x ∈ range 10 | Even x}

example : (range 5).image (fun x ↦ x * 2) = {x ∈ range 10 | Even x} := by decide

section
-- More operations on `Finset` that output `Finset`
variable (s t : Finset Nat)
#check s ×ˢ t
#check s.powerset

end

namespace finsets_and_fintypes
/-
`fold op b f s` folds the **commutative associative** operation
`op` over the `f`-image of `s`:
`fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`.
-/
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

-- Math notation
#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g

end finsets_and_fintypes

#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (hn0 : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s h ih =>
    rw [prod_insert h]
    apply mul_ne_zero
    · apply hn0; apply mem_insert_self
    apply ih
    intros x xs
    exact hn0 x (mem_insert_of_mem xs)

-- `Finset.Nonempty s` is defined to be `∃ x, x ∈ s`
noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s := Classical.choose_spec h

-- We can get a representative `List`,
noncomputable example (s : Finset ℕ) : List ℕ := s.toList
-- This also uses `Classical.choose`.

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList

#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial /- new tactic -/⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial

#check Finset.card

#eval (range 5).card

example (s : Finset ℕ) : s.card = #s := by rfl

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by simp
