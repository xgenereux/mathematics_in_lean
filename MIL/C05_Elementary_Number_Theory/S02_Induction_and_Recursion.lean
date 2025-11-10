import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/-
# Induction and Recursion

We look at different ways to execute proof by induction or recursion.

-/

#check Nat

/-
Recall that for inductive types:

  - No junk: The type contains no values beyond those
    expressible using the constructors.
  - No confusion: Values built using a different
    combination of constructors are different.

-/


/- Properties of inductive types -/
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

/- Example : The factorial of an integer -/
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 5

example : fac 0 = 1 :=
  rfl

example : fac 1 = 1 := by
  rw [fac]; rfl

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

/-
The `omega` tactic, for resolving integer and natural linear arithmetic problems.
Note: You can also try out `grind`.
-/
example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => rw [fac]; norm_num
  | succ n ih =>
    rw [fac]
    -- omega -- Doesn't work; not linear
    exact mul_pos n.succ_pos ih -- norm_num [ih], positivity

/- An example with recursion (See HGLV 4.8) -/
theorem fac_pos (n : ℕ) : 0 < fac n := by
  match n with
  | 0 => rw [fac]; norm_num
  | k + 1 => rw [fac]; exact mul_pos (by omega) (fac_pos k)

/- Same thing with cases' instead of match. -/
theorem fac_pos' (n : ℕ) : 0 < fac n := by
  -- generalize h : n = N
  -- rcases N with _ | k
  cases n with
  | zero => rw [fac]; norm_num
  | succ k => rw [fac]; exact mul_pos (by omega) (fac_pos' k)

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) :
    i ∣ fac n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rw [fac]
    rcases Nat.of_le_succ ile with h | rfl
    · apply dvd_mul_of_dvd_right (ih h)
    apply dvd_mul_right

/- Let's use `Nat.le_induction`. -/
#check Nat.le_induction
example {n : ℕ} (hle : 7 ≤ n) : 3 ^ n ≤ fac n := by
  induction n, hle using Nat.le_induction with
  | base => norm_num [fac]
  | succ n hle hn =>
    rw [fac, pow_succ, mul_comm]
    apply Nat.mul_le_mul (by omega) hn

theorem pow_two_le_fac (n : Nat) : 2 ^ (n - 1) ≤ fac n := by
  sorry
  /-
    match n with
    | 0 => simp [fac]
    | 1 => simp [fac]
    | n + 2 =>
      obtain ih := pow_two_le_fac (n + 1)
      simp_all [fac]
      rw [Nat.pow_add_one']
      apply mul_le_mul _ ih <;> norm_num
  -/

lemma pow_three_le_fac (n : ℕ) (hle : 7 ≤ n) : 3 ^ n ≤ fac n := by
  match n with
  | 7 => decide
  | k + 8 =>
      obtain ih := pow_three_le_fac (k + 7) (by norm_num)
      rw [fac, pow_succ, mul_comm]
      apply Nat.mul_le_mul (by omega) ih

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset
#print Finset
#print Multiset
/-
`Finset α` is the type of finite sets of elements of α.
It is implemented as a multiset (a **list** up to permutation)
which has no duplicate elements.

Let's type #check Finset.ind...
-/
#check Finset.induction


#check Finset.sum s f

open BigOperators
open Finset

example : s.sum f = ∑ x ∈ s, f x :=
  rfl

example : (range n).sum f = ∑ x ∈ range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
  Finset.sum_range_succ f n

theorem sum_id (n : ℕ) :
    ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add 2, ← ih]
    ring

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry -- same idea

end

/- Elimate objects using some sort of induction.
We will use `Finset.sum_induction` -/
#check Finset.sum_induction
example (n : ℕ) {s : Finset ℕ} (base : ∀ a ∈ s, n ∣ a) :
    n ∣ (∑ a ∈ s, a) := by
  apply Finset.sum_induction
  · apply dvd_add
  · norm_num
  · assumption

/-
In general, given some object,
we can use an "induction" to eliminate it.
In the homework, you will be tasked to find
such induction principle.

-/

/-
We can create an example using our own definition of `Nat`.
-/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

/- All the proofs are by induction. -/
theorem zero_add (n : MyNat) : add zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- Why are these rewrites important?
    rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [add, ih]
    rfl

example (m n : MyNat) : add m n = add n m := by
  induction n with
  | zero => rw [zero_add]; rfl
  | succ n ih => rw [add, succ_add, ih]

/- Using recursion, the induction hypothesis is replaced by the name of the lemma. -/
theorem add_comm (m n : MyNat) : add m n = add n m := by
  match m with
    | zero => simp_rw [zero_add, add]
    | succ m => simp_rw [succ_add, add, add_comm]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  sorry
  /-
    induction k with
    | zero => rfl
    | succ k ih => rw [add, ih]; rfl
  -/

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  sorry
  /-
    induction k with
    | zero => rfl
    | succ k ih => rw [add, mul, mul, ih, add_assoc]
  -/

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  sorry
  /-
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [mul, ih]
      rfl
  -/

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  sorry
  /-
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [mul, mul, ih, add_assoc, add_assoc, add_comm k, succ_add]
      rfl
  -/

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  sorry
  /-
    induction n with
    | zero => rw [zero_mul]; rfl
    | succ k ih => rw [mul, ih, succ_mul]
  -/


end MyNat
