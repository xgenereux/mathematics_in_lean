import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

/- Definition of the convergence of a sequence. -/
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

/- The `ext` tactic -/
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

/- The `congr` tactic -/
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

/- The `convert` tactic -/
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul] -- Reconcile term
  exact lt_trans zero_lt_one h -- Reconcile hyp

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  dsimp
  rw [sub_self, abs_zero]
  apply εpos

/- Look at cheat sheet -/
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  -- hint use calc
  sorry
  /-  Sol:
      specialize ht n (le_trans (le_max_right _ _) hn)
      specialize hs n (le_trans (le_max_left _ _) hn)
      calc
        |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
        _ ≤ |s n - a| + |t n - b| := by apply abs_add
        _ < ε / 2 + ε / 2 := by exact add_lt_add hs ht
        _ = ε := by ring -/
