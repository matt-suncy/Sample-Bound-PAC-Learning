import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

open Nat

/-- Combinatorial combinatorial bound for the symmetrization argument.
Shows that the probability of placing `l` errors entirely into the second half of a sequence
of size `2m` is bounded above by `1/2^l`. -/
axiom hypergeometric_bound_ax (m l : ℕ) (hl : l ≤ m) :
    (choose m l : ℝ) / (choose (2 * m) l : ℝ) ≤ (1 / 2) ^ l

lemma hypergeometric_bound (m l : ℕ) (hl : l ≤ m) :
    (choose m l : ℝ) / (choose (2 * m) l : ℝ) ≤ (1 / 2) ^ l :=
  hypergeometric_bound_ax m l hl
