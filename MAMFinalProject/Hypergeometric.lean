import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic

/-!
# Hypergeometric Symmetrization Bound

The key combinatorial inequality used in the VC symmetrization argument:
for l ≤ m, C(m,l)/C(2m,l) ≤ (1/2)^l.

This bounds the probability that a random split of 2m items places all l
error items in the second half.
-/

/-- Core ℕ inequality: 2^l · C(m,l) ≤ C(2m,l) for l ≤ m.
Proved by induction using Pascal's recurrence C(n,k+1)·(k+1) = C(n,k)·(n-k). -/
private lemma hypergeometric_bound_nat : ∀ (m l : ℕ), l ≤ m →
    2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l := by
  intro m l hl
  induction l with
  | zero => simp
  | succ l ih =>
    have hl' : l ≤ m := Nat.le_of_succ_le hl
    have ih' : 2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l := ih hl'
    rw [pow_succ]
    -- Suffices to prove A * (l+1) ≤ B * (l+1), then cancel l+1 > 0.
    suffices h : 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1) ≤
                 Nat.choose (2 * m) (l + 1) * (l + 1) from
      Nat.le_of_mul_le_mul_right h (Nat.succ_pos l)
    -- Apply Pascal's recurrences: C(n, k+1)·(k+1) = C(n,k)·(n-k)
    have hm := Nat.choose_succ_right_eq m l      -- C(m,l+1)·(l+1) = C(m,l)·(m-l)
    have h2m := Nat.choose_succ_right_eq (2 * m) l  -- C(2m,l+1)·(l+1) = C(2m,l)·(2m-l)
    calc 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1)
        = 2 ^ l * 2 * (Nat.choose m (l + 1) * (l + 1)) := by ring
      _ = 2 ^ l * 2 * (Nat.choose m l * (m - l)) := by rw [hm]
      _ = 2 ^ l * Nat.choose m l * (2 * (m - l)) := by ring
      _ ≤ Nat.choose (2 * m) l * (2 * (m - l)) := by gcongr
      _ ≤ Nat.choose (2 * m) l * (2 * m - l) := by gcongr; omega
      _ = Nat.choose (2 * m) (l + 1) * (l + 1) := by rw [← h2m]

/-- **Hypergeometric bound**: C(m,l) / C(2m,l) ≤ (1/2)^l, for l ≤ m.

The probability that a random l-element subset of [2m] falls entirely in the
second half is at most (1/2)^l. -/
lemma hypergeometric_bound (m l : ℕ) (hl : l ≤ m) :
    (Nat.choose m l : ℝ) / (Nat.choose (2 * m) l : ℝ) ≤ (1 / 2) ^ l := by
  -- Cast the ℕ bound 2^l * C(m,l) ≤ C(2m,l) to ℝ
  have hR : (2 : ℝ) ^ l * (Nat.choose m l : ℝ) ≤ (Nat.choose (2 * m) l : ℝ) := by
    exact_mod_cast hypergeometric_bound_nat m l hl
  -- Positivity
  have h2m_pos : (0 : ℝ) < (Nat.choose (2 * m) l : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  -- Apply div_le_of_le_mul₀: suffices to show C(m,l) ≤ (1/2)^l · C(2m,l)
  apply div_le_of_le_mul₀ h2m_pos.le (by positivity)
  -- Key: (1/2)^l · 2^l = 1, so C(m,l) = 1 · C(m,l) = (1/2)^l · 2^l · C(m,l) ≤ (1/2)^l · C(2m,l)
  have h12 : (1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l = 1 := by rw [← mul_pow]; norm_num
  calc (Nat.choose m l : ℝ)
      = 1 * (Nat.choose m l : ℝ) := (one_mul _).symm
    _ = ((1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l) * (Nat.choose m l : ℝ) := by rw [h12]
    _ = (1 / 2 : ℝ) ^ l * ((2 : ℝ) ^ l * (Nat.choose m l : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ l * (Nat.choose (2 * m) l : ℝ) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
