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

/-- Pure ℕ arithmetic: 2 * (m - l) ≤ 2 * m - l when l ≤ m. -/
private lemma two_mul_sub_le (m l : ℕ) (hl : l ≤ m) : 2 * (m - l) ≤ 2 * m - l := by omega

/-- Inductive step: if 2^l · C(m,l) ≤ C(2m,l) then 2^(l+1) · C(m,l+1) ≤ C(2m,l+1). -/
private lemma hypergeometric_bound_nat_succ (m l : ℕ) (hl : l ≤ m)
    (ih : 2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l) :
    2 ^ (l + 1) * Nat.choose m (l + 1) ≤ Nat.choose (2 * m) (l + 1) := by
  rw [pow_succ]
  suffices h : 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1) ≤
               Nat.choose (2 * m) (l + 1) * (l + 1) from
    Nat.le_of_mul_le_mul_right h (Nat.succ_pos l)
  have hm := Nat.choose_succ_right_eq m l
  have h2m := Nat.choose_succ_right_eq (2 * m) l
  calc 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1)
      = 2 ^ l * 2 * (Nat.choose m (l + 1) * (l + 1)) := by ring
    _ = 2 ^ l * 2 * (Nat.choose m l * (m - l)) := by rw [hm]
    _ = 2 ^ l * Nat.choose m l * (2 * (m - l)) := by ring
    _ ≤ Nat.choose (2 * m) l * (2 * (m - l)) := by gcongr
    _ ≤ Nat.choose (2 * m) l * (2 * m - l) := by gcongr; exact two_mul_sub_le m l hl
    _ = Nat.choose (2 * m) (l + 1) * (l + 1) := by rw [← h2m]

/-- Core ℕ inequality: 2^l · C(m,l) ≤ C(2m,l) for l ≤ m. -/
private lemma hypergeometric_bound_nat : ∀ (m l : ℕ), l ≤ m →
    2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l := by
  intro m l hl
  induction l with
  | zero => simp
  | succ l ih =>
    exact hypergeometric_bound_nat_succ m l (Nat.le_of_succ_le hl) (ih (Nat.le_of_succ_le hl))

/-- Cast the core ℕ inequality to ℝ: 2^l · C(m,l) ≤ C(2m,l). -/
private lemma hypergeometric_bound_cast (m l : ℕ) (hl : l ≤ m) :
    (2 : ℝ) ^ l * (Nat.choose m l : ℝ) ≤ (Nat.choose (2 * m) l : ℝ) :=
  by exact_mod_cast hypergeometric_bound_nat m l hl

/-- The binomial coefficient C(2m, l) is positive in ℝ when l ≤ m. -/
private lemma choose_2m_pos (m l : ℕ) (hl : l ≤ m) :
    (0 : ℝ) < (Nat.choose (2 * m) l : ℝ) :=
  Nat.cast_pos.mpr (Nat.choose_pos (by omega))

/-- The algebraic identity (1/2)^l · 2^l = 1 in ℝ. -/
private lemma half_pow_mul_two_pow (l : ℕ) :
    (1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l = 1 := by
  rw [← mul_pow]; norm_num

/-- **Hypergeometric bound**: C(m,l) / C(2m,l) ≤ (1/2)^l, for l ≤ m.

The probability that a random l-element subset of [2m] falls entirely in the
second half is at most (1/2)^l. -/
lemma hypergeometric_bound (m l : ℕ) (hl : l ≤ m) :
    (Nat.choose m l : ℝ) / (Nat.choose (2 * m) l : ℝ) ≤ (1 / 2) ^ l := by
  apply div_le_of_le_mul₀ (choose_2m_pos m l hl).le (by positivity)
  calc (Nat.choose m l : ℝ)
      = (1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l * (Nat.choose m l : ℝ) := by
          rw [half_pow_mul_two_pow]; ring
    _ = (1 / 2 : ℝ) ^ l * ((2 : ℝ) ^ l * (Nat.choose m l : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ l * (Nat.choose (2 * m) l : ℝ) :=
        mul_le_mul_of_nonneg_left (hypergeometric_bound_cast m l hl) (by positivity)
