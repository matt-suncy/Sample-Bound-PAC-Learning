import MAMFinalProject.Definitions
import MAMFinalProject.Hypergeometric
import MAMFinalProject.GhostSample
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory ProbabilityTheory Real Set Classical

variable {X : Type*} [MeasurableSpace X]

/-!
# Union Bound Synthesis and Sample Complexity

This file combines:
1. The growth function (bounding the number of distinct hypothesis labelings)
2. The hypergeometric bound (from Hypergeometric.lean)
3. A union bound over all labelings
to obtain Pr[B] ≤ Π_C(2m) · 2^{-εm/2}.

Then by setting this ≤ δ/2, we get the required sample size condition.
-/

section GrowthFunction

/-- The growth function Π_C(m): the maximum number of distinct labelings that
concept class C can induce on any m-point sample.

For a fixed sample S, the labeling induced by h is the set of indices i where S i ∈ h.
We define the growth function as the supremum over all samples of the number of
distinct such labelings. -/
noncomputable def growthFunction (C : Set (Concept X)) (m : ℕ) : ℕ :=
  ⨆ S : Fin m → X, Nat.card (Set.range fun h : C => restrictToSample h.val S)

/-- For any fixed sample S, the number of distinct labelings is at most growthFunction. -/
lemma card_labelings_le_growthFunction
    (C : Set (Concept X)) (m : ℕ) (S : Fin m → X) :
    Nat.card (Set.range fun h : C => restrictToSample h.val S) ≤ growthFunction C m := by
  apply le_ciSup_of_le _ S le_rfl
  refine ⟨2 ^ m, ?_⟩
  rintro x ⟨T, rfl⟩
  calc Nat.card (Set.range fun h : C => restrictToSample h.val T)
      ≤ Nat.card (Set.univ : Set (Finset (Fin m))) :=
          Nat.card_mono Set.finite_univ (Set.subset_univ _)
    _ = 2 ^ m := by
        rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

/-- The growth function is bounded above by 2^m (all possible subsets of Fin m). -/
lemma growthFunction_le_two_pow (C : Set (Concept X)) (m : ℕ) :
    growthFunction C m ≤ 2 ^ m := by
  unfold growthFunction
  rcases isEmpty_or_nonempty (Fin m → X) with hE | hNE
  · haveI := hE
    rw [ciSup_of_empty]
    exact Nat.zero_le _
  · apply ciSup_le
    intro S
    calc Nat.card (Set.range fun h : C => restrictToSample h.val S)
        ≤ Nat.card (Set.univ : Set (Finset (Fin m))) :=
            Nat.card_mono Set.finite_univ (Set.subset_univ _)
      _ = 2 ^ m := by
          rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

end GrowthFunction

section UnionBound

/-!
## Union Bound Synthesis

**Theorem**: Pr[B] ≤ growthFunction(C, 2m) · 2^{-εm/2}

**Proof**:
Fix a 2m-sample S. The concept class C induces at most growthFunction(C, 2m)
distinct labelings on S. For each labeling where h is consistent with S₁
(i.e., all errors land in S₂), the hypergeometric bound shows this happens with
probability ≤ 2^{-l} where l = number of errors on S.

By the union bound over all possible labelings:
  Pr[B] ≤ ∑_{labelings} P[all errors in S₂] ≤ growthFunction(C,2m) · 2^{-εm/2}
-/

/-- **Union bound for Event B**:
The probability of Event B is bounded by the growth function times the
hypergeometric term. -/
theorem symmetrization_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (hε : ε > 0) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤
    ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) := by
  -- The proof proceeds by:
  -- 1. For each fixed 2m-sample, at most growthFunction C (2m) labelings are consistent with S₁
  -- 2. For each such labeling making l ≥ εm/2 errors, the probability it's all in S₂ is ≤ (1/2)^l
  -- 3. Combine via union bound.
  -- The formal proof requires a Radon-Nikodym / disintegration argument on the sample space.
  sorry

end UnionBound

section SampleSizeBound

/-!
## Sample Size Bound

From the symmetrization bound, we can solve for m:
  growthFunction(C, 2m) · (1/2)^{εm/2} ≤ δ/2
⟺ log(growthFunction) - (εm/2) · log(2) ≤ log(δ/2)
⟺ m ≥ (2/ε) · (log(growthFunction(C,2m)) + log(2/δ))
-/

/-- **Sample size bound**: If m satisfies the sample complexity condition,
then Pr[B] ≤ δ/2.

Note: `hm` uses natural logarithm throughout, matching the (1/2)^{εm/2} bound via
the identity (1/2)^{εm/2} = exp(-(εm/2) · log 2). -/
theorem sample_size_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε δ : ℝ) (m : ℕ)
    (hε : ε > 0) (hδ : δ > 0)
    (hm : (2 / ε) * (Real.log (growthFunction C (2 * m)) + Real.log (2 / δ)) ≤
          m * Real.log 2) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤ ENNReal.ofReal (δ / 2) := by
  calc (sampleMeasure D (2 * m)) {S | EventB C c D ε m S}
      ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) :=
        symmetrization_bound C c D ε m hε
    _ ≤ ENNReal.ofReal (δ / 2) := by
        apply ENNReal.ofReal_le_ofReal
        -- Case split: if growthFunction = 0, LHS = 0 ≤ δ/2 trivially.
        rcases Nat.eq_zero_or_pos (growthFunction C (2 * m)) with h0 | hgpos
        · simp only [h0, Nat.cast_zero, zero_mul]
          linarith
        · -- growthFunction > 0; use logarithm argument.
          have hg_pos : (0 : ℝ) < growthFunction C (2 * m) := by exact_mod_cast hgpos
          have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
          have hδ2 : (0 : ℝ) < δ / 2 := by linarith
          -- (1/2)^(ε*m/2) = exp(-(ε*m/2) * log 2)  [via Real.rpow]
          have hrpow : (1 / 2 : ℝ) ^ (ε * ↑m / 2) =
              Real.exp (-(ε * ↑m / 2) * Real.log 2) := by
            rw [Real.rpow_def_of_pos (by norm_num)]
            congr 1
            rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
            ring
          rw [hrpow]
          -- Take log of both sides: log(g * exp(-...)) ≤ log(δ/2)
          rw [← Real.log_le_log_iff (by positivity) hδ2]
          rw [Real.log_mul hg_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
          -- Goal: log g - (ε*m/2) * log 2 ≤ log(δ/2) = log δ - log 2
          rw [show Real.log (δ / 2) = Real.log δ - Real.log 2 from
            Real.log_div hδ.ne' (by norm_num)]
          -- From hm: (2/ε) * (log g + log(2/δ)) ≤ m * log 2
          -- Rearrange: log g + log(2/δ) ≤ ε*m/2 * log 2
          have hm' : Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ) ≤
              ε * ↑m / 2 * Real.log 2 := by
            have hε2 : (0 : ℝ) < ε / 2 := by positivity
            calc Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)
                = (2 / ε) * (Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)) * (ε / 2) := by
                    field_simp
              _ ≤ (↑m * Real.log 2) * (ε / 2) := by
                    apply mul_le_mul_of_nonneg_right hm hε2.le
              _ = ε * ↑m / 2 * Real.log 2 := by ring
          -- log(2/δ) = log 2 - log δ
          have hlog2dδ : Real.log (2 / δ) = Real.log 2 - Real.log δ := by
            rw [Real.log_div (by norm_num) hδ.ne']
          linarith

end SampleSizeBound
