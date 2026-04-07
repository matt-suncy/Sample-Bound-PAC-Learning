import MAMFinalProject.Definitions
import MAMFinalProject.Hypergeometric
import MAMFinalProject.GhostSample
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
    Nat.card (Set.range fun h : C => restrictToSample h.val S) ≤ growthFunction C m :=
  le_ciSup_of_le (OrderTop.bddAbove _) S le_rfl

/-- The growth function is bounded above by 2^m (all possible subsets of Fin m). -/
lemma growthFunction_le_two_pow (C : Set (Concept X)) (m : ℕ) :
    growthFunction C m ≤ 2 ^ m := by
  apply ciSup_le
  intro S
  calc Nat.card (Set.range fun h : C => restrictToSample h.val S)
      ≤ Nat.card (Finset (Fin m)) := by
        apply Nat.card_le_card_of_injOn id (fun _ _ => Set.mem_univ _)
        simp [Set.InjOn]
    _ = 2 ^ m := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_finset_fin_le]

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
then Pr[B] ≤ δ/2. -/
theorem sample_size_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε δ : ℝ) (m : ℕ)
    (hε : ε > 0) (hδ : δ > 0)
    (hm : (2 / ε) * (Real.log (growthFunction C (2 * m)) + Real.log (2 / δ)) ≤ m) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤ ENNReal.ofReal (δ / 2) := by
  -- The proof: apply symmetrization_bound, then verify the exponential bound ≤ δ/2.
  -- From hm: ε*m/2 ≥ log(Π_C(2m)) + log(2/δ)
  -- So: Π_C(2m) * (1/2)^{εm/2} = Π_C(2m) * exp(-εm·log(2)/2)
  --                               ≤ exp(log Π_C(2m) - εm·log(2)/2)
  --                               ≤ exp(log(δ/2)) = δ/2
  calc (sampleMeasure D (2 * m)) {S | EventB C c D ε m S}
      ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) :=
        symmetrization_bound C c D ε m hε
    _ ≤ ENNReal.ofReal (δ / 2) := by
        apply ENNReal.ofReal_le_ofReal
        -- Need: Π_C(2m) * (1/2)^{εm/2} ≤ δ/2
        -- This follows from the hypothesis hm via logarithms.
        sorry

end SampleSizeBound
