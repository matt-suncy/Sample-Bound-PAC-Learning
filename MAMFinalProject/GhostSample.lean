import MAMFinalProject.Definitions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set Classical

variable {X : Type*} [MeasurableSpace X]

/-!
# Ghost Sample Lemma (Double Sample Trick)

The central probabilistic argument in the VC symmetrization proof.
We draw a double sample S of 2m points iid from D and split into halves S₁ and S₂.

**Event A**: ∃ bad hypothesis h ∈ C (true error ≥ ε) consistent with S₁.
**Event B**: ∃ bad hypothesis h ∈ C consistent with S₁ AND making ≥ εm/2 errors on S₂.

The lemma shows Pr[A] ≤ 2·Pr[B], which is the key step in the symmetrization argument.
-/

section Events

variable (C : Set (Concept X)) (c : Concept X) (D : Measure X) (ε : ℝ) (m : ℕ)

/-- Hypothesis h is "bad": its true error is at least ε. -/
def isBadHypothesis [IsProbabilityMeasure D] (h : Concept X) : Prop :=
  ε ≤ (trueError D h c).toReal

/-- Hypothesis h is consistent with sample S₁ (zero empirical error on S₁). -/
def isConsistentWith (h c : Concept X) (S₁ : Fin m → X) : Prop :=
  ∀ i : Fin m, ¬ isError h c (S₁ i)

/-- Hypothesis h makes ≥ εm/2 errors on S₂. -/
def hasManyErrors (h c : Concept X) (S₂ : Fin m → X) : Prop :=
  ε * m / 2 ≤ errorCount h c S₂

/-- **Event A**: there exists a bad hypothesis consistent with the first half of S. -/
def EventA (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis C c D ε h ∧ isConsistentWith m h c (firstHalf S)

/-- **Event B**: there exists a bad hypothesis consistent with S₁ and with ≥ εm/2 errors on S₂. -/
def EventB (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis C c D ε h ∧ isConsistentWith m h c (firstHalf S)
           ∧ hasManyErrors m h c ε (secondHalf S)

/-- Event B implies Event A. -/
lemma eventB_implies_eventA (S : Fin (2 * m) → X) (hB : EventB C c D ε m S) :
    EventA C c D ε m S := by
  obtain ⟨h, hh, hbad, hcons, _⟩ := hB
  exact ⟨h, hh, hbad, hcons⟩

end Events

section BernoulliErrorBound

/-!
## Bernoulli Error Bound

If h is a bad hypothesis (true error ≥ ε), then under the iid product measure P₂,
the probability that h makes ≥ εm/2 errors on a fresh m-sample is ≥ 1/2.

**Proof**: The number of errors is a sum of m iid Bernoulli(p) RVs with p ≥ ε.
- Mean ≥ εm
- Variance ≤ m·p·(1-p) ≤ m/4
- By Chebyshev: P[errors < εm/2] ≤ P[|errors - μ| > μ/2] ≤ Var/(μ/2)² ≤ 4/(εm) ≤ 1/2
  (using p ≥ ε and m ≥ 8/ε)
-/

/-- For a fixed bad hypothesis h, the indicator of "error at point x" has expectation ≥ ε. -/
lemma error_indicator_mean_ge (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (ε : ℝ) (hε : ε > 0)
    (hbad : ε ≤ (trueError D h c).toReal) :
    ε ≤ (D {x | isError h c x}).toReal := by
  -- The error set equals the symmetric difference (up to definitional equality)
  have : {x | isError h c x} = symmDiff h.val c.val := by
    ext x; simp [isError, symmDiff, Set.mem_symmDiff]
    tauto
  rw [this]; exact hbad

/-- **Key probabilistic lemma**: For a bad hypothesis h, the probability that a fresh
m-point sample (drawn iid from D) has ≥ εm/2 errors is ≥ 1/2.

This follows from Chebyshev's inequality applied to the sum of m iid Bernoulli(p)
random variables (p ≥ ε ≥ 0), using the assumption m ≥ 8/ε. -/
lemma bernoulli_error_lower_bound
    (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) (ε : ℝ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hbad : ε ≤ (trueError D h c).toReal) :
    ENNReal.ofReal (1 / 2) ≤
      (sampleMeasure D m) {S₂ : Fin m → X | hasManyErrors m h c ε S₂} := by
  -- The proof uses Chebyshev's inequality on the sum of iid Bernoulli error indicators.
  -- Let p = (trueError D h c).toReal ≥ ε. The error count on m points has:
  --   E[errors] = m * p ≥ m * ε
  --   Var[errors] = m * p * (1-p) ≤ m/4
  -- Chebyshev gives: P[errors < εm/2] ≤ P[|errors - mp| > mp/2] ≤ Var/(mp/2)² ≤ 4/(mp) ≤ 4/(mε) ≤ 1/2
  -- The sampleMeasure is Measure.pi (fun _ => D).
  -- Each coordinate i gives an independent Bernoulli(p) error indicator.
  sorry

end BernoulliErrorBound

section GhostSampleBound

/-!
## Main Ghost Sample Bound

Combines the product measure decomposition (Fubini) with the Bernoulli error bound
to prove Pr[A] ≤ 2·Pr[B].

**Proof sketch**:
1. Use the bijection Fin(2m) ≅ Fin(m) ⊕ Fin(m) to write
   P = P₁ ⊗ P₂ where P₁ = P₂ = sampleMeasure D m.
2. By Fubini (lintegral_prod): P[B] = ∫ S₁, P₂[B(S₁,·)] dP₁.
3. For S₁ where A holds, P₂[B(S₁,·)] ≥ 1/2 (by bernoulli_error_lower_bound).
4. Therefore P[B] ≥ (1/2) · P₁[A] = (1/2) · P[A].
-/

/-- The 2m-sample measure splits as a product of two m-sample measures. -/
lemma sampleMeasure_eq_prod (D : Measure X) [IsProbabilityMeasure D] (m : ℕ) :
    (sampleMeasure D (2 * m)).map (fun S => (firstHalf S, secondHalf S)) =
    (sampleMeasure D m).prod (sampleMeasure D m) := by
  -- This follows from the measure-preserving equivalence between
  -- Measure.pi (fun _ : Fin (2m) => D) and
  -- (Measure.pi (fun _ : Fin m => D)).prod (Measure.pi (fun _ : Fin m => D))
  -- via the bijection Fin (2m) ≅ Fin m ⊕ Fin m.
  sorry

/-- **Ghost Sample Lemma**: Under the iid double-sample measure,
Pr[EventA] ≤ 2 · Pr[EventB]. -/
theorem ghost_sample_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤
    2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} := by
  -- Write P₁ ⊗ P₂ for the product of two m-sample measures.
  set P := sampleMeasure D (2 * m)
  set P₁ := sampleMeasure D m
  set P₂ := sampleMeasure D m
  -- Key facts about B: B ⊆ A, and for S₁ where A holds, P₂[B(S₁,·)] ≥ 1/2.
  -- By Fubini, P[B] = ∫ S₁, P₂[B(S₁,·)] dP₁ ≥ (1/2) · P₁[A].
  -- Hence P[A] ≤ 2 · P[B].
  sorry

end GhostSampleBound
