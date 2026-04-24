import MAMFinalProject.Definitions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory Set

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

/-- Hypothesis h is "bad": its true error is at least ε. -/
def isBadHypothesis (D : Measure X) [IsProbabilityMeasure D] (c : Concept X) (ε : ℝ)
    (h : Concept X) : Prop :=
  ε ≤ (trueError D h c).toReal

/-- Hypothesis h is consistent with sample S₁ (zero empirical error on S₁). -/
def isConsistentWith (h c : Concept X) {m : ℕ} (S₁ : Fin m → X) : Prop :=
  ∀ i : Fin m, ¬ isError h c (S₁ i)

/-- Hypothesis h makes ≥ εm/2 errors on S₂. -/
def hasManyErrors (ε : ℝ) (m : ℕ) (h c : Concept X) (S₂ : Fin m → X) : Prop :=
  ε * m / 2 ≤ errorCount h c S₂

/-- **Event A**: there exists a bad hypothesis consistent with the first half of S. -/
def EventA (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c (firstHalf S)

/-- **Event B**: there exists a bad hypothesis consistent with S₁ and with ≥ εm/2 errors on S₂. -/
def EventB (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c (firstHalf S)
           ∧ hasManyErrors ε m h c (secondHalf S)

/-- Event B implies Event A. -/
lemma eventB_implies_eventA (C : Set (Concept X)) (c : Concept X) (D : Measure X)
    [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X)
    (hB : EventB C c D ε m S) : EventA C c D ε m S := by
  obtain ⟨h, hh, hbad, hcons, _⟩ := hB
  exact ⟨h, hh, hbad, hcons⟩

end Events

/-! ## Shared Measurability Helpers -/

private lemma isError_set_symmDiff (h c : Concept X) :
    {x : X | isError h c x} = symmDiff h.val c.val := by
  ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto

lemma isError_measurableSet (h c : Concept X) : MeasurableSet {x : X | isError h c x} :=
  isError_set_symmDiff h c ▸ h.2.symmDiff c.2

section BernoulliErrorBound

/-!
## Bernoulli Error Bound

If h is a bad hypothesis (true error ≥ ε), then under the iid product measure,
the probability that h makes ≥ εm/2 errors on a fresh m-sample is ≥ 1/2.

**Proof**: The number of errors is a sum of m iid Bernoulli(p) RVs with p ≥ ε.
- Mean ≥ εm
- Variance ≤ m·p·(1-p) ≤ m/4
- By Chebyshev: P[errors < εm/2] ≤ P[|errors - μ| > μ/2] ≤ Var/(μ/2)² ≤ 4/(εm) ≤ 1/2
  (using p ≥ ε and m ≥ 8/ε)
-/

private noncomputable def errIndicator (h c : Concept X) : X → ℝ :=
  fun x => if isError h c x then 1 else 0

private lemma errIndicator_eq_indicator (h c : Concept X) :
    errIndicator h c = Set.indicator {x | isError h c x} 1 := by
  funext x; simp [errIndicator, Set.indicator, Set.mem_setOf_eq]

private lemma errIndicator_measurable (h c : Concept X) : Measurable (errIndicator h c) := by
  rw [errIndicator_eq_indicator]
  exact measurable_const.indicator (isError_measurableSet h c)

private lemma errIndicator_mem_Icc (h c : Concept X) (x : X) :
    errIndicator h c x ∈ Set.Icc 0 1 := by
  simp [errIndicator, Set.mem_Icc]; split_ifs <;> norm_num

private lemma errIndicator_memlp (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) :
    MemLp (errIndicator h c) 2 D :=
  memLp_of_bounded (Filter.Eventually.of_forall (errIndicator_mem_Icc h c))
    (errIndicator_measurable h c).aestronglyMeasurable 2

private lemma errIndicator_integral (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) :
    ∫ x, errIndicator h c x ∂D = (trueError D h c).toReal := by
  rw [errIndicator_eq_indicator, integral_indicator_one (isError_measurableSet h c),
      measureReal_def, isError_set_symmDiff]
  rfl

/-- The variance of the error indicator is bounded by the true error probability. -/
private lemma errIndicator_variance_le (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) : variance (errIndicator h c) D ≤ (trueError D h c).toReal := by
  set p := (trueError D h c).toReal
  have hp_le1 : p ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
  have hbd := variance_le_sub_mul_sub (μ := D)
    (Filter.Eventually.of_forall (errIndicator_mem_Icc h c))
    (errIndicator_measurable h c).aestronglyMeasurable.aemeasurable
  rw [errIndicator_integral] at hbd; simp only [sub_zero] at hbd
  calc variance (errIndicator h c) D ≤ (1 - p) * p := hbd
    _ ≤ 1 * p := mul_le_mul_of_nonneg_right (by linarith) hp_nonneg
    _ = p := one_mul p

private lemma errIndicator_integrable_coord (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) (i : Fin m) :
    Integrable (fun S : Fin m → X => errIndicator h c (S i))
      (Measure.pi (fun _ : Fin m => D)) := by
  have hmemlp : MemLp (fun S : Fin m → X => errIndicator h c (S i)) 2
      (Measure.pi (fun _ : Fin m => D)) :=
    memLp_of_bounded
      (Filter.Eventually.of_forall fun (S : Fin m → X) => errIndicator_mem_Icc h c (S i))
      ((errIndicator_measurable h c).comp (measurable_pi_apply i)).aestronglyMeasurable
      2
  exact hmemlp.integrable (by norm_num)

/-- E[Σᵢ errIndicator(Sᵢ)] = m · p under the iid product measure. -/
private lemma errorSum_integral (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) :
    ∫ S : Fin m → X, ∑ i : Fin m, errIndicator h c (S i) ∂(sampleMeasure D m) =
    (m : ℝ) * (trueError D h c).toReal := by
  simp only [sampleMeasure]
  calc ∫ S : Fin m → X, ∑ i : Fin m, errIndicator h c (S i)
          ∂Measure.pi (fun _ : Fin m => D)
      = ∑ i : Fin m, ∫ S : Fin m → X, errIndicator h c (S i)
          ∂Measure.pi (fun _ : Fin m => D) :=
          integral_finset_sum _ (fun i _ => errIndicator_integrable_coord D h c m i)
    _ = ∑ _ : Fin m, (trueError D h c).toReal := by
          apply Finset.sum_congr rfl; intro i _
          exact (integral_comp_eval (μ := fun _ : Fin m => D) (i := i)
            (errIndicator_measurable h c).aestronglyMeasurable).trans
            (errIndicator_integral D h c)
    _ = (m : ℝ) * (trueError D h c).toReal := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Var[Σᵢ errIndicator(Sᵢ)] ≤ m · p under the iid product measure. -/
private lemma errorSum_variance_le (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) :
    variance (fun S : Fin m → X => ∑ i : Fin m, errIndicator h c (S i)) (sampleMeasure D m) ≤
    (m : ℝ) * (trueError D h c).toReal := by
  have hvsumpi :
      variance (fun S : Fin m → X => ∑ i : Fin m, errIndicator h c (S i))
        (sampleMeasure D m) = ∑ _ : Fin m, variance (errIndicator h c) D := by
    rw [show (fun S : Fin m → X => ∑ i : Fin m, errIndicator h c (S i)) =
            ∑ i : Fin m, (fun S : Fin m → X => errIndicator h c (S i)) from by
          funext S; simp [Finset.sum_apply],
        show sampleMeasure D m = Measure.pi (fun _ : Fin m => D) from rfl]
    haveI : ∀ i : Fin m, IsProbabilityMeasure ((fun _ : Fin m => D) i) :=
      fun _ => ‹IsProbabilityMeasure D›
    have hv := variance_sum_pi (ι := Fin m) (μ := fun _ : Fin m => D)
      (X := fun _ : Fin m => errIndicator h c) (fun _ => errIndicator_memlp D h c)
    simp only [Function.const_apply] at hv; exact hv
  rw [hvsumpi]
  calc ∑ _ : Fin m, variance (errIndicator h c) D
      ≤ ∑ _ : Fin m, (trueError D h c).toReal :=
          Finset.sum_le_sum fun _ _ => errIndicator_variance_le D h c
    _ = (m : ℝ) * (trueError D h c).toReal := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- MeasurableSet for the hasManyErrors event. -/
private lemma many_errors_measurableSet (h c : Concept X) (m : ℕ) (ε : ℝ) :
    MeasurableSet {S : Fin m → X | hasManyErrors ε m h c S} := by
  have heq : {S : Fin m → X | hasManyErrors ε m h c S} =
      {S | ε * ↑m / 2 ≤ ∑ i : Fin m, errIndicator h c (S i)} :=
    Set.ext fun S => by simp [hasManyErrors, errIndicator, errorCount, Finset.sum_boole]
  rw [heq]
  exact measurableSet_le measurable_const
    (Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i))

/-- Pure algebra: when mp ≥ 8, we have mp ≤ (1/2) · (mp/2)². -/
private lemma mp_le_half_mp_div2_sq {mp : ℝ} (h : 8 ≤ mp) : mp ≤ 1 / 2 * (mp / 2) ^ 2 := by
  nlinarith [sq_nonneg mp]

/-- For a fixed bad hypothesis h, the indicator of "error at point x" has expectation ≥ ε. -/
lemma error_indicator_mean_ge (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (ε : ℝ) (hε : ε > 0)
    (hbad : ε ≤ (trueError D h c).toReal) :
    ε ≤ (D {x | isError h c x}).toReal := by
  rw [isError_set_symmDiff]; exact hbad

set_option maxHeartbeats 800000 in
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
      (sampleMeasure D m) {S₂ : Fin m → X | hasManyErrors ε m h c S₂} := by
  set p := (trueError D h c).toReal with hp_def
  have hp_pos : 0 < p := lt_of_lt_of_le hε hbad
  have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hmp_pos : 0 < (m : ℝ) * p := mul_pos hm_real hp_pos
  have hmp8 : 8 ≤ (m : ℝ) * p :=
    calc 8 = 8 / ε * ε := by field_simp
      _ ≤ (m : ℝ) * ε := mul_le_mul_of_nonneg_right hm hε.le
      _ ≤ (m : ℝ) * p := mul_le_mul_of_nonneg_left hbad hm_real.le
  -- Error sum Y = Σᵢ errIndicator h c (Sᵢ)
  let Y : (Fin m → X) → ℝ := fun S => ∑ i : Fin m, errIndicator h c (S i)
  have hY_meas : Measurable Y :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i)
  have hY_range : ∀ S : Fin m → X, Y S ∈ Set.Icc 0 (m : ℝ) := fun S => by
    refine ⟨Finset.sum_nonneg fun i _ => ?_, ?_⟩
    · simp [errIndicator]; split_ifs <;> norm_num
    · calc Y S ≤ ∑ _ : Fin m, 1 :=
              Finset.sum_le_sum fun i _ => by simp [errIndicator]; split_ifs <;> norm_num
          _ = (m : ℝ) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hY_memlp : MemLp Y 2 (sampleMeasure D m) :=
    memLp_of_bounded (Filter.Eventually.of_forall hY_range) hY_meas.aestronglyMeasurable 2
  -- hasManyErrors ↔ ε * m / 2 ≤ Y (bridge between domain def and Y)
  have hMany_iff : ∀ S : Fin m → X, hasManyErrors ε m h c S ↔ ε * ↑m / 2 ≤ Y S := fun S => by
    unfold hasManyErrors Y
    simp [errIndicator, errorCount, Finset.sum_boole]
  -- Mean and variance from extracted helpers
  have hEY : ∫ S : Fin m → X, Y S ∂(sampleMeasure D m) = (m : ℝ) * p :=
    errorSum_integral D h c m
  have hVarY : variance Y (sampleMeasure D m) ≤ (m : ℝ) * p :=
    errorSum_variance_le D h c m
  -- Chebyshev: P(|Y - mp| ≥ mp/2) ≤ Var/(mp/2)²
  have hCheby := meas_ge_le_variance_div_sq (μ := sampleMeasure D m) hY_memlp
    (show 0 < (m : ℝ) * p / 2 by linarith)
  rw [hEY] at hCheby
  -- Var/(mp/2)² ≤ 1/2 (uses pure algebraic bound)
  have hBound : ENNReal.ofReal (variance Y (sampleMeasure D m) / ((m : ℝ) * p / 2) ^ 2) ≤
                ENNReal.ofReal (1 / 2) := by
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (sq_pos_of_pos (by linarith))]
    linarith [mp_le_half_mp_div2_sq hmp8]
  -- Complement of hasManyErrors ⊆ Chebyshev deviation event
  have hSubset : {S : Fin m → X | ¬ hasManyErrors ε m h c S} ⊆
                 {S | (m : ℝ) * p / 2 ≤ |Y S - (m : ℝ) * p|} := by
    intro S hS
    simp only [Set.mem_setOf_eq, hMany_iff, not_le] at hS
    simp only [Set.mem_setOf_eq]
    have hYlt : Y S < (m : ℝ) * p / 2 :=
      calc Y S < ε * ↑m / 2 := hS
        _ ≤ p * ↑m / 2 := by linarith [mul_le_mul_of_nonneg_right hbad hm_real.le]
        _ = (m : ℝ) * p / 2 := by ring
    rw [abs_of_neg (by linarith : Y S - (m : ℝ) * p < 0)]; linarith
  -- P(¬hasManyErrors) ≤ 1/2 via Chebyshev
  have hPcomp : (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} ≤ ENNReal.ofReal (1 / 2) :=
    (measure_mono hSubset).trans (hCheby.trans hBound)
  -- Conclude: P(hasManyErrors) = 1 - P(¬hasManyErrors) ≥ 1/2
  have hms : MeasurableSet {S : Fin m → X | hasManyErrors ε m h c S} :=
    many_errors_measurableSet h c m ε
  have hcompl_good : (sampleMeasure D m) {S | hasManyErrors ε m h c S} =
                     1 - (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} := by
    rw [show {S : Fin m → X | ¬ hasManyErrors ε m h c S} = {S | hasManyErrors ε m h c S}ᶜ
          from by ext; simp,
        prob_compl_eq_one_sub hms,
        ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  have h1sub : (1 : ENNReal) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
  rw [hcompl_good]
  calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := h1sub.symm
    _ ≤ 1 - (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} :=
        tsub_le_tsub_left hPcomp 1

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
  simp only [sampleMeasure]
  have h2m : m + m = 2 * m := by ring
  let f : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (Fin.castOrderIso h2m).toEquiv
  have step1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => X) f).symm
      (Measure.pi fun _ : Fin (2 * m) => D)
      (Measure.pi fun _ : Fin m ⊕ Fin m => D) :=
    MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : Fin (2 * m) => D) f)
  have step2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X))
      (Measure.pi fun _ : Fin m ⊕ Fin m => D)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => D)
  have comp := step2.comp step1
  have hfun : (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) =
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm := by
    funext S
    simp only [Function.comp]
    have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm S = S ∘ f := by
      funext j
      change (Equiv.piCongrLeft (fun _ => X) f).symm S j = S (f j)
      exact Equiv.piCongrLeft_symm_apply (fun _ => X) f S j
    rw [hcoe]
    apply Prod.ext
    · funext i; simp only [firstHalf]; congr 1
    · funext i; simp only [secondHalf]; congr 1
  rw [hfun]
  exact comp.map_eq

/-- The consistent set is a pi-set preimage. -/
private lemma consistent_set_eq_pi (hh c : Concept X) (m : ℕ) :
    {S₁ : Fin m → X | isConsistentWith hh c S₁} =
    Set.pi Set.univ (fun _ => {x | isError hh c x}ᶜ) := by
  ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff]

/-- The A-product set is measurable. -/
private lemma A_prod_measurable (C : Set (Concept X)) (c : Concept X)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (hC : Set.Countable C) :
    MeasurableSet {p : (Fin m → X) × (Fin m → X) |
      ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1} := by
  have hA_eq : {p : (Fin m → X) × (Fin m → X) |
        ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1} =
      ⋃ hh ∈ C, {p | isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1} := by
    ext p; simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hC, hbad, hcons⟩; exact ⟨h, hC, hbad, hcons⟩
    · rintro ⟨h, hC, hbad, hcons⟩; exact ⟨h, hC, hbad, hcons⟩
  rw [hA_eq]
  apply MeasurableSet.biUnion hC; intro hh _
  by_cases hbad : isBadHypothesis D c ε hh
  · rw [show {p : (Fin m → X) × (Fin m → X) |
              isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1} =
            Prod.fst ⁻¹' {S₁ | isConsistentWith hh c S₁} from by ext p; simp [hbad],
        consistent_set_eq_pi]
    exact measurable_fst (MeasurableSet.univ_pi (fun _ => (isError_measurableSet hh c).compl))
  · simp [hbad]

/-- The B-product set is measurable. -/
private lemma B_prod_measurable (C : Set (Concept X)) (c : Concept X)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (hC : Set.Countable C) :
    MeasurableSet {p : (Fin m → X) × (Fin m → X) |
      ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
               hasManyErrors ε m h c p.2} := by
  have hB_eq : {p : (Fin m → X) × (Fin m → X) |
        ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
                 hasManyErrors ε m h c p.2} =
      ⋃ hh ∈ C, {p | isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1 ∧
                     hasManyErrors ε m hh c p.2} := by
    ext p; simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hC, hbad, hcons, hmany⟩; exact ⟨h, hC, hbad, hcons, hmany⟩
    · rintro ⟨h, hC, hbad, hcons, hmany⟩; exact ⟨h, hC, hbad, hcons, hmany⟩
  rw [hB_eq]
  apply MeasurableSet.biUnion hC; intro hh _
  by_cases hbad : isBadHypothesis D c ε hh
  · rw [show {p : (Fin m → X) × (Fin m → X) |
              isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1 ∧
              hasManyErrors ε m hh c p.2} =
            {p | isConsistentWith hh c p.1} ∩ {p | hasManyErrors ε m hh c p.2} from by
          ext p; simp [hbad]]
    have hcons_meas : MeasurableSet {p : (Fin m → X) × (Fin m → X) | isConsistentWith hh c p.1} := by
      rw [show {p : (Fin m → X) × (Fin m → X) | isConsistentWith hh c p.1} =
              Prod.fst ⁻¹' {S₁ | isConsistentWith hh c S₁} from rfl,
          consistent_set_eq_pi]
      exact measurable_fst (MeasurableSet.univ_pi (fun _ => (isError_measurableSet hh c).compl))
    exact hcons_meas.inter (measurable_snd (many_errors_measurableSet hh c m ε))
  · simp [hbad]

/-- **Ghost Sample Lemma**: Under the iid double-sample measure,
Pr[EventA] ≤ 2 · Pr[EventB]. -/
theorem ghost_sample_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hC : Set.Countable C) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤
    2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} := by
  set P₁ := sampleMeasure D m
  let f : (Fin (2 * m) → X) → (Fin m → X) × (Fin m → X) :=
    fun S => (firstHalf S, secondHalf S)
  have hf_meas : Measurable f := by
    apply Measurable.prod
    · exact measurable_pi_lambda _ fun i => measurable_pi_apply _
    · exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  -- Product-space versions of Events A and B
  let A_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1}
  let B_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
         hasManyErrors ε m h c p.2}
  have hA_meas : MeasurableSet A_prod := A_prod_measurable C c D ε m hC
  have hB_meas : MeasurableSet B_prod := B_prod_measurable C c D ε m hC
  -- Preimage equalities
  have hf_preimage_A : f ⁻¹' A_prod = {S | EventA C c D ε m S} := by
    ext S; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, f, Prod.fst,
                      EventA, isBadHypothesis, isConsistentWith]
  have hf_preimage_B : f ⁻¹' B_prod = {S | EventB C c D ε m S} := by
    ext S; simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq, f,
                      EventB, isBadHypothesis, isConsistentWith, hasManyErrors]
  -- Pull back to product measure
  have hProd_eq := sampleMeasure_eq_prod D m
  have hPA : (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} = (P₁.prod P₁) A_prod := by
    rw [← hf_preimage_A, ← Measure.map_apply hf_meas hA_meas, hProd_eq]
  have hPB : (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} = (P₁.prod P₁) B_prod := by
    rw [← hf_preimage_B, ← Measure.map_apply hf_meas hB_meas, hProd_eq]
  rw [hPA, hPB, Measure.prod_apply hA_meas, Measure.prod_apply hB_meas]
  -- Factor constant 2 into integral
  have hB_slice_meas : Measurable (fun S₁ : Fin m → X => P₁ (Prod.mk S₁ ⁻¹' B_prod)) :=
    measurable_measure_prodMk_left hB_meas
  rw [show (2 : ENNReal) * ∫⁻ S₁, P₁ (Prod.mk S₁ ⁻¹' B_prod) ∂P₁ =
          ∫⁻ S₁, 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod) ∂P₁ from
    (lintegral_const_mul 2 hB_slice_meas).symm]
  -- Pointwise comparison via bernoulli_error_lower_bound
  apply lintegral_mono; intro S₁
  change P₁ (Prod.mk S₁ ⁻¹' A_prod) ≤ 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod)
  by_cases hS₁ : ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c S₁
  · have hAsec : Prod.mk S₁ ⁻¹' A_prod = Set.univ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_univ,
                          iff_true]; exact hS₁
    rw [hAsec, measure_univ]
    obtain ⟨h, hh, hbad, hcons⟩ := hS₁
    have hBsec_lb : ENNReal.ofReal (1 / 2) ≤ P₁ (Prod.mk S₁ ⁻¹' B_prod) :=
      (bernoulli_error_lower_bound D h c m ε hε hm hm_pos hbad).trans
        (measure_mono fun S₂ hS₂ => by
          simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq]
          exact ⟨h, hh, hbad, hcons, hS₂⟩)
    have h12 : 2 * ENNReal.ofReal (1 / 2) = 1 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat]
      exact ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc (1 : ENNReal) = 2 * ENNReal.ofReal (1 / 2) := h12.symm
      _ ≤ 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod) := mul_le_mul_right hBsec_lb 2
  · have hAsec : Prod.mk S₁ ⁻¹' A_prod = ∅ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                          iff_false]
      intro ⟨h, hh, hbad, hcons⟩; exact hS₁ ⟨h, hh, hbad, hcons⟩
    rw [hAsec, measure_empty]; exact zero_le _

end GhostSampleBound
