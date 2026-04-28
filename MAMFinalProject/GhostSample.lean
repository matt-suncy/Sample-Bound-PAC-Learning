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

/-- Error sum Σᵢ errIndicator(Sᵢ) lies in [0, m] for any sample S. -/
private lemma errorSum_range (h c : Concept X) (m : ℕ) (S : Fin m → X) :
    ∑ i : Fin m, errIndicator h c (S i) ∈ Set.Icc 0 (m : ℝ) := by
  refine ⟨Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · simp [errIndicator]; split_ifs <;> norm_num
  · calc ∑ i : Fin m, errIndicator h c (S i)
          ≤ ∑ _ : Fin m, 1 :=
            Finset.sum_le_sum fun i _ => by simp [errIndicator]; split_ifs <;> norm_num
        _ = (m : ℝ) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The error count sum has MemLp 2 under the iid product measure. -/
private lemma errorSum_memlp (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) (m : ℕ) :
    MemLp (fun S : Fin m → X => ∑ i : Fin m, errIndicator h c (S i)) 2 (sampleMeasure D m) :=
  memLp_of_bounded
    (Filter.Eventually.of_forall (errorSum_range h c m))
    (Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i)).aestronglyMeasurable
    2

/-- Bridge: hasManyErrors holds iff the error sum meets the threshold ε·m/2. -/
private lemma hasManyErrors_iff_errorSum (h c : Concept X) (m : ℕ) (ε : ℝ) (S : Fin m → X) :
    hasManyErrors ε m h c S ↔ ε * ↑m / 2 ≤ ∑ i : Fin m, errIndicator h c (S i) := by
  simp [hasManyErrors, errIndicator, errorCount, Finset.sum_boole]

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
  rw [show {S : Fin m → X | hasManyErrors ε m h c S} =
          {S | ε * ↑m / 2 ≤ ∑ i : Fin m, errIndicator h c (S i)} from
        Set.ext fun S => hasManyErrors_iff_errorSum h c m ε S]
  exact measurableSet_le measurable_const
    (Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i))

/-- Pure algebra: if 8 ≤ μ, then μ ≤ (1/2) · (μ/2)². -/
private lemma mp_le_half_mp_div2_sq {mp : ℝ} (h : 8 ≤ mp) : mp ≤ 1 / 2 * (mp / 2) ^ 2 := by
  nlinarith [sq_nonneg mp]

/-- Pure arithmetic: 8/ε ≤ m and ε ≤ p with m > 0 imply 8 ≤ m * p. -/
private lemma eight_le_mul_of_div_le {ε p m : ℝ} (hε : 0 < ε) (hm : 8 / ε ≤ m)
    (hp : ε ≤ p) (hm_pos : 0 < m) : 8 ≤ m * p :=
  calc 8 = 8 / ε * ε := by field_simp
    _ ≤ m * ε := mul_le_mul_of_nonneg_right hm hε.le
    _ ≤ m * p := mul_le_mul_of_nonneg_left hp hm_pos.le

/-- Pure algebra: if Var ≤ μ and 8 ≤ μ, then Var / (μ/2)² ≤ 1/2. -/
private lemma var_div_sq_le_half {var μ : ℝ} (hvar : var ≤ μ) (hμ8 : 8 ≤ μ) :
    var / (μ / 2) ^ 2 ≤ 1 / 2 := by
  rw [div_le_iff₀ (sq_pos_of_pos (by linarith))]
  linarith [mp_le_half_mp_div2_sq hμ8]

/-- ENNReal arithmetic: 1 - ofReal(1/2) = ofReal(1/2). -/
private lemma one_sub_ofReal_half : (1 : ENNReal) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num

/-- The set of samples failing the hasManyErrors threshold is contained in the
Chebyshev large-deviation event {|Y - mean| ≥ mean/2}. -/
private lemma notManyErrors_subset_chebyshev_dev (h c : Concept X) (m : ℕ) (ε p : ℝ)
    (hm_real : 0 < (m : ℝ)) (hp_pos : 0 < p) (hbad : ε ≤ p) :
    {S : Fin m → X | ¬ hasManyErrors ε m h c S} ⊆
    {S | (m : ℝ) * p / 2 ≤ |∑ i : Fin m, errIndicator h c (S i) - (m : ℝ) * p|} := by
  intro S hS
  -- Uses: hasManyErrors_iff_errorSum
  simp only [Set.mem_setOf_eq, hasManyErrors_iff_errorSum, not_le] at hS
  have hYlt : ∑ i : Fin m, errIndicator h c (S i) < (m : ℝ) * p / 2 :=
    calc ∑ i : Fin m, errIndicator h c (S i) < ε * ↑m / 2 := hS
      _ ≤ p * ↑m / 2 := by linarith [mul_le_mul_of_nonneg_right hbad hm_real.le]
      _ = (m : ℝ) * p / 2 := by ring
  simp only [Set.mem_setOf_eq,
    abs_of_neg (show ∑ i : Fin m, errIndicator h c (S i) - (m : ℝ) * p < 0 by
      linarith [mul_pos hm_real hp_pos])]
  linarith

/-- If P(Eᶜ) ≤ 1/2 in a probability space, then P(E) ≥ 1/2. -/
private lemma prob_ge_half_of_compl_le_half {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {E : Set α} (hms : MeasurableSet E)
    (h : μ Eᶜ ≤ ENNReal.ofReal (1 / 2)) : ENNReal.ofReal (1 / 2) ≤ μ E := by
  -- Uses: prob_compl_eq_one_sub, one_sub_ofReal_half
  have hμE : μ E = 1 - μ Eᶜ := by
    rw [prob_compl_eq_one_sub hms, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [hμE]
  calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := one_sub_ofReal_half.symm
    _ ≤ 1 - μ Eᶜ := tsub_le_tsub_left h 1

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
random variables (p ≥ ε ≥ 0), using the assumption m ≥ 8/ε.

Proof outline:
  1. Arithmetic: 8 ≤ m·p           (eight_le_mul_of_div_le)
  2. Mean = m·p, Var ≤ m·p          (errorSum_integral, errorSum_variance_le)
  3. Chebyshev: P(|Y−mp| ≥ mp/2) ≤ Var/(mp/2)²  (meas_ge_le_variance_div_sq, errorSum_memlp)
  4. Algebraic bound: Var/(mp/2)² ≤ 1/2         (var_div_sq_le_half)
  5. Subset: ¬hasManyErrors ⊆ large-deviation event (notManyErrors_subset_chebyshev_dev)
  6. Flip: P(Eᶜ) ≤ 1/2 → P(E) ≥ 1/2            (prob_ge_half_of_compl_le_half) -/
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
  -- Uses: eight_le_mul_of_div_le
  have hmp8 : 8 ≤ (m : ℝ) * p := eight_le_mul_of_div_le hε hm hbad hm_real
  let Y : (Fin m → X) → ℝ := fun S => ∑ i : Fin m, errIndicator h c (S i)
  -- Uses: errorSum_integral, errorSum_variance_le
  have hEY : ∫ S : Fin m → X, Y S ∂(sampleMeasure D m) = (m : ℝ) * p :=
    errorSum_integral D h c m
  have hVarY : variance Y (sampleMeasure D m) ≤ (m : ℝ) * p :=
    errorSum_variance_le D h c m
  -- Uses: meas_ge_le_variance_div_sq, errorSum_memlp
  have hCheby := meas_ge_le_variance_div_sq (μ := sampleMeasure D m)
    (errorSum_memlp D h c m) (show 0 < (m : ℝ) * p / 2 by linarith)
  rw [hEY] at hCheby
  -- Uses: var_div_sq_le_half
  have hBound : ENNReal.ofReal (variance Y (sampleMeasure D m) / ((m : ℝ) * p / 2) ^ 2) ≤
                ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal (var_div_sq_le_half hVarY hmp8)
  -- Uses: notManyErrors_subset_chebyshev_dev
  have hPcomp : (sampleMeasure D m) {S | hasManyErrors ε m h c S}ᶜ ≤ ENNReal.ofReal (1 / 2) := by
    apply (measure_mono _).trans (hCheby.trans hBound)
    rw [show {S : Fin m → X | hasManyErrors ε m h c S}ᶜ =
            {S | ¬ hasManyErrors ε m h c S} from by ext; simp]
    exact notManyErrors_subset_chebyshev_dev h c m ε p hm_real hp_pos hbad
  -- Uses: prob_ge_half_of_compl_le_half, many_errors_measurableSet
  exact prob_ge_half_of_compl_le_half (many_errors_measurableSet h c m ε) hPcomp

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

/-- The probability of a product-space event under the 2m-sample equals its probability
under the product of two m-sample measures.

Uses: sampleMeasure_eq_prod -/
lemma event_prob_eq_prod (D : Measure X) [IsProbabilityMeasure D] (m : ℕ)
    {E : Set ((Fin m → X) × (Fin m → X))} (hE : MeasurableSet E) :
    (sampleMeasure D (2 * m)) {S | (firstHalf S, secondHalf S) ∈ E} =
    ((sampleMeasure D m).prod (sampleMeasure D m)) E := by
  have hf_meas : Measurable (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) :=
    Measurable.prod (measurable_pi_lambda _ fun i => measurable_pi_apply _)
                    (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  rw [show {S : Fin (2 * m) → X | (firstHalf S, secondHalf S) ∈ E} =
          (fun S => (firstHalf S, secondHalf S)) ⁻¹' E from rfl,
      ← Measure.map_apply hf_meas hE, sampleMeasure_eq_prod D m]

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

/-- ENNReal arithmetic: 2 * ofReal(1/2) = 1. -/
private lemma two_mul_ofReal_half : (2 : ENNReal) * ENNReal.ofReal (1 / 2) = 1 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  exact ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **Ghost Sample Lemma**: Under the iid double-sample measure,
Pr[EventA] ≤ 2 · Pr[EventB].

Proof outline:
  1. Translate events to product space A_prod, B_prod     (A_prod_measurable, B_prod_measurable)
  2. Rewrite probabilities via the product measure        (event_prob_eq_prod)
  3. Apply Fubini / lintegral_mono pointwise
  4. For each S₁ witnessing EventA: B-slice ≥ 1/2         (bernoulli_error_lower_bound)
  5. Conclude 1 = 2 · (1/2) ≤ 2 · P(B-slice)            (two_mul_ofReal_half) -/
theorem ghost_sample_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hC : Set.Countable C) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤
    2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} := by
  -- Product-space versions of Events A and B
  let A_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1}
  let B_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
         hasManyErrors ε m h c p.2}
  -- Uses: A_prod_measurable, B_prod_measurable
  have hA_meas : MeasurableSet A_prod := A_prod_measurable C c D ε m hC
  have hB_meas : MeasurableSet B_prod := B_prod_measurable C c D ε m hC
  -- Uses: event_prob_eq_prod (which absorbs sampleMeasure_eq_prod + Measure.map_apply)
  have hPA : (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} =
      ((sampleMeasure D m).prod (sampleMeasure D m)) A_prod := by
    rw [show {S : Fin (2 * m) → X | EventA C c D ε m S} =
            {S | (firstHalf S, secondHalf S) ∈ A_prod} from by
          ext S; simp [EventA, A_prod, isBadHypothesis, isConsistentWith]]
    exact event_prob_eq_prod D m hA_meas
  have hPB : (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} =
      ((sampleMeasure D m).prod (sampleMeasure D m)) B_prod := by
    rw [show {S : Fin (2 * m) → X | EventB C c D ε m S} =
            {S | (firstHalf S, secondHalf S) ∈ B_prod} from by
          ext S; simp [EventB, B_prod, isBadHypothesis, isConsistentWith, hasManyErrors]]
    exact event_prob_eq_prod D m hB_meas
  rw [hPA, hPB, Measure.prod_apply hA_meas, Measure.prod_apply hB_meas]
  -- Factor constant 2 into integral (Uses: lintegral_const_mul)
  have hB_slice_meas : Measurable (fun S₁ : Fin m → X =>
      (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod)) :=
    measurable_measure_prodMk_left hB_meas
  rw [(lintegral_const_mul 2 hB_slice_meas).symm]
  -- Pointwise bound: for each S₁, P(A-slice) ≤ 2 · P(B-slice)
  apply lintegral_mono; intro S₁
  change (sampleMeasure D m) (Prod.mk S₁ ⁻¹' A_prod) ≤
         2 * (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod)
  by_cases hS₁ : ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c S₁
  · -- S₁ witnesses EventA: A-slice = univ, B-slice ≥ 1/2
    have hAsec : Prod.mk S₁ ⁻¹' A_prod = Set.univ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hS₁
    rw [hAsec, measure_univ]
    obtain ⟨h, hh, hbad, hcons⟩ := hS₁
    -- Uses: bernoulli_error_lower_bound
    have hBsec_lb : ENNReal.ofReal (1 / 2) ≤
        (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod) :=
      (bernoulli_error_lower_bound D h c m ε hε hm hm_pos hbad).trans
        (measure_mono fun S₂ hS₂ => by
          simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq]
          exact ⟨h, hh, hbad, hcons, hS₂⟩)
    -- Uses: two_mul_ofReal_half
    calc (1 : ENNReal) = 2 * ENNReal.ofReal (1 / 2) := two_mul_ofReal_half.symm
      _ ≤ 2 * (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod) := mul_le_mul_right hBsec_lb 2
  · -- S₁ does not witness EventA: A-slice = ∅
    have hAsec : Prod.mk S₁ ⁻¹' A_prod = ∅ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq,
                          Set.mem_empty_iff_false, iff_false]
      exact fun ⟨h, hh, hbad, hcons⟩ => hS₁ ⟨h, hh, hbad, hcons⟩
    rw [hAsec, measure_empty]; exact zero_le _

end GhostSampleBound
