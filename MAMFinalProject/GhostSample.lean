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
-- NOTE: we should consider stating that 0 < ε < 1 in the definition
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
-- NOTE: maybe we should not define event B to include that h is a bad hypothesis.
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

set_option maxHeartbeats 800000 in
/-- **Key probabilistic lemma**: For a bad hypothesis h, the probability that a fresh
m-point sample (drawn iid from D) has ≥ εm/2 errors is ≥ 1/2.

Note: The default (400000 heartbeats) isn't enough because that lemma
involves heavy automation — likely simp, norm_num, or linarith calls over real-valued probability expressions that take a long time to elaborate. Without it, Lean
would abort with a "maximum heartbeats reached" error mid-proof.

This follows from Chebyshev's inequality applied to the sum of m iid Bernoulli(p)
random variables (p ≥ ε ≥ 0), using the assumption m ≥ 8/ε. -/
lemma bernoulli_error_lower_bound
    (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) (ε : ℝ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hbad : ε ≤ (trueError D h c).toReal) :
    ENNReal.ofReal (1 / 2) ≤
      (sampleMeasure D m) {S₂ : Fin m → X | hasManyErrors ε m h c S₂} := by
  -- Setup: let p = true error probability ≥ ε
  set p := (trueError D h c).toReal with hp_def
  have hp_pos : 0 < p := lt_of_lt_of_le hε hbad
  have hp_le1 : p ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hmp_pos : 0 < (m : ℝ) * p := mul_pos hm_real hp_pos
  -- 1. Define the error indicator and the error sum Y
  let errInd : X → ℝ := fun x => if isError h c x then 1 else 0
  have herrSet : MeasurableSet {x : X | isError h c x} := by
    have : {x : X | isError h c x} = symmDiff h.val c.val := by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
    rw [this]; exact h.2.symmDiff c.2
  have herrInd_eq : errInd = Set.indicator {x : X | isError h c x} 1 := by
    funext x; simp [errInd, Set.indicator, Set.mem_setOf_eq]
  have herrInd_meas : Measurable errInd := by
    rw [herrInd_eq]; exact measurable_const.indicator herrSet
  have herrInd_aesm : AEStronglyMeasurable errInd D := herrInd_meas.aestronglyMeasurable
  have herrInd_range : ∀ᵐ x ∂D, errInd x ∈ Set.Icc 0 1 :=
    Filter.Eventually.of_forall fun x => by
      simp only [errInd, Set.mem_Icc]; split_ifs <;> norm_num
  have herrInd_memlp : MemLp errInd 2 D := memLp_of_bounded herrInd_range herrInd_aesm 2
  -- 2. Mean of errInd = p
  have hset_eq : {x : X | isError h c x} = symmDiff h.val c.val := by
    ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
  have hEerrInd : ∫ x, errInd x ∂D = p := by
    rw [herrInd_eq, integral_indicator_one herrSet, measureReal_def, hset_eq]
    rfl
  -- 3. Error sum Y and its connection to errorCount
  let Y : (Fin m → X) → ℝ := fun S => ∑ i : Fin m, errInd (S i)
  have hY_eq : ∀ S : Fin m → X, Y S = (errorCount h c S : ℝ) := fun S => by
    simp [Y, errInd, errorCount, Finset.sum_boole]
  have hMany_iff : ∀ S : Fin m → X, hasManyErrors ε m h c S ↔ ε * ↑m / 2 ≤ Y S := fun S => by
    unfold hasManyErrors; rw [← hY_eq S]
  -- 4. Y is measurable and bounded
  have hY_meas : Measurable Y :=
    Finset.measurable_sum Finset.univ fun i _ => herrInd_meas.comp (measurable_pi_apply i)
  have hY_range : ∀ᵐ S ∂(sampleMeasure D m), Y S ∈ Set.Icc 0 (m : ℝ) :=
    Filter.Eventually.of_forall fun S => by
      refine ⟨Finset.sum_nonneg fun i _ => ?_, ?_⟩
      · simp [errInd]; split_ifs <;> norm_num
      · calc Y S ≤ ∑ _ : Fin m, 1 :=
              Finset.sum_le_sum fun i _ => by simp [errInd]; split_ifs <;> norm_num
          _ = (m : ℝ) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hY_memlp : MemLp Y 2 (sampleMeasure D m) :=
    memLp_of_bounded hY_range hY_meas.aestronglyMeasurable 2
  -- 5. Mean of Y = m * p
  have hEY : ∫ S : Fin m → X, Y S ∂(sampleMeasure D m) = (m : ℝ) * p := by
    simp only [Y, sampleMeasure]
    -- Integrability of each coordinate function under Measure.pi
    have hint : ∀ i : Fin m, Integrable (fun S : Fin m → X => errInd (S i))
        (Measure.pi (fun _ : Fin m => D)) := fun i =>
      (memLp_of_bounded
        (Filter.Eventually.of_forall fun S => by
          change (if isError h c (S i) then (1:ℝ) else 0) ∈ Set.Icc 0 1
          split_ifs <;> norm_num)
        ((herrInd_meas.comp (measurable_pi_apply i)).aestronglyMeasurable) 2).integrable
        (by norm_num)
    calc ∫ S : Fin m → X, ∑ i : Fin m, errInd (S i) ∂Measure.pi (fun _ : Fin m => D)
        = ∑ i : Fin m, ∫ S : Fin m → X, errInd (S i) ∂Measure.pi (fun _ : Fin m => D) :=
            integral_finset_sum _ (fun i _ => hint i)
      _ = ∑ _ : Fin m, p := by
            apply Finset.sum_congr rfl; intro i _
            exact (integral_comp_eval (μ := fun _ : Fin m => D) (i := i) herrInd_aesm).trans
              hEerrInd
      _ = (m : ℝ) * p := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 6. Variance of errInd ≤ p
  have hVarerrInd : variance errInd D ≤ p := by
    have hbd := variance_le_sub_mul_sub (μ := D) herrInd_range herrInd_aesm.aemeasurable
    rw [hEerrInd] at hbd; simp only [sub_zero] at hbd
    calc variance errInd D ≤ (1 - p) * p := hbd
      _ ≤ 1 * p := mul_le_mul_of_nonneg_right (by linarith) hp_pos.le
      _ = p := one_mul p
  -- 7. Variance of Y ≤ m * p
  have hVarY : variance Y (sampleMeasure D m) ≤ (m : ℝ) * p := by
    have hvsumpi : variance Y (sampleMeasure D m) = ∑ _ : Fin m, variance errInd D := by
      -- Rewrite Y and sampleMeasure to explicit forms, then apply variance_sum_pi
      rw [show Y = ∑ i : Fin m, (fun S : Fin m → X => errInd (S i)) from by
            funext S
            change ∑ i : Fin m, errInd (S i) = (∑ i : Fin m, (fun S : Fin m → X => errInd (S i))) S
            simp [Finset.sum_apply],
          show sampleMeasure D m = Measure.pi (fun _ : Fin m => D) from rfl]
      haveI : ∀ i : Fin m, IsProbabilityMeasure ((fun _ : Fin m => D) i) :=
        fun _ => ‹IsProbabilityMeasure D›
      have h := variance_sum_pi (ι := Fin m) (μ := fun _ : Fin m => D)
        (X := fun _ : Fin m => errInd) (fun _ => herrInd_memlp)
      simp only [Function.const_apply] at h
      exact h
    rw [hvsumpi]
    calc ∑ _ : Fin m, variance errInd D
        ≤ ∑ _ : Fin m, p := Finset.sum_le_sum fun _ _ => hVarerrInd
      _ = (m : ℝ) * p := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 8. Chebyshev with c = m*p/2
  have hc_pos : 0 < (m : ℝ) * p / 2 := by linarith
  have hCheby := meas_ge_le_variance_div_sq (μ := sampleMeasure D m) hY_memlp hc_pos
  rw [hEY] at hCheby
  -- 9. The Chebyshev bound ≤ 1/2
  have hmp8 : 8 ≤ (m : ℝ) * p :=
    calc 8 = 8 / ε * ε := by field_simp
      _ ≤ (m : ℝ) * ε := mul_le_mul_of_nonneg_right hm hε.le
      _ ≤ (m : ℝ) * p := mul_le_mul_of_nonneg_left hbad hm_real.le
  have hBound : ENNReal.ofReal (variance Y (sampleMeasure D m) / ((m : ℝ) * p / 2) ^ 2) ≤
                ENNReal.ofReal (1 / 2) := by
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (sq_pos_of_pos hc_pos)]
    calc variance Y (sampleMeasure D m)
        ≤ (m : ℝ) * p := hVarY
      _ ≤ 1 / 2 * ((m : ℝ) * p / 2) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ) * p), hmp8]
  -- 10. Complement of hasManyErrors ⊆ Chebyshev event
  have hSubset : {S : Fin m → X | ¬ hasManyErrors ε m h c S} ⊆
                 {S | (m : ℝ) * p / 2 ≤ |Y S - (m : ℝ) * p|} := by
    intro S hS
    simp only [Set.mem_setOf_eq, hMany_iff, not_le] at hS
    simp only [Set.mem_setOf_eq]
    have hYS_lt : Y S < (m : ℝ) * p / 2 := by
      calc Y S < ε * ↑m / 2 := hS
        _ ≤ p * ↑m / 2 := by linarith [mul_le_mul_of_nonneg_right hbad hm_real.le]
        _ = (m : ℝ) * p / 2 := by ring
    rw [abs_of_neg (by linarith : Y S - (m : ℝ) * p < 0)]; linarith
  -- 11. P(¬hasManyErrors) ≤ 1/2
  have hPcomp : (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} ≤ ENNReal.ofReal (1 / 2) :=
    (measure_mono hSubset).trans (hCheby.trans hBound)
  -- 12. MeasurableSet of the good event
  have hms_good : MeasurableSet {S : Fin m → X | hasManyErrors ε m h c S} := by
    have : {S : Fin m → X | hasManyErrors ε m h c S} = {S | ε * ↑m / 2 ≤ Y S} :=
      Set.ext (fun S => hMany_iff S)
    rw [this]; exact measurableSet_le measurable_const hY_meas
  -- 13. Conclude: P(hasManyErrors) = 1 - P(¬hasManyErrors) ≥ 1 - 1/2 = 1/2
  have hbad_eq : {S : Fin m → X | ¬ hasManyErrors ε m h c S} =
                 {S | hasManyErrors ε m h c S}ᶜ := by ext; simp
  have hcompl_good : (sampleMeasure D m) {S | hasManyErrors ε m h c S} =
                     1 - (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} := by
    rw [hbad_eq, prob_compl_eq_one_sub hms_good,
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
  -- Build the equivalence Fin m ⊕ Fin m ≃ Fin (2*m)
  have h2m : m + m = 2 * m := by ring
  let f : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (Fin.castOrderIso h2m).toEquiv
  -- Step 1: (piCongrLeft f).symm is measure-preserving: (Fin(2m)→X) → (Fin m⊕Fin m→X)
  have step1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => X) f).symm
      (Measure.pi fun _ : Fin (2 * m) => D)
      (Measure.pi fun _ : Fin m ⊕ Fin m => D) :=
    MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : Fin (2 * m) => D) f)
  -- Step 2: sumPiEquivProdPi is measure-preserving: (Fin m⊕Fin m→X) → (Fin m→X)×(Fin m→X)
  have step2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X))
      (Measure.pi fun _ : Fin m ⊕ Fin m => D)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => D)
  -- The composition is measure-preserving
  have comp := step2.comp step1
  -- Show the composition function equals (firstHalf, secondHalf)
  have hfun : (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) =
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm := by
    funext S
    simp only [Function.comp]
    -- Simplify (piCongrLeft f).symm S to S ∘ f pointwise
    have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm S = S ∘ f := by
      funext j
      change (Equiv.piCongrLeft (fun _ => X) f).symm S j = S (f j)
      exact Equiv.piCongrLeft_symm_apply (fun _ => X) f S j
    rw [hcoe]
    -- sumPiEquivProdPi (S ∘ f) reduces to (fun i => S (f (.inl i)), fun i => S (f (.inr i)))
    -- which equals (firstHalf S, secondHalf S) since
    -- f (.inl i) = ⟨i.val,_⟩ and f (.inr i) = ⟨m+i.val,_⟩
    apply Prod.ext
    · funext i; simp only [firstHalf]; congr 1
    · funext i; simp only [secondHalf]; congr 1
  rw [hfun]
  exact comp.map_eq

/-- **Ghost Sample Lemma**: Under the iid double-sample measure,
Pr[EventA] ≤ 2 · Pr[EventB]. -/
theorem ghost_sample_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hC : Set.Countable C) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤
    2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} := by
  -- Write P₁ ⊗ P₂ for the product of two m-sample measures.
  set P := sampleMeasure D (2 * m)
  set P₁ := sampleMeasure D m
  set P₂ := sampleMeasure D m
  -- Key facts about B: B ⊆ A, and for S₁ where A holds, P₂[B(S₁,·)] ≥ 1/2.
  -- By Fubini, P[B] = ∫ S₁, P₂[B(S₁,·)] dP₁ ≥ (1/2) · P₁[A].
  -- Hence P[A] ≤ 2 · P[B].
  -- The map splitting a 2m-sample into two halves
  let f : (Fin (2 * m) → X) → (Fin m → X) × (Fin m → X) := fun S => (firstHalf S, secondHalf S)
  have hf_meas : Measurable f := by
    apply Measurable.prod
    · apply measurable_pi_lambda; intro i; exact measurable_pi_apply _
    · apply measurable_pi_lambda; intro i; exact measurable_pi_apply _
  -- Events in the product space
  let A_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1}
  let B_prod : Set ((Fin m → X) × (Fin m → X)) :=
    {p | ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
         hasManyErrors ε m h c p.2}
  -- Measurability of A_prod and B_prod via countable union (using hC : Set.Countable C)
  -- Helper: error set for any concept is measurable
  have herrSet_for : ∀ hh : Concept X, MeasurableSet {x : X | isError hh c x} := fun hh => by
    rw [show {x : X | isError hh c x} = symmDiff hh.val c.val from by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto]
    exact hh.2.symmDiff c.2
  -- Helper: consistent set for any concept is a pi-set preimage
  have hcons_pi_for : ∀ hh : Concept X,
      {S₁ : Fin m → X | isConsistentWith hh c S₁} =
      Set.pi Set.univ (fun _ => {x | isError hh c x}ᶜ) := fun hh => by
    ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff]
  have hA_meas : MeasurableSet A_prod := by
    have hA_eq : A_prod = ⋃ hh ∈ C,
        {p : (Fin m → X) × (Fin m → X) |
          isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1} := by
      change {p : (Fin m → X) × (Fin m → X) |
          ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1} = _
      ext p; simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h, hC, hbad, hcons⟩; exact ⟨h, hC, hbad, hcons⟩
      · rintro ⟨h, hC, hbad, hcons⟩; exact ⟨h, hC, hbad, hcons⟩
    rw [hA_eq]
    apply MeasurableSet.biUnion hC
    intro hh _
    by_cases hbad : isBadHypothesis D c ε hh
    · -- Bad case: set reduces to Prod.fst⁻¹(pi-set)
      have heq : {p : (Fin m → X) × (Fin m → X) |
            isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1} =
          Prod.fst ⁻¹' Set.pi Set.univ (fun _ => {x | isError hh c x}ᶜ) := by
        ext p; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff, hbad]
      rw [heq]
      exact measurable_fst (MeasurableSet.univ_pi (fun _ => (herrSet_for hh).compl))
    · -- Not-bad case: set is empty
      have heq : {p : (Fin m → X) × (Fin m → X) |
            isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1} = ∅ := by
        ext p; simp [hbad]
      rw [heq]; exact MeasurableSet.empty
  have hB_meas : MeasurableSet B_prod := by
    have hB_eq : B_prod = ⋃ hh ∈ C,
        {p : (Fin m → X) × (Fin m → X) |
          isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1 ∧
          hasManyErrors ε m hh c p.2} := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hh, hhC, hbad, hcons, hmany⟩; exact ⟨hh, hhC, hbad, hcons, hmany⟩
      · rintro ⟨hh, hhC, hbad, hcons, hmany⟩; exact ⟨hh, hhC, hbad, hcons, hmany⟩
    rw [hB_eq]
    apply MeasurableSet.biUnion hC
    intro hh _
    by_cases hbad : isBadHypothesis D c ε hh
    · -- Bad case: set = {p | consistent p.1} ∩ {p | manyErrors p.2}
      have heq : {p : (Fin m → X) × (Fin m → X) |
            isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1 ∧
            hasManyErrors ε m hh c p.2} =
          {p | isConsistentWith hh c p.1} ∩ {p | hasManyErrors ε m hh c p.2} := by
        ext p; simp [hbad]
      rw [heq]
      -- Measurability of consistent slice (preimage of pi-set under fst)
      have hcons_meas : MeasurableSet {p : (Fin m → X) × (Fin m → X) |
            isConsistentWith hh c p.1} := by
        rw [show {p : (Fin m → X) × (Fin m → X) | isConsistentWith hh c p.1} =
            Prod.fst ⁻¹' {S₁ : Fin m → X | isConsistentWith hh c S₁} from rfl,
            hcons_pi_for hh]
        exact measurable_fst (MeasurableSet.univ_pi (fun _ => (herrSet_for hh).compl))
      -- Measurability of many-errors slice (preimage of measurable set under snd)
      have hmany_meas : MeasurableSet {p : (Fin m → X) × (Fin m → X) |
            hasManyErrors ε m hh c p.2} := by
        have herrInd_meas : Measurable (fun x : X => if isError hh c x then (1:ℝ) else 0) := by
          have : (fun x : X => if isError hh c x then (1:ℝ) else 0) =
              Set.indicator {x | isError hh c x} 1 := by
            funext x; simp [Set.indicator]
          rw [this]; exact measurable_const.indicator (herrSet_for hh)
        have herr_cast_meas : Measurable (fun S₂ : Fin m → X => (errorCount hh c S₂ : ℝ)) := by
          have hcast : (fun S₂ : Fin m → X => (errorCount hh c S₂ : ℝ)) =
              fun S₂ => ∑ i : Fin m, if isError hh c (S₂ i) then (1:ℝ) else 0 := by
            funext S₂; simp [errorCount, Finset.sum_boole]
          rw [hcast]
          exact Finset.measurable_sum Finset.univ
            (fun i _ => herrInd_meas.comp (measurable_pi_apply i))
        have hmany_eq : {p : (Fin m → X) × (Fin m → X) | hasManyErrors ε m hh c p.2} =
            Prod.snd ⁻¹' {S₂ | ε * ↑m / 2 ≤ (errorCount hh c S₂ : ℝ)} := by
          ext p; simp [hasManyErrors]
        rw [hmany_eq]
        exact measurable_snd (measurableSet_le measurable_const herr_cast_meas)
      exact hcons_meas.inter hmany_meas
    · -- Not-bad case: set is empty
      have heq : {p : (Fin m → X) × (Fin m → X) |
            isBadHypothesis D c ε hh ∧ isConsistentWith hh c p.1 ∧
            hasManyErrors ε m hh c p.2} = ∅ := by
        ext p; simp [hbad]
      rw [heq]; exact MeasurableSet.empty
  -- Preimage equalities
  have hf_preimage_A : f ⁻¹' A_prod = {S | EventA C c D ε m S} := by
    ext S
    simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, f, Prod.fst,
               EventA, isBadHypothesis, isConsistentWith]
  have hf_preimage_B : f ⁻¹' B_prod = {S | EventB C c D ε m S} := by
    ext S
    simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq, f, Prod.fst, Prod.snd,
               EventB, isBadHypothesis, isConsistentWith, hasManyErrors]
  -- Pull back to product measure using sampleMeasure_eq_prod
  have hProd_eq := sampleMeasure_eq_prod D m
  have hPA : (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} = (P₁.prod P₁) A_prod := by
    rw [← hf_preimage_A, ← Measure.map_apply hf_meas hA_meas, hProd_eq]
  have hPB : (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} = (P₁.prod P₁) B_prod := by
    rw [← hf_preimage_B, ← Measure.map_apply hf_meas hB_meas, hProd_eq]
  rw [hPA, hPB]
  -- Apply Fubini (Measure.prod_apply) to both sides
  rw [Measure.prod_apply hA_meas, Measure.prod_apply hB_meas]
  -- Measurability of slice function (follows from hB_meas)
  have hB_slice_meas : Measurable (fun S₁ : Fin m → X => P₁ (Prod.mk S₁ ⁻¹' B_prod)) :=
    measurable_measure_prodMk_left hB_meas
  -- Factor constant 2 into integral
  rw [show (2 : ENNReal) * ∫⁻ S₁, P₁ (Prod.mk S₁ ⁻¹' B_prod) ∂P₁ =
          ∫⁻ S₁, 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod) ∂P₁ from
    (lintegral_const_mul 2 hB_slice_meas).symm]
  -- Pointwise comparison
  apply lintegral_mono
  intro S₁
  -- Beta-reduce the lambda-wrapped goal
  change P₁ (Prod.mk S₁ ⁻¹' A_prod) ≤ 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod)
  by_cases hS₁ : ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c S₁
  · -- S₁ is in A_half: A_prod section is all of univ
    have hAsec : Prod.mk S₁ ⁻¹' A_prod = Set.univ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_univ,
                          iff_true, Prod.fst]; exact hS₁
    rw [hAsec, measure_univ]
    -- P₁[B_prod section S₁] ≥ ENNReal.ofReal (1/2)
    have hBsec_lb : ENNReal.ofReal (1/2) ≤ P₁ (Prod.mk S₁ ⁻¹' B_prod) := by
      obtain ⟨h, hh, hbad, hcons⟩ := hS₁
      apply (bernoulli_error_lower_bound D h c m ε hε hm hm_pos hbad).trans
      apply measure_mono
      intro S₂ hS₂
      simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq, Prod.fst, Prod.snd]
      exact ⟨h, hh, hbad, hcons, hS₂⟩
    -- 1 ≤ 2 * P₁(B_prod section)
    have h12 : 2 * ENNReal.ofReal (1 / 2) = 1 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat]
      exact ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc (1 : ENNReal) = 2 * ENNReal.ofReal (1/2) := h12.symm
      _ ≤ 2 * P₁ (Prod.mk S₁ ⁻¹' B_prod) := mul_le_mul_right hBsec_lb 2
  · -- S₁ is not in A_half: A_prod section is empty
    have hAsec : Prod.mk S₁ ⁻¹' A_prod = ∅ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                          Prod.fst, iff_false]
      intro ⟨h, hh, hbad, hcons⟩; exact hS₁ ⟨h, hh, hbad, hcons⟩
    rw [hAsec, measure_empty]; exact zero_le _

end GhostSampleBound
