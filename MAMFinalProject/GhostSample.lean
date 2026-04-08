import MAMFinalProject.Definitions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

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
      (sampleMeasure D m) {S₂ : Fin m → X | hasManyErrors ε m h c S₂} := by
  -- Setup: let p = true error probability ≥ ε
  set p := (trueError D h c).toReal with hp_def
  have hp_pos : 0 < p := lt_of_lt_of_le hε hbad
  have hp_le1 : p ≤ 1 := by
    simp only [hp_def, trueError, Measure.real_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hmp_pos : 0 < (m : ℝ) * p := mul_pos hm_real hp_pos
  -- 1. Define the error indicator function
  let errInd : X → ℝ := fun x => if isError h c x then 1 else 0
  -- Measurability of error set
  have herrSet : MeasurableSet {x : X | isError h c x} := by
    have hset : {x : X | isError h c x} = symmDiff h.val c.val := by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
    rw [hset]; exact h.2.symmDiff c.2
  -- errInd is the indicator of the error set
  have herrInd_eq : errInd = Set.indicator {x : X | isError h c x} 1 := by
    funext x; simp [errInd, Set.indicator, Set.mem_setOf_eq]
  -- errInd is AEStronglyMeasurable under D
  have herrInd_aesm : AEStronglyMeasurable errInd D := by
    rw [herrInd_eq]
    exact ((measurable_const (α := X) (b := (1 : ℝ))).indicator herrSet).aestronglyMeasurable
  -- errInd is bounded in [0, 1]

  -- errInd ∈ L²(D)
  have herrInd_memlp : MemLp errInd 2 D := memLp_of_bounded herrInd_range herrInd_aesm 2
  -- 2. Mean of errInd under D is p
  have hEerrInd : ∫ x, errInd x ∂D = p := by
    rw [herrInd_eq, integral_indicator_one herrSet, measureReal_def]
    congr 1
    have : {x : X | isError h c x} = symmDiff h.val c.val := by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
    rw [this]; rfl
  -- 3. Error count as ℝ-valued sum
  let Y : (Fin m → X) → ℝ := fun S => ∑ i : Fin m, errInd (S i)
  -- Y equals errorCount cast to ℝ
  have hY_eq : ∀ S : Fin m → X, Y S = (errorCount h c S : ℝ) := fun S => by
    simp only [Y, errInd, errorCount, Finset.sum_boole, Nat.cast_id]
    push_cast; rw [Finset.sum_boole]
  -- hasManyErrors iff ε*m/2 ≤ Y
  have hMany_iff : ∀ S : Fin m → X, hasManyErrors ε m h c S ↔ ε * m / 2 ≤ Y S := fun S => by
    simp only [hasManyErrors, ← hY_eq]; constructor <;> intro h <;> exact_mod_cast h
  -- 4. Y is measurable (sum of measurable functions)
  have hY_meas : Measurable Y := by
    unfold_let Y
    apply Finset.measurable_sum; intro i _
    apply Measurable.comp _ (measurable_pi_apply i)
    rw [herrInd_eq]
    exact (measurable_const (b := (1:ℝ))).indicator herrSet
  -- Y is bounded in [0, m]
  have hY_range : ∀ᵐ S ∂(sampleMeasure D m), Y S ∈ Set.Icc 0 (m : ℝ) :=
    Filter.eventually_of_forall fun S => by
      constructor
      · apply Finset.sum_nonneg; intro i _; simp [errInd]; split_ifs <;> norm_num
      · calc Y S ≤ ∑ _ : Fin m, 1 := Finset.sum_le_sum fun i _ => by
              simp [errInd]; split_ifs <;> norm_num
          _ = m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Y ∈ L²(sampleMeasure D m)
  have hY_memlp : MemLp Y 2 (sampleMeasure D m) :=
    memLp_of_bounded hY_range hY_meas.aestronglyMeasurable 2
  -- 5. Mean of Y = m * p
  have hEY : ∫ S : Fin m → X, Y S ∂(sampleMeasure D m) = (m : ℝ) * p := by
    simp only [Y, sampleMeasure]
    rw [integral_finset_sum Finset.univ (fun i _ => ?_)]
    · simp_rw [integral_comp_eval herrInd_aesm, hEerrInd]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · exact (herrInd_memlp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).comp_measurable
              (measurable_pi_apply i)
  -- 6. Variance of errInd ≤ p (using Bhatia-Davis: Var ≤ (1-p)*p ≤ p)
  have hVarerrInd : variance errInd D ≤ p := by
    have hbd := variance_le_sub_mul_sub (μ := D) herrInd_range herrInd_aesm.aemeasurable
    rw [hEerrInd] at hbd
    simp only [sub_zero] at hbd
    calc variance errInd D ≤ (1 - p) * p := hbd
      _ ≤ 1 * p := by apply mul_le_mul_of_nonneg_right _ hp_pos.le; linarith
      _ = p := one_mul p
  -- 7. Variance of Y = m * Var[errInd] ≤ m * p
  have hVarY : variance Y (sampleMeasure D m) ≤ (m : ℝ) * p := by
    have hvsumpi : variance Y (sampleMeasure D m) = ∑ _ : Fin m, variance errInd D := by
      have := variance_sum_pi (μ := fun _ : Fin m => D) (fun _ => herrInd_memlp)
      simp only [sampleMeasure] at *
      convert this using 2
      funext S; simp [Y]
    rw [hvsumpi]
    calc ∑ _ : Fin m, variance errInd D
        ≤ ∑ _ : Fin m, p := Finset.sum_le_sum fun _ _ => hVarerrInd
      _ = (m : ℝ) * p := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 8. Apply Chebyshev with c = m*p/2
  have hc_pos : 0 < (m : ℝ) * p / 2 := by linarith
  have hCheby := meas_ge_le_variance_div_sq (μ := sampleMeasure D m) hY_memlp hc_pos
  -- Rewrite using hEY: the Chebyshev event uses E[Y] = m*p
  rw [hEY] at hCheby
  -- 9. Bound the Chebyshev probability ≤ 1/2
  have hBound : ENNReal.ofReal (variance Y (sampleMeasure D m) / ((m : ℝ) * p / 2) ^ 2) ≤
                ENNReal.ofReal (1 / 2) := by
    apply ENNReal.ofReal_le_ofReal
    have hc2 : ((m : ℝ) * p / 2) ^ 2 > 0 := sq_pos_of_pos hc_pos
    rw [div_le_div_iff hc2 (by norm_num : (0:ℝ) < 2)]
    calc variance Y (sampleMeasure D m) * 2
        ≤ (m : ℝ) * p * 2 := by linarith
      _ ≤ ((m : ℝ) * p / 2) ^ 2 * 2 := by
          -- Need: mp * 2 ≤ (mp/2)^2 * 2 ↔ mp ≤ (mp)^2/4 ↔ 4 ≤ mp
          -- But mp ≥ mε ≥ 8 * ε / ε = 8 ≥ 4. Wait, we need 4 ≤ mp.
          -- From hm: 8/ε ≤ m, so mε ≥ 8, so mp ≥ mε ≥ 8. So mp ≥ 8 > 4.
          have hmp8 : 8 ≤ (m : ℝ) * p := by
            calc 8 = 8 / ε * ε := by field_simp
              _ ≤ (m : ℝ) * ε := by apply mul_le_mul_of_nonneg_right hm hε.le
              _ ≤ (m : ℝ) * p := by apply mul_le_mul_of_nonneg_left hbad hm_real.le
          nlinarith [sq_nonneg ((m : ℝ) * p)]
  -- 10. The complement of hasManyErrors is a subset of the Chebyshev event
  have hSubset : {S : Fin m → X | ¬ hasManyErrors ε m h c S} ⊆
                 {S | (m : ℝ) * p / 2 ≤ |Y S - (m : ℝ) * p|} := by
    intro S hS
    simp only [Set.mem_setOf_eq, hMany_iff, not_le] at hS
    simp only [Set.mem_setOf_eq]
    -- Y S < ε*m/2 ≤ m*p/2 (since ε ≤ p, m ≥ 0)
    have hYS_lt : Y S < (m : ℝ) * p / 2 := by
      calc Y S < ε * (m : ℝ) / 2 := hS
        _ ≤ p * (m : ℝ) / 2 := by apply div_le_div_of_nonneg_right _ (by norm_num)
                                   apply mul_le_mul_of_nonneg_right hbad hm_real.le
        _ = (m : ℝ) * p / 2 := by ring
    -- Y S < mp, so |Y S - mp| = mp - Y S > mp/2
    have hYS_lt_mp : Y S < (m : ℝ) * p := by linarith
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  -- 11. Combine: P(¬hasManyErrors) ≤ P(Chebyshev event) ≤ 1/2
  have hPcomp : (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} ≤ ENNReal.ofReal (1 / 2) :=
    (measure_mono hSubset).trans (hCheby.trans hBound)
  -- 12. Conclude: P(hasManyErrors) ≥ 1/2 (by complement)
  have hms : MeasurableSet {S : Fin m → X | ¬ hasManyErrors ε m h c S} :=
    (hY_meas.measurableSet_le measurable_const).compl.compl.congr
      (by ext S; simp [hasManyErrors, hY_eq, ← hMany_iff]; tauto)
  -- Actually easier: use MeasurableSet of the "good" set
  have hms_good : MeasurableSet {S : Fin m → X | hasManyErrors ε m h c S} := by
    simp_rw [Set.setOf_iff_iff.mpr (fun S => hMany_iff S)]
    exact measurable_const.measurableSet_le hY_meas
  rw [← Set.compl_compl {S | hasManyErrors ε m h c S}]
  rw [prob_compl_eq_one_sub hms_good.compl]
  have h1sub : 1 - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (by norm_num : (1:ℝ)/2 ≤ 1)]
    norm_num
  have hcompl_eq : {S : Fin m → X | hasManyErrors ε m h c S}ᶜ =
                   {S | ¬ hasManyErrors ε m h c S} := Set.compl_setOf _ _
  rw [hcompl_eq]
  calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := h1sub.symm
    _ ≤ 1 - (sampleMeasure D m) {S | ¬ hasManyErrors ε m h c S} :=
        ENNReal.tsub_le_tsub_left hPcomp 1
    _ = (sampleMeasure D m) {S | hasManyErrors ε m h c S} := by
        rw [← hcompl_eq, prob_compl_eq_one_sub hms_good]
        simp [ENNReal.sub_sub_cancel]

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
    -- which equals (firstHalf S, secondHalf S) since f (.inl i) = ⟨i.val,_⟩ and f (.inr i) = ⟨m+i.val,_⟩
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
