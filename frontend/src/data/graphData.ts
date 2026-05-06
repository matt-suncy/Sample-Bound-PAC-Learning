// Single source of truth for the dependency graph.
// To update for a new Lean formalization state: edit nodes/edges here only.
// PLACEHOLDER: label, naturalLanguageStatement strings should be replaced with precise human-readable content.

export interface TheoremNodeData {
  id: string
  label: string                   // short human-readable title (PLACEHOLDER)
  naturalLanguageStatement: string // full natural language statement (PLACEHOLDER)
  leanCode: string                 // full Lean declaration
  file: string
  isHighlighted?: boolean          // main result of its file → #EEF3FF background
  isPrivate?: boolean              // private lemma → italic label
}

export interface TheoremEdge {
  source: string  // dependency (called lemma id)
  target: string  // caller (lemma that uses source)
}

// ─────────────────────────────────────────────────────────────────────────────
// NODES
// ─────────────────────────────────────────────────────────────────────────────

export const theoremNodes: TheoremNodeData[] = [

  // ── Definitions.lean ──────────────────────────────────────────────────────

  {
    id: 'firstHalf_combineHalves',
    file: 'Definitions.lean',
    label: 'First Half of Combined Sample',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Splitting a combined sample recovers the first half: firstHalf(combineHalves(S₁, S₂)) = S₁.',
    leanCode:
`@[simp]
lemma firstHalf_combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) :
    firstHalf (combineHalves S₁ S₂) = S₁ := by
  funext i
  simp only [firstHalf, combineHalves, dif_pos i.isLt]`,
  },
  {
    id: 'secondHalf_combineHalves',
    file: 'Definitions.lean',
    label: 'Second Half of Combined Sample',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Splitting a combined sample recovers the second half: secondHalf(combineHalves(S₁, S₂)) = S₂.',
    leanCode:
`@[simp]
lemma secondHalf_combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) :
    secondHalf (combineHalves S₁ S₂) = S₂ := by
  funext i
  simp only [secondHalf, combineHalves]
  have hlt : ¬ (m + i.val < m) := by omega
  rw [dif_neg hlt]
  exact congrArg S₂ (Fin.ext (by simp [Nat.add_sub_cancel_left]))`,
  },
  {
    id: 'sampleMeasure_isProbability',
    file: 'Definitions.lean',
    isHighlighted: true,
    label: 'Sample Measure is a Probability Measure',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The product measure $\\mathcal{D}^m$ is a probability measure whenever $\\mathcal{D}$ is. Required throughout since Mathlib measure-theory lemmas assume $\\texttt{IsProbabilityMeasure}$.',
    leanCode:
`instance sampleMeasure_isProbability (D : Measure X) [IsProbabilityMeasure D] (m : ℕ) :
    IsProbabilityMeasure (sampleMeasure D m) := by
  unfold sampleMeasure
  infer_instance`,
  },

  // ── GhostSample.lean — private helpers ────────────────────────────────────

  {
    id: 'isError_set_symmDiff',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Set Equals Symmetric Difference',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The set of error points for h vs c equals the symmetric difference of their underlying sets. Bridges the predicate isError with the measure-theoretic symmDiff used in trueError.',
    leanCode:
`private lemma isError_set_symmDiff (h c : Concept X) :
    {x : X | isError h c x} = symmDiff h.val c.val := by
  ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto`,
  },
  {
    id: 'errIndicator_eq_indicator',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Indicator as Set Indicator',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Rewrites errIndicator as a Set.indicator, which is the canonical Mathlib form. Needed to apply Mathlib\'s integral lemmas for indicator functions.',
    leanCode:
`private lemma errIndicator_eq_indicator (h c : Concept X) :
    errIndicator h c = Set.indicator {x | isError h c x} 1 := by
  funext x; simp [errIndicator, Set.indicator, Set.mem_setOf_eq]`,
  },
  {
    id: 'errIndicator_measurable',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Indicator is Measurable',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The error indicator function is measurable. Required for integration and for MemLp.',
    leanCode:
`private lemma errIndicator_measurable (h c : Concept X) : Measurable (errIndicator h c) := by
  rw [errIndicator_eq_indicator]
  exact measurable_const.indicator (isError_measurableSet h c)`,
  },
  {
    id: 'errIndicator_mem_Icc',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Indicator Takes Values in [0,1]',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The error indicator takes values in [0, 1]. Used to verify the boundedness condition needed for MemLp and the variance bound.',
    leanCode:
`private lemma errIndicator_mem_Icc (h c : Concept X) (x : X) :
    errIndicator h c x ∈ Set.Icc 0 1 := by
  simp [errIndicator, Set.mem_Icc]; split_ifs <;> norm_num`,
  },
  {
    id: 'errIndicator_memlp',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Indicator in L²(D)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The error indicator function is in L²(D). Required as a hypothesis for Chebyshev\'s inequality and for variance_sum_pi.',
    leanCode:
`private lemma errIndicator_memlp (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) :
    MemLp (errIndicator h c) 2 D :=
  memLp_of_bounded (Filter.Eventually.of_forall (errIndicator_mem_Icc h c))
    (errIndicator_measurable h c).aestronglyMeasurable 2`,
  },
  {
    id: 'errIndicator_integral',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Expectation of Error Indicator = True Error',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The expectation of the error indicator under D equals the true error probability. Connects the mean of the error sum to trueError.',
    leanCode:
`private lemma errIndicator_integral (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) :
    ∫ x, errIndicator h c x ∂D = (trueError D h c).toReal := by
  rw [errIndicator_eq_indicator, integral_indicator_one (isError_measurableSet h c),
      measureReal_def, isError_set_symmDiff]
  rfl`,
  },
  {
    id: 'errIndicator_variance_le',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Variance of Error Indicator ≤ True Error',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The variance of the error indicator is at most the true error probability p. Uses Bernoulli(p) variance = p(1-p) ≤ p.',
    leanCode:
`private lemma errIndicator_variance_le (D : Measure X) [IsProbabilityMeasure D]
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
    _ = p := one_mul p`,
  },
  {
    id: 'errIndicator_integrable_coord',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Indicator Integrable at Each Coordinate',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The function S ↦ errIndicator(S(i)) is integrable under D^m. Needed to swap the sum and integral in errorSum_integral.',
    leanCode:
`private lemma errIndicator_integrable_coord (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) (i : Fin m) :
    Integrable (fun S : Fin m → X => errIndicator h c (S i))
      (Measure.pi (fun _ : Fin m => D)) := by
  have hmemlp : MemLp (fun S : Fin m → X => errIndicator h c (S i)) 2
      (Measure.pi (fun _ : Fin m => D)) :=
    memLp_of_bounded
      (Filter.Eventually.of_forall fun (S : Fin m → X) => errIndicator_mem_Icc h c (S i))
      ((errIndicator_measurable h c).comp (measurable_pi_apply i)).aestronglyMeasurable
      2
  exact hmemlp.integrable (by norm_num)`,
  },
  {
    id: 'errorSum_range',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Sum in [0, m]',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The sum of error indicators over a sample lies in [0, m] for any sample S. This range bound is the key input to memLp_of_bounded.',
    leanCode:
`private lemma errorSum_range (h c : Concept X) (m : ℕ) (S : Fin m → X) :
    ∑ i : Fin m, errIndicator h c (S i) ∈ Set.Icc 0 (m : ℝ) := by
  refine ⟨Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · simp [errIndicator]; split_ifs <;> norm_num
  · calc ∑ i : Fin m, errIndicator h c (S i)
          ≤ ∑ _ : Fin m, 1 :=
            Finset.sum_le_sum fun i _ => by simp [errIndicator]; split_ifs <;> norm_num
        _ = (m : ℝ) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]`,
  },
  {
    id: 'errorSum_memlp',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Error Sum in L²(D^m)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The error sum S ↦ Σᵢ errIndicator(S(i)) is in L²(D^m). The main measurability certificate required to apply Chebyshev\'s inequality.',
    leanCode:
`private lemma errorSum_memlp (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X) (m : ℕ) :
    MemLp (fun S : Fin m → X => ∑ i : Fin m, errIndicator h c (S i)) 2 (sampleMeasure D m) :=
  memLp_of_bounded
    (Filter.Eventually.of_forall (errorSum_range h c m))
    (Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i)).aestronglyMeasurable
    2`,
  },
  {
    id: 'hasManyErrors_iff_errorSum',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Many Errors ↔ Error Sum ≥ εm/2',
    // PLACEHOLDER:
    naturalLanguageStatement: 'hasManyErrors holds for S iff the error indicator sum reaches εm/2. Bridges the domain predicate and the numeric sum for Chebyshev.',
    leanCode:
`private lemma hasManyErrors_iff_errorSum (h c : Concept X) (m : ℕ) (ε : ℝ) (S : Fin m → X) :
    hasManyErrors ε m h c S ↔ ε * ↑m / 2 ≤ ∑ i : Fin m, errIndicator h c (S i) := by
  simp [hasManyErrors, errIndicator, errorCount, Finset.sum_boole]`,
  },
  {
    id: 'errorSum_integral',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Expected Error Count = m·p',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The expected number of errors under D^m is m·p, where p = trueError. Used as the mean in the Chebyshev bound.',
    leanCode:
`private lemma errorSum_integral (D : Measure X) [IsProbabilityMeasure D]
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
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`,
  },
  {
    id: 'errorSum_variance_le',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Variance of Error Sum ≤ m·p',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The variance of the error sum under D^m is at most m·p. Uses independence of coordinates via variance_sum_pi. Together with the mean, gives control over the Chebyshev ratio.',
    leanCode:
`private lemma errorSum_variance_le (D : Measure X) [IsProbabilityMeasure D]
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
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`,
  },
  {
    id: 'many_errors_measurableSet',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Many-Errors Event is Measurable',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The event {S | hasManyErrors} is measurable. Required when computing its complement probability and applying prob_compl_eq_one_sub.',
    leanCode:
`private lemma many_errors_measurableSet (h c : Concept X) (m : ℕ) (ε : ℝ) :
    MeasurableSet {S : Fin m → X | hasManyErrors ε m h c S} := by
  rw [show {S : Fin m → X | hasManyErrors ε m h c S} =
          {S | ε * ↑m / 2 ≤ ∑ i : Fin m, errIndicator h c (S i)} from
        Set.ext fun S => hasManyErrors_iff_errorSum h c m ε S]
  exact measurableSet_le measurable_const
    (Finset.measurable_sum Finset.univ fun i _ =>
      (errIndicator_measurable h c).comp (measurable_pi_apply i))`,
  },
  {
    id: 'mp_le_half_mp_div2_sq',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'μ ≤ (1/2)(μ/2)² when μ ≥ 8',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Pure algebra: if μ ≥ 8 then μ ≤ (1/2)(μ/2)². This is the algebraic inequality that makes the Chebyshev ratio Var/(μ/2)² collapse to ≤ 1/2.',
    leanCode:
`private lemma mp_le_half_mp_div2_sq {mp : ℝ} (h : 8 ≤ mp) : mp ≤ 1 / 2 * (mp / 2) ^ 2 := by
  nlinarith [sq_nonneg mp]`,
  },
  {
    id: 'eight_le_mul_of_div_le',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: '8 ≤ m·p when 8/ε ≤ m and ε ≤ p',
    // PLACEHOLDER:
    naturalLanguageStatement: 'If 8/ε ≤ m, ε ≤ p, and m > 0, then 8 ≤ m·p. Converts the sample-size hypothesis into the mp ≥ 8 form needed by var_div_sq_le_half.',
    leanCode:
`private lemma eight_le_mul_of_div_le {ε p m : ℝ} (hε : 0 < ε) (hm : 8 / ε ≤ m)
    (hp : ε ≤ p) (hm_pos : 0 < m) : 8 ≤ m * p :=
  calc 8 = 8 / ε * ε := by field_simp
    _ ≤ m * ε := mul_le_mul_of_nonneg_right hm hε.le
    _ ≤ m * p := mul_le_mul_of_nonneg_left hp hm_pos.le`,
  },
  {
    id: 'var_div_sq_le_half',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Var/(μ/2)² ≤ 1/2',
    // PLACEHOLDER:
    naturalLanguageStatement: 'If Var ≤ μ and 8 ≤ μ, then Var/(μ/2)² ≤ 1/2. The crux of the Chebyshev argument — shows the probability of a large deviation is at most 1/2.',
    leanCode:
`private lemma var_div_sq_le_half {var μ : ℝ} (hvar : var ≤ μ) (hμ8 : 8 ≤ μ) :
    var / (μ / 2) ^ 2 ≤ 1 / 2 := by
  rw [div_le_iff₀ (sq_pos_of_pos (by linarith))]
  linarith [mp_le_half_mp_div2_sq hμ8]`,
  },
  {
    id: 'one_sub_ofReal_half',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: '1 − ofReal(1/2) = ofReal(1/2)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'ENNReal arithmetic: 1 − ofReal(1/2) = ofReal(1/2). Used to flip between "complement ≤ 1/2" and "event ≥ 1/2".',
    leanCode:
`private lemma one_sub_ofReal_half :
    (1 : ENNReal) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num`,
  },
  {
    id: 'notManyErrors_subset_chebyshev_dev',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: '¬ManyErrors ⊆ Chebyshev Large-Deviation Event',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Any sample failing the many-errors threshold has its error sum far below the mean, placing it inside the Chebyshev large-deviation set. This inclusion lets us bound P(¬hasManyErrors) via Chebyshev.',
    leanCode:
`private lemma notManyErrors_subset_chebyshev_dev (h c : Concept X) (m : ℕ) (ε p : ℝ)
    (hm_real : 0 < (m : ℝ)) (hp_pos : 0 < p) (hbad : ε ≤ p) :
    {S : Fin m → X | ¬ hasManyErrors ε m h c S} ⊆
    {S | (m : ℝ) * p / 2 ≤ |∑ i : Fin m, errIndicator h c (S i) - (m : ℝ) * p|} := by
  intro S hS
  simp only [Set.mem_setOf_eq, hasManyErrors_iff_errorSum, not_le] at hS
  have hYlt : ∑ i : Fin m, errIndicator h c (S i) < (m : ℝ) * p / 2 :=
    calc ∑ i : Fin m, errIndicator h c (S i) < ε * ↑m / 2 := hS
      _ ≤ p * ↑m / 2 := by linarith [mul_le_mul_of_nonneg_right hbad hm_real.le]
      _ = (m : ℝ) * p / 2 := by ring
  simp only [Set.mem_setOf_eq,
    abs_of_neg (show ∑ i : Fin m, errIndicator h c (S i) - (m : ℝ) * p < 0 by
      linarith [mul_pos hm_real hp_pos])]
  linarith`,
  },
  {
    id: 'prob_ge_half_of_compl_le_half',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'P(Eᶜ) ≤ 1/2 → P(E) ≥ 1/2',
    // PLACEHOLDER:
    naturalLanguageStatement: 'In any probability space, if P(Eᶜ) ≤ 1/2 then P(E) ≥ 1/2. The final flip that converts an upper bound on the complement into the lower bound we want.',
    leanCode:
`private lemma prob_ge_half_of_compl_le_half {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {E : Set α} (hms : MeasurableSet E)
    (h : μ Eᶜ ≤ ENNReal.ofReal (1 / 2)) : ENNReal.ofReal (1 / 2) ≤ μ E := by
  have hμE : μ E = 1 - μ Eᶜ := by
    rw [prob_compl_eq_one_sub hms, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [hμE]
  calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := one_sub_ofReal_half.symm
    _ ≤ 1 - μ Eᶜ := tsub_le_tsub_left h 1`,
  },
  {
    id: 'consistent_set_eq_pi',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Consistent Set as Product Set',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The set of samples consistent with h is a pi-set (product set): each coordinate must lie outside the error set. This form is what Mathlib needs to compute its measure as a product.',
    leanCode:
`private lemma consistent_set_eq_pi (hh c : Concept X) (m : ℕ) :
    {S₁ : Fin m → X | isConsistentWith hh c S₁} =
    Set.pi Set.univ (fun _ => {x | isError hh c x}ᶜ) := by
  ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff]`,
  },
  {
    id: 'A_prod_measurable',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Event A (Product Space) is Measurable',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The product-space version of Event A is measurable. Required to apply Fubini (via Measure.prod_apply) and to form the slice measures.',
    leanCode:
`private lemma A_prod_measurable (C : Set (Concept X)) (c : Concept X)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (hC : Set.Countable C) :
    MeasurableSet {p : (Fin m → X) × (Fin m → X) |
      ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1} := by
  -- union over countably many h ∈ C; each slice is a measurable pi-set preimage
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
  · simp [hbad]`,
  },
  {
    id: 'B_prod_measurable',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: 'Event B (Product Space) is Measurable',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The product-space version of Event B is measurable. Same role as A_prod_measurable — required for Fubini and slice measures.',
    leanCode:
`private lemma B_prod_measurable (C : Set (Concept X)) (c : Concept X)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (hC : Set.Countable C) :
    MeasurableSet {p : (Fin m → X) × (Fin m → X) |
      ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
               hasManyErrors ε m h c p.2} := by
  -- analogous to A_prod_measurable; each slice is intersection of pi-set and many-errors set
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
    have hcons_meas : MeasurableSet
        {p : (Fin m → X) × (Fin m → X) | isConsistentWith hh c p.1} := by
      rw [show {p : (Fin m → X) × (Fin m → X) | isConsistentWith hh c p.1} =
              Prod.fst ⁻¹' {S₁ | isConsistentWith hh c S₁} from rfl,
          consistent_set_eq_pi]
      exact measurable_fst (MeasurableSet.univ_pi (fun _ => (isError_measurableSet hh c).compl))
    exact hcons_meas.inter (measurable_snd (many_errors_measurableSet hh c m ε))
  · simp [hbad]`,
  },
  {
    id: 'two_mul_ofReal_half',
    file: 'GhostSample.lean',
    isPrivate: true,
    label: '2 · ofReal(1/2) = 1',
    // PLACEHOLDER:
    naturalLanguageStatement: 'ENNReal arithmetic: 2 · ofReal(1/2) = 1. Used to convert the lower bound P(B-slice) ≥ 1/2 into 1 ≤ 2·P(B-slice) in the final pointwise comparison.',
    leanCode:
`private lemma two_mul_ofReal_half : (2 : ENNReal) * ENNReal.ofReal (1 / 2) = 1 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  exact ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top`,
  },

  // ── GhostSample.lean — public ──────────────────────────────────────────────

  {
    id: 'isError_measurableSet',
    file: 'GhostSample.lean',
    label: 'Error Set is Measurable',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The set of error points {x | isError h c x} is measurable. Required any time we take its measure or integrate over it.',
    leanCode:
`lemma isError_measurableSet (h c : Concept X) : MeasurableSet {x : X | isError h c x} :=
  isError_set_symmDiff h c ▸ h.2.symmDiff c.2`,
  },
/*   {
    id: 'error_indicator_mean_ge',
    file: 'GhostSample.lean',
    label: 'Error Indicator Mean ≥ ε for Bad Hypotheses',
    // PLACEHOLDER:
    naturalLanguageStatement: 'For a bad hypothesis h (true error ≥ ε), the probability of an error at a random point is at least ε. A sanity lemma bridging isBadHypothesis and the error set measure.',
    leanCode:
`lemma error_indicator_mean_ge (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (ε : ℝ) (hε : ε > 0)
    (hbad : ε ≤ (trueError D h c).toReal) :
    ε ≤ (D {x | isError h c x}).toReal := by
  rw [isError_set_symmDiff]; exact hbad`,
  }, */
  {
    id: 'bernoulli_error_lower_bound',
    file: 'GhostSample.lean',
    isHighlighted: true,
    label: 'Bernoulli Error Lower Bound',
    // PLACEHOLDER:
    naturalLanguageStatement: 'For a bad hypothesis $h$ with $\\mathrm{error}_{\\mathcal{D}}(h,c) \\geq \\varepsilon$ and sample size $m \\geq 8/\\varepsilon$, a fresh $m$-point i.i.d. sample contains at least $\\varepsilon m/2$ errors with probability at least $1/2$. Proved via Chebyshev applied to $m$ i.i.d. Bernoulli$(p)$ variables. This is needed to show that $\\Pr[A] \\leq 2 \\cdot \\Pr[B]$.',
    leanCode:
`set_option maxHeartbeats 800000 in
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
  have hmp8 : 8 ≤ (m : ℝ) * p := eight_le_mul_of_div_le hε hm hbad hm_real
  let Y : (Fin m → X) → ℝ := fun S => ∑ i : Fin m, errIndicator h c (S i)
  have hEY : ∫ S : Fin m → X, Y S ∂(sampleMeasure D m) = (m : ℝ) * p :=
    errorSum_integral D h c m
  have hVarY : variance Y (sampleMeasure D m) ≤ (m : ℝ) * p :=
    errorSum_variance_le D h c m
  have hCheby := meas_ge_le_variance_div_sq (μ := sampleMeasure D m)
    (errorSum_memlp D h c m) (show 0 < (m : ℝ) * p / 2 by linarith)
  rw [hEY] at hCheby
  have hBound : ENNReal.ofReal (variance Y (sampleMeasure D m) / ((m : ℝ) * p / 2) ^ 2) ≤
                ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal (var_div_sq_le_half hVarY hmp8)
  have hPcomp : (sampleMeasure D m) {S | hasManyErrors ε m h c S}ᶜ ≤ ENNReal.ofReal (1 / 2) := by
    apply (measure_mono _).trans (hCheby.trans hBound)
    rw [show {S : Fin m → X | hasManyErrors ε m h c S}ᶜ =
            {S | ¬ hasManyErrors ε m h c S} from by ext; simp]
    exact notManyErrors_subset_chebyshev_dev h c m ε p hm_real hp_pos hbad
  exact prob_ge_half_of_compl_le_half (many_errors_measurableSet h c m ε) hPcomp`,
  },
  {
    id: 'sampleMeasure_eq_prod',
    file: 'GhostSample.lean',
    label: '2m-Sample Measure = Product of Two m-Sample Measures',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The push-forward of the 2m-sample measure along the half-split map equals D^m ⊗ D^m. The measure-theoretic fact that allows treating the two halves as independent.',
    leanCode:
`lemma sampleMeasure_eq_prod (D : Measure X) [IsProbabilityMeasure D] (m : ℕ) :
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
  exact (step2.comp step1).map_eq`,
  },
  {
    id: 'event_prob_eq_prod',
    file: 'GhostSample.lean',
    label: 'Event Probability via Product Measure',
    // PLACEHOLDER:
    naturalLanguageStatement: 'For any measurable product-space event E, the 2m-sample probability of {S | (firstHalf S, secondHalf S) ∈ E} equals (D^m ⊗ D^m)(E). A convenience corollary of sampleMeasure_eq_prod.',
    leanCode:
`lemma event_prob_eq_prod (D : Measure X) [IsProbabilityMeasure D] (m : ℕ)
    {E : Set ((Fin m → X) × (Fin m → X))} (hE : MeasurableSet E) :
    (sampleMeasure D (2 * m)) {S | (firstHalf S, secondHalf S) ∈ E} =
    ((sampleMeasure D m).prod (sampleMeasure D m)) E := by
  have hf_meas : Measurable (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) :=
    Measurable.prod (measurable_pi_lambda _ fun i => measurable_pi_apply _)
                    (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  rw [show {S : Fin (2 * m) → X | (firstHalf S, secondHalf S) ∈ E} =
          (fun S => (firstHalf S, secondHalf S)) ⁻¹' E from rfl,
      ← Measure.map_apply hf_meas hE, sampleMeasure_eq_prod D m]`,
  },
  {
    id: 'ghost_sample_bound',
    file: 'GhostSample.lean',
    isHighlighted: true,
    label: 'Ghost Sample Lemma: Pr[A] ≤ 2·Pr[B]',
    // PLACEHOLDER:
    naturalLanguageStatement: '$\\Pr[A] \\leq 2\\Pr[B]$: the probability that some bad $h \\in \\mathcal{C}$ is consistent with the first-half sample $S_1$ is at most twice the probability that it also makes $\\geq \\varepsilon m/2$ errors on the ghost half $S_2$. This theorem bounds $\\Pr[A]$ in terms of $\\Pr[B]$ which then allows us to apply the bound on $\\Pr[B]$ in terms of $\\delta$.',
    leanCode:
`theorem ghost_sample_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ)
    (hε : ε > 0) (hm : 8 / ε ≤ (m : ℝ)) (hm_pos : 0 < m)
    (hC : Set.Countable C) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤
    2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} := by
  -- translate events to product space, apply Fubini, use bernoulli_error_lower_bound
  let A_prod := {p : (Fin m → X) × (Fin m → X) |
    ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1}
  let B_prod := {p : (Fin m → X) × (Fin m → X) |
    ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c p.1 ∧
             hasManyErrors ε m h c p.2}
  have hA_meas : MeasurableSet A_prod := A_prod_measurable C c D ε m hC
  have hB_meas : MeasurableSet B_prod := B_prod_measurable C c D ε m hC
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
  rw [hPA, hPB, Measure.prod_apply hA_meas, Measure.prod_apply hB_meas,
      ← lintegral_const_mul 2 (measurable_measure_prodMk_left hB_meas)]
  apply lintegral_mono; intro S₁
  by_cases hS₁ : ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c S₁
  · have hAsec : Prod.mk S₁ ⁻¹' A_prod = Set.univ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hS₁
    rw [hAsec, measure_univ]
    obtain ⟨h, hh, hbad, hcons⟩ := hS₁
    have hBsec_lb : ENNReal.ofReal (1 / 2) ≤
        (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod) :=
      (bernoulli_error_lower_bound D h c m ε hε hm hm_pos hbad).trans
        (measure_mono fun S₂ hS₂ => by
          simp only [Set.mem_preimage, B_prod, Set.mem_setOf_eq]
          exact ⟨h, hh, hbad, hcons, hS₂⟩)
    calc (1 : ENNReal) = 2 * ENNReal.ofReal (1 / 2) := two_mul_ofReal_half.symm
      _ ≤ 2 * (sampleMeasure D m) (Prod.mk S₁ ⁻¹' B_prod) := mul_le_mul_right hBsec_lb 2
  · have hAsec : Prod.mk S₁ ⁻¹' A_prod = ∅ := by
      ext S₂; simp only [Set.mem_preimage, A_prod, Set.mem_setOf_eq,
                          Set.mem_empty_iff_false, iff_false]
      exact fun ⟨h, hh, hbad, hcons⟩ => hS₁ ⟨h, hh, hbad, hcons⟩
    rw [hAsec, measure_empty]; exact zero_le _`,
  },
  {
    id: 'eventB_implies_eventA',
    file: 'GhostSample.lean',
    label: 'Event B Implies Event A',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Event B (bad hypothesis consistent with S₁ and making many errors on S₂) implies Event A (bad hypothesis consistent with S₁). Immediate from the definitions.',
    leanCode:
`lemma eventB_implies_eventA (C : Set (Concept X)) (c : Concept X) (D : Measure X)
    [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X)
    (hB : EventB C c D ε m S) : EventA C c D ε m S := by
  obtain ⟨h, hh, hbad, hcons, _⟩ := hB
  exact ⟨h, hh, hbad, hcons⟩`,
  },

  // ── Hypergeometric.lean — private ─────────────────────────────────────────

  {
    id: 'two_mul_sub_le',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: '2(m−l) ≤ 2m−l',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Pure natural number arithmetic: 2(m−l) ≤ 2m−l for l ≤ m. Needed in the inductive step to ensure the combinatorial ratio moves in the right direction.',
    leanCode:
`private lemma two_mul_sub_le (m l : ℕ) (hl : l ≤ m) : 2 * (m - l) ≤ 2 * m - l := by omega`,
  },
  {
    id: 'hypergeometric_bound_nat_succ',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: 'Hypergeometric Bound Inductive Step',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Inductive step: if 2^l · C(m,l) ≤ C(2m,l) then 2^(l+1) · C(m,l+1) ≤ C(2m,l+1). Uses Pascal-type recurrences for binomial coefficients.',
    leanCode:
`private lemma hypergeometric_bound_nat_succ (m l : ℕ) (hl : l ≤ m)
    (ih : 2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l) :
    2 ^ (l + 1) * Nat.choose m (l + 1) ≤ Nat.choose (2 * m) (l + 1) := by
  rw [pow_succ]
  suffices h : 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1) ≤
               Nat.choose (2 * m) (l + 1) * (l + 1) from
    Nat.le_of_mul_le_mul_right h (Nat.succ_pos l)
  have hm := Nat.choose_succ_right_eq m l
  have h2m := Nat.choose_succ_right_eq (2 * m) l
  calc 2 ^ l * 2 * Nat.choose m (l + 1) * (l + 1)
      = 2 ^ l * Nat.choose m l * (2 * (m - l)) := by rw [hm]; ring
    _ ≤ Nat.choose (2 * m) l * (2 * (m - l)) := by gcongr
    _ ≤ Nat.choose (2 * m) l * (2 * m - l) := by gcongr; exact two_mul_sub_le m l hl
    _ = Nat.choose (2 * m) (l + 1) * (l + 1) := by rw [← h2m]`,
  },
  {
    id: 'hypergeometric_bound_nat',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: 'Hypergeometric Bound (ℕ)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Full induction: 2^l · C(m,l) ≤ C(2m,l) for all l ≤ m. The core combinatorial inequality underlying the hypergeometric bound.',
    leanCode:
`private lemma hypergeometric_bound_nat : ∀ (m l : ℕ), l ≤ m →
    2 ^ l * Nat.choose m l ≤ Nat.choose (2 * m) l := by
  intro m l hl
  induction l with
  | zero => simp
  | succ l ih =>
    exact hypergeometric_bound_nat_succ m l (Nat.le_of_succ_le hl) (ih (Nat.le_of_succ_le hl))`,
  },
  {
    id: 'hypergeometric_bound_cast',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: 'Hypergeometric Bound Cast to ℝ',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Casts the core ℕ inequality to ℝ. A routine but necessary type-coercion step before performing real division.',
    leanCode:
`private lemma hypergeometric_bound_cast (m l : ℕ) (hl : l ≤ m) :
    (2 : ℝ) ^ l * (Nat.choose m l : ℝ) ≤ (Nat.choose (2 * m) l : ℝ) :=
  by exact_mod_cast hypergeometric_bound_nat m l hl`,
  },
  {
    id: 'choose_2m_pos',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: 'C(2m, l) > 0',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The binomial coefficient C(2m, l) is positive in ℝ when l ≤ m. Needed to safely divide by C(2m, l) in hypergeometric_bound.',
    leanCode:
`private lemma choose_2m_pos (m l : ℕ) (hl : l ≤ m) :
    (0 : ℝ) < (Nat.choose (2 * m) l : ℝ) :=
  Nat.cast_pos.mpr (Nat.choose_pos (by omega))`,
  },
  {
    id: 'half_pow_mul_two_pow',
    file: 'Hypergeometric.lean',
    isPrivate: true,
    label: '(1/2)^l · 2^l = 1',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The algebraic identity (1/2)^l · 2^l = 1 in ℝ. Used to rewrite the combinatorial inequality into the ratio form C(m,l)/C(2m,l) ≤ (1/2)^l.',
    leanCode:
`private lemma half_pow_mul_two_pow (l : ℕ) :
    (1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l = 1 := by
  rw [← mul_pow]; norm_num`,
  },

  // ── Hypergeometric.lean — public ──────────────────────────────────────────

  {
    id: 'hypergeometric_bound',
    file: 'Hypergeometric.lean',
    isHighlighted: true,
    label: 'Hypergeometric Bound: C(m,l)/C(2m,l) ≤ (1/2)^l',
    // PLACEHOLDER:
    naturalLanguageStatement: '$\\binom{m}{l}/\\binom{2m}{l} \\leq (1/2)^l$ for $l \\leq m$. A uniform random split of $2m$ points places all $l$ errors in the second half with probability at most $(1/2)^l$. (This file is imported but not used in the current main proof chain.)',
    leanCode:
`lemma hypergeometric_bound (m l : ℕ) (hl : l ≤ m) :
    (Nat.choose m l : ℝ) / (Nat.choose (2 * m) l : ℝ) ≤ (1 / 2) ^ l := by
  apply div_le_of_le_mul₀ (choose_2m_pos m l hl).le (by positivity)
  calc (Nat.choose m l : ℝ)
      = (1 / 2 : ℝ) ^ l * (2 : ℝ) ^ l * (Nat.choose m l : ℝ) := by
          rw [half_pow_mul_two_pow]; ring
    _ = (1 / 2 : ℝ) ^ l * ((2 : ℝ) ^ l * (Nat.choose m l : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ l * (Nat.choose (2 * m) l : ℝ) :=
        mul_le_mul_of_nonneg_left (hypergeometric_bound_cast m l hl) (by positivity)`,
  },

  // ── Symmetrization.lean — private ─────────────────────────────────────────

  {
    id: 'log_two_le_two',
    file: 'Symmetrization.lean',
    isPrivate: true,
    label: 'log 2 ≤ 2',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Pure analysis: log 2 ≤ 2. Needed in one_sub_pow_le_rpow_half to convert the exp(−εm) bound into the (1/2)^(εm/2) form.',
    leanCode:
`private lemma log_two_le_two : Real.log 2 ≤ 2 :=
  calc Real.log 2
      ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp 2])
    _ = 2 := Real.log_exp 2`,
  },
  {
    id: 'rpow_half_eq_exp',
    file: 'Symmetrization.lean',
    isPrivate: true,
    label: '(1/2)^(εm/2) = exp(−(εm/2)·log 2)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Bridge: (1/2)^(εm/2) = exp(−(εm/2)·log 2). Connects the probabilistic expression (1/2)^(εm/2) with the exponential form needed in the sample size algebra.',
    leanCode:
`private lemma rpow_half_eq_exp (ε : ℝ) (m : ℕ) :
    (1 / 2 : ℝ) ^ (ε * ↑m / 2) = Real.exp (-(ε * ↑m / 2) * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2)]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  ring`,
  },
  {
    id: 'one_sub_pow_le_rpow_half',
    file: 'Symmetrization.lean',
    isPrivate: true,
    label: '(1−p)^m ≤ (1/2)^(εm/2)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The key analytic bound: (1−p)^m ≤ (1/2)^(εm/2) when 0 < ε ≤ p ≤ 1. Chains three steps: (1−p)^m ≤ exp(−pm), exp(−pm) ≤ exp(−εm) (since p ≥ ε), exp(−εm) ≤ (1/2)^(εm/2) (since log 2 ≤ 2).',
    leanCode:
`private lemma one_sub_pow_le_rpow_half {p ε : ℝ} {m : ℕ}
    (hε : 0 < ε) (hp_ε : ε ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ m ≤ (1 / 2 : ℝ) ^ (ε * ↑m / 2) := by
  have h1p : 0 ≤ 1 - p := by linarith
  have hstep1 : (1 - p) ^ m ≤ Real.exp (-(p * m)) :=
    calc (1 - p) ^ m
        ≤ Real.exp (-p) ^ m :=
            pow_le_pow_left₀ h1p (by linarith [Real.one_sub_le_exp_neg p]) m
      _ = Real.exp (-(p * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hstep2 : Real.exp (-(p * m)) ≤ Real.exp (-(ε * m)) := by
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right hp_ε (Nat.cast_nonneg m)]
  have hstep3 : Real.exp (-(ε * m)) ≤ (1 / 2 : ℝ) ^ (ε * ↑m / 2) := by
    rw [rpow_half_eq_exp]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg m), log_two_le_two]
  linarith`,
  },

  // ── Symmetrization.lean — public ──────────────────────────────────────────

  {
    id: 'card_labelings_le_growthFunction',
    file: 'Symmetrization.lean',
    label: 'Labelings on Any Sample ≤ Growth Function',
    // PLACEHOLDER:
    naturalLanguageStatement: 'For any fixed sample S of size m, the number of distinct labelings of S by C is at most growthFunction C m. Justifies the definition by confirming the supremum is an upper bound.',
    leanCode:
`lemma card_labelings_le_growthFunction
    (C : Set (Concept X)) (m : ℕ) (S : Fin m → X) :
    Nat.card (Set.range fun h : C => restrictToSample h.val S) ≤ growthFunction C m := by
  apply le_ciSup_of_le _ S le_rfl
  refine ⟨2 ^ m, ?_⟩
  rintro x ⟨T, rfl⟩
  calc Nat.card (Set.range fun h : C => restrictToSample h.val T)
      ≤ Nat.card (Set.univ : Set (Finset (Fin m))) :=
          Nat.card_mono Set.finite_univ (Set.subset_univ _)
    _ = 2 ^ m := by
        rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]`,
  },
  {
    id: 'growthFunction_le_two_pow',
    file: 'Symmetrization.lean',
    label: 'Growth Function ≤ 2^m',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The growth function satisfies growthFunction C m ≤ 2^m. A trivial upper bound confirming the supremum in the definition is finite.',
    leanCode:
`lemma growthFunction_le_two_pow (C : Set (Concept X)) (m : ℕ) :
    growthFunction C m ≤ 2 ^ m := by
  unfold growthFunction
  rcases isEmpty_or_nonempty (Fin m → X) with hE | hNE
  · haveI := hE; rw [ciSup_of_empty]; exact Nat.zero_le _
  · apply ciSup_le; intro S
    calc Nat.card (Set.range fun h : C => restrictToSample h.val S)
        ≤ Nat.card (Set.univ : Set (Finset (Fin m))) :=
            Nat.card_mono Set.finite_univ (Set.subset_univ _)
      _ = 2 ^ m := by
          rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]`,
  },
  {
    id: 'consistent_firstHalf_prob',
    file: 'Symmetrization.lean',
    label: 'Consistency Probability = (1−p)^m',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The probability that hypothesis h is consistent with the first half of a 2m-sample equals (1−p)^m, where p = trueError. Computed via the product structure of the measure and independence across coordinates.',
    leanCode:
`lemma consistent_firstHalf_prob (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) :
    (sampleMeasure D (2 * m)) {S | isConsistentWith h c (firstHalf S)} =
    ENNReal.ofReal ((1 - (trueError D h c).toReal) ^ m) := by
  set p := (trueError D h c).toReal with hp_def
  have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
  have hp_le1 : p ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  have herrSet : MeasurableSet {x : X | isError h c x} := isError_measurableSet h c
  have hconsist_pi : {S₁ : Fin m → X | isConsistentWith h c S₁} =
      Set.pi Set.univ (fun _ => {x | isError h c x}ᶜ) := by
    ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff]
  have hconsist_meas : MeasurableSet {S₁ : Fin m → X | isConsistentWith h c S₁} :=
    hconsist_pi ▸ MeasurableSet.univ_pi fun _ => herrSet.compl
  rw [show {S : Fin (2 * m) → X | isConsistentWith h c (firstHalf S)} =
          (fun S => (firstHalf S, secondHalf S)) ⁻¹'
            ({S₁ | isConsistentWith h c S₁} ×ˢ Set.univ) from by
        ext S; simp [isConsistentWith],
      ← Measure.map_apply
          (Measurable.prod (measurable_pi_lambda _ fun i => measurable_pi_apply _)
                           (measurable_pi_lambda _ fun i => measurable_pi_apply _))
          (hconsist_meas.prod MeasurableSet.univ),
      sampleMeasure_eq_prod D m, Measure.prod_prod, measure_univ, mul_one,
      show sampleMeasure D m = Measure.pi (fun _ : Fin m => D) from rfl,
      hconsist_pi, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prob_compl_eq_one_sub herrSet]
  have hD_err : D {x : X | isError h c x} = ENNReal.ofReal p := by
    have hset : {x : X | isError h c x} = symmDiff h.val c.val := by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
    rw [hset]; exact (ENNReal.ofReal_toReal (measure_lt_top D _).ne).symm
  have h1p_ennreal : (1 : ENNReal) - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_sub 1 hp_nonneg).symm
  rw [hD_err, h1p_ennreal, ← ENNReal.ofReal_pow (by linarith)]`,
  },
  {
    id: 'per_hypothesis_bound',
    file: 'Symmetrization.lean',
    label: 'Per-Hypothesis Probability ≤ (1/2)^(εm/2)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'For any bad hypothesis h, the probability that a 2m-sample has h consistent with the first half AND making many errors on the second half is at most (1/2)^(εm/2). The per-hypothesis contribution to the union bound.',
    leanCode:
`lemma per_hypothesis_bound (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (ε : ℝ) (m : ℕ) (hε : ε > 0) (hbad : isBadHypothesis D c ε h) :
    (sampleMeasure D (2 * m))
        {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)} ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) := by
  have hp_ε : ε ≤ (trueError D h c).toReal := hbad
  have hp_le1 : (trueError D h c).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  calc (sampleMeasure D (2 * m))
          {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)}
      ≤ (sampleMeasure D (2 * m)) {S | isConsistentWith h c (firstHalf S)} :=
          measure_mono Set.inter_subset_left
    _ = ENNReal.ofReal ((1 - (trueError D h c).toReal) ^ m) :=
          consistent_firstHalf_prob D h c m
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) :=
          ENNReal.ofReal_le_ofReal (one_sub_pow_le_rpow_half hε hp_ε hp_le1)`,
  },
  {
    id: 'symmetrization_bound',
    file: 'Symmetrization.lean',
    isHighlighted: true,
    label: 'Symmetrization Bound: Pr[B] ≤ Π_C(2m) · (1/2)^(εm/2)',
    // PLACEHOLDER:
    naturalLanguageStatement: '$\\Pr[B] \\leq \\Pi_{\\mathcal{C}}(2m) \\cdot (1/2)^{\\varepsilon m/2}$, where $\\Pi_{\\mathcal{C}}(2m)$ is the growth function. The union bound over at most $\\Pi_{\\mathcal{C}}(2m)$ distinct labelings, each bounded by $(1/2)^{\\varepsilon m/2}$ via per_hypothesis_bound. This theorem is a union bound applied on the per_hypothesis_bound over all possible labelings (the growth function).',
    leanCode:
`theorem symmetrization_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (hε : ε > 0)
    (hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h})
    (hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m)) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤
    ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) := by
  set bad_fin := hbad_fin.toFinset
  have hcov : {S | EventB C c D ε m S} ⊆
      ⋃ h ∈ bad_fin, {S | isConsistentWith h c (firstHalf S) ∧
                          hasManyErrors ε m h c (secondHalf S)} := by
    intro S ⟨h, hC, hbad, hcons, herr⟩
    exact Set.mem_iUnion₂.mpr ⟨h, hbad_fin.mem_toFinset.mpr ⟨hC, hbad⟩, hcons, herr⟩
  have hterm : ∀ h ∈ bad_fin, (sampleMeasure D (2 * m))
      {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) := fun h hmem => by
    have hmem' := hbad_fin.mem_toFinset.mp hmem
    exact per_hypothesis_bound D h c ε m hε hmem'.2
  calc (sampleMeasure D (2 * m)) {S | EventB C c D ε m S}
      ≤ bad_fin.card • ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) :=
          (measure_mono hcov).trans
            ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm))
    _ ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad_card) (by positivity))`,
  },
  {
    id: 'sample_size_bound',
    file: 'Symmetrization.lean',
    isHighlighted: true,
    label: 'Sample Size Bound: Pr[B] ≤ δ/2',
    // PLACEHOLDER:
    naturalLanguageStatement: 'If $\\frac{2}{\\varepsilon}\\!\\left(\\log\\Pi_{\\mathcal{C}}(2m) + \\log\\frac{2}{\\delta}\\right) \\leq m\\log 2$, then $\\Pr[B] \\leq \\delta/2$. Obtained by taking logarithms of the symmetrization bound and rearranging. This theorem inserts the minimum number of samples needed to ensure Event B occurs with a low probability. This a precise way to say that a hypothesis that is consistent with $m$ samples is very unlikely to be bad.',
    leanCode:
`theorem sample_size_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε δ : ℝ) (m : ℕ)
    (hε : ε > 0) (hδ : δ > 0)
    (hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h})
    (hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m))
    (hm : (2 / ε) * (Real.log (growthFunction C (2 * m)) + Real.log (2 / δ)) ≤
          m * Real.log 2) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤ ENNReal.ofReal (δ / 2) := by
  calc (sampleMeasure D (2 * m)) {S | EventB C c D ε m S}
      ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) :=
          symmetrization_bound C c D ε m hε hbad_fin hbad_card
    _ ≤ ENNReal.ofReal (δ / 2) := by
        apply ENNReal.ofReal_le_ofReal
        rcases Nat.eq_zero_or_pos (growthFunction C (2 * m)) with h0 | hgpos
        · simp only [h0, Nat.cast_zero, zero_mul]; linarith
        · have hg_pos : (0 : ℝ) < growthFunction C (2 * m) := by exact_mod_cast hgpos
          have hδ2 : (0 : ℝ) < δ / 2 := by linarith
          rw [rpow_half_eq_exp, ← Real.log_le_log_iff (by positivity) hδ2,
              Real.log_mul hg_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
              show Real.log (δ / 2) = Real.log δ - Real.log 2 from
                Real.log_div hδ.ne' (by norm_num)]
          have hm' : Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ) ≤
              ε * ↑m / 2 * Real.log 2 :=
            calc Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)
                = (2 / ε) * (Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)) *
                    (ε / 2) := by field_simp
              _ ≤ (↑m * Real.log 2) * (ε / 2) :=
                    mul_le_mul_of_nonneg_right hm (by positivity)
              _ = ε * ↑m / 2 * Real.log 2 := by ring
          linarith [Real.log_div (show (2:ℝ) ≠ 0 by norm_num) hδ.ne']`,
  },

  // ── Main.lean — private ───────────────────────────────────────────────────

  {
    id: 'rpow_exp_div_form',
    file: 'Main.lean',
    isPrivate: true,
    label: '(exp(1)·n/d)^d = exp(d)/(d/n)^d',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Bridge: (exp(1)·n/d)^d = exp(d)/(d/n)^d. Converts the RHS of sum_choose_le_pow\'s goal into a form amenable to the le_div_iff step, avoiding repeated inline algebra.',
    leanCode:
`private lemma rpow_exp_div_form (n d : ℕ) (r : ℝ)
    (hn : (0 : ℝ) < n) (hd : (0 : ℝ) < d) (hr : r = d / n) :
    (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d = Real.exp (d : ℝ) / r ^ d := by
  have hexp_d : Real.exp 1 ^ d = Real.exp (d : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hr, div_pow, mul_pow, hexp_d, div_pow]; field_simp`,
  },
  {
    id: 'm_pos_of_size_condition',
    file: 'Main.lean',
    isPrivate: true,
    label: 'm > 0 from Size Condition',
    // PLACEHOLDER:
    naturalLanguageStatement: 'If 8/ε ≤ m and ε > 0 then m > 0. A positivity side-goal factored out to keep the main theorem clean.',
    leanCode:
`private lemma m_pos_of_size_condition {ε : ℝ} {m : ℕ} (hε : 0 < ε) (hm : 8 / ε ≤ (m : ℝ)) :
    0 < m := by
  have : 0 < 8 / ε := by positivity
  exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hm; linarith)`,
  },
  {
    id: 'one_le_two_exp_mul_div',
    file: 'Main.lean',
    isPrivate: true,
    label: '1 ≤ 2·exp(1)·m/d',
    // PLACEHOLDER:
    naturalLanguageStatement: '1 ≤ 2·exp(1)·m/d when d ≤ 2m and m ≥ 1. Needed when the growth function is zero to show d·log(2em/d) ≥ 0.',
    leanCode:
`private lemma one_le_two_exp_mul_div (m d : ℕ) (hd : 0 < d) (hmd : d ≤ 2 * m)
    (hm_pos : 0 < m) : 1 ≤ 2 * Real.exp 1 * (m : ℝ) / (d : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  simp only [one_mul]
  calc (d : ℝ) ≤ 2 * m := by exact_mod_cast hmd
    _ ≤ 2 * Real.exp 1 * m := by nlinarith [Real.one_le_exp zero_le_one]`,
  },
  {
    id: 'log_growthFunction_le_sauerShelah',
    file: 'Main.lean',
    isPrivate: true,
    label: 'log Π_C(2m) ≤ d·log(2em/d)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The log of the growth function is bounded by d·log(2em/d). Converts the polynomial Sauer-Shelah bound into the logarithmic form required by sample_size_bound.',
    leanCode:
`private lemma log_growthFunction_le_sauerShelah (C : Set (Concept X)) (m d : ℕ)
    (hd : 0 < d) (hVC : VC_dim C ≤ d) (hmd : d ≤ 2 * m) (hm_pos : 0 < m)
    (h_vcDim_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d) :
    Real.log (growthFunction C (2 * m) : ℝ) ≤ ↑d * Real.log (2 * Real.exp 1 * ↑m / ↑d) := by
  have hg := sauer_shelah_bound C m d hd hVC hmd h_vcDim_elem
  rcases Nat.eq_zero_or_pos (growthFunction C (2 * m)) with h0 | hpos
  · simp only [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (one_le_two_exp_mul_div m d hd hmd hm_pos))
  · rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hpos) hg`,
  },
  {
    id: 'two_mul_ofReal_div2',
    file: 'Main.lean',
    isPrivate: true,
    label: '2 · ofReal(δ/2) = ofReal(δ)',
    // PLACEHOLDER:
    naturalLanguageStatement: 'ENNReal bridge: 2 · ofReal(δ/2) = ofReal(δ) for δ ≥ 0. The final arithmetic step that collapses 2·(δ/2) back to δ.',
    leanCode:
`private lemma two_mul_ofReal_div2 {δ : ℝ} (hδ : 0 ≤ δ) :
    (2 : ENNReal) * ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1; ring`,
  },

  // ── Main.lean — public ────────────────────────────────────────────────────

  {
    id: 'card_restrictionFamily_eq',
    file: 'Main.lean',
    label: 'Restriction Family Cardinality Equals Labeling Count',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The cardinality of the restriction family at sample S equals the number of distinct labelings of S by C. A routine conversion between Finset.card and Nat.card needed for Sauer-Shelah.',
    leanCode:
`lemma card_restrictionFamily_eq
    (C : Set (Concept X)) {m : ℕ} (S : Fin m → X) :
    (restrictionFamily C S).card = Nat.card (Set.range fun h : C => restrictToSample h.val S) := by
  simp [restrictionFamily]`,
  },
  {
    id: 'growthFunction_le_sauerShelah_sum',
    file: 'Main.lean',
    label: 'Growth Function ≤ Sauer-Shelah Sum',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The growth function satisfies growthFunction C m ≤ Σ_{k ≤ d} C(m,k) when VC_dim C ≤ d. The key step connecting VC dimension to a concrete polynomial bound, via Mathlib\'s Finset.card_shatterer_le_sum_vcDim.',
    leanCode:
`theorem growthFunction_le_sauerShelah_sum
    (C : Set (Concept X)) (m : ℕ) (d : ℕ) (hd : VC_dim C ≤ d)
    (h_vcDim_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d) :
    growthFunction C m ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
  apply ciSup_le'
  intro S
  rw [show Nat.card (Set.range fun h : C => restrictToSample h.val S) =
      (restrictionFamily C S).card from by rw [card_restrictionFamily_eq]]
  calc (restrictionFamily C S).card
      ≤ (restrictionFamily C S).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (restrictionFamily C S).vcDim, (Fintype.card (Fin m)).choose k :=
        Finset.card_shatterer_le_sum_vcDim (𝒜 := restrictionFamily C S) (α := Fin m)
    _ ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
        simp only [Fintype.card_fin]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Iic_subset_Iic.mpr (h_vcDim_elem m S)
        · intros; positivity`,
  },
  {
    id: 'sum_choose_le_pow',
    file: 'Main.lean',
    label: 'Binomial Sum ≤ (en/d)^d',
    // PLACEHOLDER:
    naturalLanguageStatement: 'The standard inequality Σ_{k≤d} C(n,k) ≤ (e·n/d)^d. Proved by setting r = d/n, bounding the partial sum by the full binomial sum (1+r)^n, then using 1+r ≤ exp(r).',
    leanCode:
`lemma sum_choose_le_pow (n d : ℕ) (hd : 0 < d) (hnd : d ≤ n) :
    (∑ k ∈ Finset.Iic d, Nat.choose n k : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le hd hnd
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdn : (d : ℝ) ≤ n := Nat.cast_le.mpr hnd
  set r : ℝ := d / n with hr_def
  have hr0 : 0 < r := div_pos hd' hn
  have hr1 : r ≤ 1 := (div_le_one hn).mpr hdn
  have hr_pow_pos : 0 < r ^ d := pow_pos hr0 d
  rw [rpow_exp_div_form n d r hn hd' hr_def, le_div_iff₀ hr_pow_pos]
  calc (∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ)) * r ^ d
      = ∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ) * r ^ d := Finset.sum_mul _ _ _
    _ ≤ ∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ) * r ^ k := by
          apply Finset.sum_le_sum; intro k hk
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr0.le hr1 (Finset.mem_Iic.mp hk))
            (Nat.cast_nonneg _)
    _ ≤ ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * r ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_Iic] at hk; simp only [Finset.mem_range]; omega
          · intros; positivity
    _ = (r + 1) ^ n := by
          symm; rw [add_pow]
          apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ Real.exp (d : ℝ) := by
          calc (r + 1) ^ n
              ≤ (Real.exp r) ^ n :=
                  pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp r) n
            _ = Real.exp (d : ℝ) := by
                  rw [← Real.exp_nat_mul]; congr 1; rw [hr_def]; field_simp`,
  },
  {
    id: 'sauer_shelah_bound',
    file: 'Main.lean',
    isHighlighted: true,
    label: 'Sauer-Shelah Bound: Π_C(2m) ≤ (2em/d)^d',
    // PLACEHOLDER:
    naturalLanguageStatement: '$\\Pi_{\\mathcal{C}}(2m) \\leq \\left(\\frac{2em}{d}\\right)^d$ where $d = \\mathrm{VCdim}(\\mathcal{C})$. The growth function is at most polynomial in $m$, enabling the final probability bound. This motivates the whole proof because we can achieve a polynomial bound on the number of samples based on the VC dimension.',
    leanCode:
`theorem sauer_shelah_bound (C : Set (Concept X)) (m d : ℕ)
    (hd : 0 < d) (hVC : VC_dim C ≤ d) (hmd : d ≤ 2 * m)
    (h_vcDim_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d) :
    (growthFunction C (2 * m) : ℝ) ≤ (2 * Real.exp 1 * m / d) ^ d := by
  have hss := growthFunction_le_sauerShelah_sum C (2 * m) d hVC h_vcDim_elem
  calc (growthFunction C (2 * m) : ℝ)
      ≤ ∑ k ∈ Finset.Iic d, Nat.choose (2 * m) k := by exact_mod_cast hss
    _ ≤ (Real.exp 1 * (2 * m) / d) ^ d := by
        have h := sum_choose_le_pow (2 * m) d hd hmd; push_cast at h ⊢; exact h
    _ = (2 * Real.exp 1 * m / d) ^ d := by ring`,
  },
  {
    id: 'pac_sample_complexity_bound',
    file: 'Main.lean',
    isHighlighted: true,
    label: 'PAC Sample Complexity Bound',
    // PLACEHOLDER:
    naturalLanguageStatement: 'Fix any concept class $\\mathcal{C}$, fix any distribution $\\mathcal{D}$, any target concept $c\\in\\mathcal{C}$: given a dataset of $m \\geq 8/\\varepsilon$, $m \\geq \\frac{2}{\\varepsilon}\\!\\left(d\\log\\frac{2em}{d}+\\log\\frac{2}{\\delta}\\right)$ samples, then for any $\\varepsilon$ and $\\delta$, the probability all bad hypotheses $h\\in\\mathcal{C}$ are inconsistent with the dataset is at least $1-\\delta$. More formally: $\\Pr_{S\\sim\\mathcal{D}^{2m}}[\\exists h\\in\\mathcal{C}: \\mathrm{error}(h)\\geq\\varepsilon,\\ h\\text{ consistent with }S_1]\\leq\\delta$.',
    leanCode:
`theorem pac_sample_complexity_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε δ : ℝ) (m d : ℕ)
    (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ < 1)
    (hd : 0 < d) (hVC : VC_dim C ≤ d)
    (hmd : d ≤ 2 * m)
    (hm_size : 8 / ε ≤ (m : ℝ))
    (hC : Set.Countable C)
    (hVC_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d)
    (hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h})
    (hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m))
    (hm : (2 / ε) * (d * Real.log (2 * Real.exp 1 * m / d) + Real.log (2 / δ)) ≤
          m * Real.log 2) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤ ENNReal.ofReal δ := by
  have hm_pos : 0 < m := m_pos_of_size_condition hε hm_size
  calc (sampleMeasure D (2 * m)) {S | EventA C c D ε m S}
      ≤ 2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} :=
          ghost_sample_bound C c D ε m hε hm_size hm_pos hC
    _ ≤ 2 * ENNReal.ofReal (δ / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sample_size_bound C c D ε δ m hε hδ hbad_fin hbad_card
          calc (2 / ε) * (Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ))
              ≤ (2 / ε) * (↑d * Real.log (2 * Real.exp 1 * ↑m / ↑d) + Real.log (2 / δ)) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    gcongr
                    exact log_growthFunction_le_sauerShelah C m d hd hVC hmd hm_pos hVC_elem
            _ ≤ m * Real.log 2 := hm
    _ = ENNReal.ofReal δ := two_mul_ofReal_div2 hδ.le`,
  },
]

// ─────────────────────────────────────────────────────────────────────────────
// EDGES  (source = dependency/called, target = caller)
// Arrows point from source (lower) to target (higher) in the BT layout.
// ─────────────────────────────────────────────────────────────────────────────

export const theoremEdges: TheoremEdge[] = [
  // isError_set_symmDiff is the base for measurability and integral bridges
  { source: 'isError_set_symmDiff', target: 'isError_measurableSet' },
  { source: 'isError_set_symmDiff', target: 'errIndicator_integral' },
  //{ source: 'isError_set_symmDiff', target: 'error_indicator_mean_ge' },

  // errIndicator infrastructure
  { source: 'errIndicator_eq_indicator', target: 'errIndicator_measurable' },
  { source: 'errIndicator_eq_indicator', target: 'errIndicator_integral' },
  { source: 'isError_measurableSet',     target: 'errIndicator_measurable' },
  { source: 'isError_measurableSet',     target: 'errIndicator_integral' },
  { source: 'errIndicator_measurable',   target: 'errIndicator_memlp' },
  { source: 'errIndicator_measurable',   target: 'errIndicator_integrable_coord' },
  { source: 'errIndicator_measurable',   target: 'errorSum_memlp' },
  { source: 'errIndicator_measurable',   target: 'many_errors_measurableSet' },
  { source: 'errIndicator_measurable',   target: 'errIndicator_variance_le' },
  { source: 'errIndicator_measurable',   target: 'errorSum_integral' },
  { source: 'errIndicator_mem_Icc',      target: 'errIndicator_memlp' },
  { source: 'errIndicator_mem_Icc',      target: 'errIndicator_integrable_coord' },
  { source: 'errIndicator_mem_Icc',      target: 'errIndicator_variance_le' },
  { source: 'errIndicator_integral',     target: 'errIndicator_variance_le' },
  { source: 'errIndicator_integral',     target: 'errorSum_integral' },
  { source: 'errIndicator_integrable_coord', target: 'errorSum_integral' },
  { source: 'errIndicator_variance_le',  target: 'errorSum_variance_le' },
  { source: 'errIndicator_memlp',        target: 'errorSum_variance_le' },
  { source: 'errorSum_range',            target: 'errorSum_memlp' },

  // hasManyErrors bridge
  { source: 'hasManyErrors_iff_errorSum', target: 'notManyErrors_subset_chebyshev_dev' },
  { source: 'hasManyErrors_iff_errorSum', target: 'many_errors_measurableSet' },

  // Pure-math helpers for Chebyshev
  { source: 'mp_le_half_mp_div2_sq',            target: 'var_div_sq_le_half' },
  { source: 'one_sub_ofReal_half',               target: 'prob_ge_half_of_compl_le_half' },

  // bernoulli_error_lower_bound aggregates all the above
  { source: 'errorSum_integral',                 target: 'bernoulli_error_lower_bound' },
  { source: 'errorSum_variance_le',              target: 'bernoulli_error_lower_bound' },
  { source: 'errorSum_memlp',                    target: 'bernoulli_error_lower_bound' },
  { source: 'many_errors_measurableSet',         target: 'bernoulli_error_lower_bound' },
  { source: 'eight_le_mul_of_div_le',            target: 'bernoulli_error_lower_bound' },
  { source: 'var_div_sq_le_half',                target: 'bernoulli_error_lower_bound' },
  { source: 'notManyErrors_subset_chebyshev_dev',target: 'bernoulli_error_lower_bound' },
  { source: 'prob_ge_half_of_compl_le_half',     target: 'bernoulli_error_lower_bound' },

  // ghost_sample_bound dependencies
  { source: 'isError_measurableSet',    target: 'A_prod_measurable' },
  { source: 'isError_measurableSet',    target: 'B_prod_measurable' },
  { source: 'consistent_set_eq_pi',    target: 'A_prod_measurable' },
  { source: 'consistent_set_eq_pi',    target: 'B_prod_measurable' },
  { source: 'many_errors_measurableSet',target: 'B_prod_measurable' },
  { source: 'sampleMeasure_eq_prod',   target: 'event_prob_eq_prod' },
  { source: 'bernoulli_error_lower_bound', target: 'ghost_sample_bound' },
  { source: 'event_prob_eq_prod',      target: 'ghost_sample_bound' },
  { source: 'A_prod_measurable',       target: 'ghost_sample_bound' },
  { source: 'B_prod_measurable',       target: 'ghost_sample_bound' },
  { source: 'two_mul_ofReal_half',     target: 'ghost_sample_bound' },

  // Hypergeometric chain (standalone — not connected to main proof)
  { source: 'two_mul_sub_le',                   target: 'hypergeometric_bound_nat_succ' },
  { source: 'hypergeometric_bound_nat_succ',    target: 'hypergeometric_bound_nat' },
  { source: 'hypergeometric_bound_nat',         target: 'hypergeometric_bound_cast' },
  { source: 'hypergeometric_bound_cast',        target: 'hypergeometric_bound' },
  { source: 'choose_2m_pos',                    target: 'hypergeometric_bound' },
  { source: 'half_pow_mul_two_pow',             target: 'hypergeometric_bound' },

  // Symmetrization chain
  { source: 'isError_measurableSet',   target: 'consistent_firstHalf_prob' },
  { source: 'sampleMeasure_eq_prod',   target: 'consistent_firstHalf_prob' },
  { source: 'log_two_le_two',          target: 'one_sub_pow_le_rpow_half' },
  { source: 'rpow_half_eq_exp',        target: 'one_sub_pow_le_rpow_half' },
  { source: 'rpow_half_eq_exp',        target: 'sample_size_bound' },
  { source: 'consistent_firstHalf_prob',   target: 'per_hypothesis_bound' },
  { source: 'one_sub_pow_le_rpow_half',    target: 'per_hypothesis_bound' },
  { source: 'per_hypothesis_bound',        target: 'symmetrization_bound' },
  { source: 'symmetrization_bound',        target: 'sample_size_bound' },

  // Main.lean chain
  { source: 'rpow_exp_div_form',             target: 'sum_choose_le_pow' },
  { source: 'card_restrictionFamily_eq',     target: 'growthFunction_le_sauerShelah_sum' },
  { source: 'sum_choose_le_pow',             target: 'sauer_shelah_bound' },
  { source: 'growthFunction_le_sauerShelah_sum', target: 'sauer_shelah_bound' },
  { source: 'sauer_shelah_bound',            target: 'log_growthFunction_le_sauerShelah' },
  { source: 'one_le_two_exp_mul_div',        target: 'log_growthFunction_le_sauerShelah' },
  { source: 'log_growthFunction_le_sauerShelah', target: 'pac_sample_complexity_bound' },
  { source: 'm_pos_of_size_condition',       target: 'pac_sample_complexity_bound' },
  { source: 'ghost_sample_bound',            target: 'pac_sample_complexity_bound' },
  { source: 'sample_size_bound',             target: 'pac_sample_complexity_bound' },
  { source: 'two_mul_ofReal_div2',           target: 'pac_sample_complexity_bound' },
]
