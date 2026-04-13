import MAMFinalProject.Definitions
import MAMFinalProject.Hypergeometric
import MAMFinalProject.GhostSample
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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
hypergeometric term.

Hypotheses `hbad_fin` and `hbad_card` express the core VC-theoretic content of the union bound:
the number of "effective" bad hypotheses (those that can witness EventB) is at most the growth
function. For a finite concept class this follows directly; for infinite C a full proof would
require a measurable-selection / disintegration argument. -/
theorem symmetrization_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (hε : ε > 0)
    (hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h})
    (hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m)) :
    (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤
    ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) := by
  -- STEP 1: For each bad h ∈ C, the B_h event (consistent with S₁ AND many errors on S₂)
  -- has probability ≤ (1/2)^{εm/2}. Proof:
  --   P[B_h] ≤ P[consistent] = (1-p)^m ≤ exp(-pm) ≤ exp(-εm) ≤ (1/2)^{εm/2}
  -- where p = trueError ≥ ε and the last step uses log 2 ≤ 2.
  have per_h_bound : ∀ h : Concept X, h ∈ C → isBadHypothesis D c ε h →
      (sampleMeasure D (2 * m))
        {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * (m : ℝ) / 2)) := by
    intro h _ hbad
    set p := (trueError D h c).toReal with hp_def
    have hp_ε : ε ≤ p := hbad
    have hp_pos : 0 < p := lt_of_lt_of_le hε hp_ε
    have hp_le1 : p ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
    -- P[consistent ∧ many errors] ≤ P[consistent]
    apply (measure_mono Set.inter_subset_left).trans
    -- P[consistent with first half] = (1-p)^m in ENNReal
    -- (Uses sampleMeasure_eq_prod + Measure.prod_prod + Measure.pi_pi + complement)
    have hconsist_bound :
        (sampleMeasure D (2 * m)) {S | isConsistentWith h c (firstHalf S)} =
        ENNReal.ofReal ((1 - p) ^ m) := by
      -- Measurability of the error set
      have herrSet : MeasurableSet {x : X | isError h c x} := by
        rw [show {x : X | isError h c x} = symmDiff h.val c.val from by
          ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto]
        exact h.2.symmDiff c.2
      -- The consistent set equals Set.pi univ (complement of error set)
      have hconsist_pi : {S₁ : Fin m → X | isConsistentWith h c S₁} =
          Set.pi Set.univ (fun _ => {x | isError h c x}ᶜ) := by
        ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff, Set.mem_setOf_eq]
      -- Measurability of the consistent-S₁ set
      have hconsist_meas : MeasurableSet {S₁ : Fin m → X | isConsistentWith h c S₁} :=
        hconsist_pi ▸ MeasurableSet.univ_pi (fun _ => herrSet.compl)
      -- Measurability of splitting map
      have hf_meas : Measurable (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) :=
        Measurable.prod (measurable_pi_lambda _ fun i => measurable_pi_apply _)
                        (measurable_pi_lambda _ fun i => measurable_pi_apply _)
      -- Preimage equality: consistent-S₁ event = f⁻¹(A ×ˢ univ)
      have hconsist_preimage :
          {S : Fin (2 * m) → X | isConsistentWith h c (firstHalf S)} =
          (fun S => (firstHalf S, secondHalf S)) ⁻¹' ({S₁ | isConsistentWith h c S₁} ×ˢ Set.univ) := by
        ext S; simp [isConsistentWith]
      -- Reduce to P₁ using sampleMeasure_eq_prod + prod_prod
      rw [hconsist_preimage,
          ← Measure.map_apply hf_meas (hconsist_meas.prod MeasurableSet.univ),
          sampleMeasure_eq_prod D m, Measure.prod_prod, measure_univ, mul_one]
      -- Compute P₁ {S₁ | consistent} = ∏ i, D{x|¬error} = (1-p)^m
      rw [show sampleMeasure D m = Measure.pi (fun _ : Fin m => D) from rfl,
          hconsist_pi, Measure.pi_pi,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          prob_compl_eq_one_sub herrSet]
      -- D {x | isError} = trueError D h c = ENNReal.ofReal p
      have hD_err : D {x : X | isError h c x} = ENNReal.ofReal p := by
        have hset_eq : {x : X | isError h c x} = symmDiff h.val c.val := by
          ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
        rw [hset_eq]
        exact (ENNReal.ofReal_toReal (measure_lt_top D _).ne).symm
      rw [hD_err]
      -- 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p)
      have h1p_ennreal : (1 : ENNReal) - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_sub 1 hp_pos.le).symm
      rw [h1p_ennreal, ← ENNReal.ofReal_pow (by linarith)]
    apply hconsist_bound.le.trans
    -- (1-p)^m ≤ (1/2)^{εm/2} via exp bound
    apply ENNReal.ofReal_le_ofReal
    have h1p : 0 ≤ 1 - p := by linarith
    -- Use log 2 ≤ 2 (since 2 ≤ exp 2 by add_one_le_exp)
    have hlog2_le2 : Real.log 2 ≤ 2 :=
      calc Real.log 2
          ≤ Real.log (Real.exp 2) :=
            Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp 2])
        _ = 2 := Real.log_exp 2
    -- (1-p)^m ≤ exp(-pm): from 1 - x ≤ exp(-x) applied m times
    have hstep1 : (1 - p) ^ m ≤ Real.exp (-(p * m)) := by
      calc (1 - p) ^ m
          ≤ Real.exp (-p) ^ m :=
            pow_le_pow_left₀ h1p (by linarith [Real.one_sub_le_exp_neg p]) m
        _ = Real.exp (-(p * m)) := by rw [← Real.exp_nat_mul]; ring_nf
    -- exp(-pm) ≤ exp(-εm): since p ≥ ε
    have hstep2 : Real.exp (-(p * m)) ≤ Real.exp (-(ε * m)) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith [mul_le_mul_of_nonneg_right hp_ε this]
    -- exp(-εm) ≤ (1/2)^{εm/2}: since -εm ≤ -(εm/2)·log2 (as log 2 ≤ 2)
    have hstep3 : Real.exp (-(ε * m)) ≤ (1 / 2 : ℝ) ^ (ε * (m : ℝ) / 2) := by
      rw [show (1/2 : ℝ) ^ (ε * ↑m / 2) = Real.exp (-(ε * ↑m / 2) * Real.log 2) from by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2)]
        congr 1
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
        ring]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [mul_nonneg hε.le this]
    linarith
  -- STEP 2: Union bound over bad hypotheses.
  -- EventB ⊆ ⋃ h ∈ bad_fin, B_h where bad_fin is the finite set of bad hypotheses.
  -- P[EventB] ≤ ∑ h ∈ bad_fin, P[B_h]           (measure_biUnion_finset_le)
  --          ≤ bad_fin.card · (1/2)^{εm/2}        (Finset.sum_le_card_nsmul + per_h_bound)
  --          ≤ growthFunction · (1/2)^{εm/2}       (hbad_card)
  set bad_fin := hbad_fin.toFinset
  -- EventB ⊆ ⋃ h ∈ bad_fin, B_h
  have hcov : {S | EventB C c D ε m S} ⊆
      ⋃ h ∈ bad_fin, {S | isConsistentWith h c (firstHalf S) ∧
                          hasManyErrors ε m h c (secondHalf S)} := by
    intro S ⟨h, hC, hbad, hcons, herr⟩
    exact Set.mem_iUnion₂.mpr ⟨h, hbad_fin.mem_toFinset.mpr ⟨hC, hbad⟩, hcons, herr⟩
  -- per-term bound for each h ∈ bad_fin
  have hterm : ∀ h ∈ bad_fin, (sampleMeasure D (2 * m))
      {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) := fun h hmem => by
    have hmem' := hbad_fin.mem_toFinset.mp hmem
    exact per_h_bound h hmem'.1 hmem'.2
  -- Chain: μ(EventB) ≤ ∑ μ(B_h) ≤ card • p ≤ GF • p = ofReal(GF * p)
  have hchain : (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} ≤
      bad_fin.card • ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) :=
    (measure_mono hcov).trans
      ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm))
  apply hchain.trans
  -- bad_fin.card • ofReal p ≤ ofReal (GF * p)
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast hbad_card

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
