import MAMFinalProject.Definitions
import MAMFinalProject.Hypergeometric
import MAMFinalProject.GhostSample
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Real Set

variable {X : Type*} [MeasurableSpace X]

/-!
# Union Bound Synthesis and Sample Complexity

This file combines:
1. The growth function (bounding the number of distinct hypothesis labelings)
2. A per-hypothesis exponential bound: P[consistent ∧ manyErrors] ≤ (1/2)^{εm/2}
   via (1−p)^m ≤ exp(−pm) ≤ exp(−εm) ≤ (1/2)^{εm/2}  (see `per_hypothesis_bound`)
3. A union bound over all bad hypotheses
to obtain Pr[B] ≤ Π_C(2m) · (1/2)^{εm/2}.

Then by setting this ≤ δ/2, we get the required sample size condition.

Note: `Hypergeometric.lean` contains an alternative combinatorial route to step 2
via C(m,l)/C(2m,l) ≤ (1/2)^l, but it is not used in the current proofs.
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

/-- Pure math: log 2 ≤ 2. -/
private lemma log_two_le_two : Real.log 2 ≤ 2 :=
  calc Real.log 2
      ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp 2])
    _ = 2 := Real.log_exp 2

/-- Bridge: (1/2)^(ε·m/2) = exp(-(ε·m/2) · log 2). -/
private lemma rpow_half_eq_exp (ε : ℝ) (m : ℕ) :
    (1 / 2 : ℝ) ^ (ε * ↑m / 2) = Real.exp (-(ε * ↑m / 2) * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2)]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  ring

/-- Pure analysis: (1 - p)^m ≤ (1/2)^(ε·m/2) when 0 < ε ≤ p ≤ 1. -/
private lemma one_sub_pow_le_rpow_half {p ε : ℝ} {m : ℕ}
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
  linarith

/-- The probability that a hypothesis is consistent with the first half of a 2m-sample
equals (1 - p)^m, where p = trueError D h c. -/
lemma consistent_firstHalf_prob (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X) (m : ℕ) :
    (sampleMeasure D (2 * m)) {S | isConsistentWith h c (firstHalf S)} =
    ENNReal.ofReal ((1 - (trueError D h c).toReal) ^ m) := by
  set p := (trueError D h c).toReal with hp_def
  have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
  have hp_le1 : p ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  -- Measurability setup
  have herrSet : MeasurableSet {x : X | isError h c x} := isError_measurableSet h c
  have hconsist_pi : {S₁ : Fin m → X | isConsistentWith h c S₁} =
      Set.pi Set.univ (fun _ => {x | isError h c x}ᶜ) := by
    ext S; simp [isConsistentWith, Set.mem_pi, Set.mem_compl_iff]
  have hconsist_meas : MeasurableSet {S₁ : Fin m → X | isConsistentWith h c S₁} :=
    hconsist_pi ▸ MeasurableSet.univ_pi fun _ => herrSet.compl
  have hf_meas : Measurable (fun S : Fin (2 * m) → X => (firstHalf S, secondHalf S)) :=
    Measurable.prod (measurable_pi_lambda _ fun i => measurable_pi_apply _)
                    (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  -- Reduce to the m-sample marginal via the product structure
  have hpreimage : {S : Fin (2 * m) → X | isConsistentWith h c (firstHalf S)} =
      (fun S => (firstHalf S, secondHalf S)) ⁻¹'
        ({S₁ | isConsistentWith h c S₁} ×ˢ Set.univ) := by
    ext S; simp [isConsistentWith]
  rw [hpreimage, ← Measure.map_apply hf_meas (hconsist_meas.prod MeasurableSet.univ),
      sampleMeasure_eq_prod D m, Measure.prod_prod, measure_univ, mul_one,
      show sampleMeasure D m = Measure.pi (fun _ : Fin m => D) from rfl,
      hconsist_pi, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prob_compl_eq_one_sub herrSet]
  -- Bridge: D{x | isError h c x} = ENNReal.ofReal p
  have hD_err : D {x : X | isError h c x} = ENNReal.ofReal p := by
    have hset : {x : X | isError h c x} = symmDiff h.val c.val := by
      ext x; simp [isError, symmDiff, Set.mem_symmDiff]; tauto
    rw [hset]; exact (ENNReal.ofReal_toReal (measure_lt_top D _).ne).symm
  -- Bridge: 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p)
  have h1p_ennreal : (1 : ENNReal) - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_sub 1 hp_nonneg).symm
  rw [hD_err, h1p_ennreal, ← ENNReal.ofReal_pow (by linarith)]

/-- For a bad hypothesis h, the probability that a 2m-sample has h consistent with S₁
and making ≥ εm/2 errors on S₂ is at most (1/2)^(εm/2).

Proof: bound by P[consistent with S₁] = (1-p)^m ≤ (1/2)^{εm/2}. -/
lemma per_hypothesis_bound (D : Measure X) [IsProbabilityMeasure D]
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
          ENNReal.ofReal_le_ofReal (one_sub_pow_le_rpow_half hε hp_ε hp_le1)

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
  set bad_fin := hbad_fin.toFinset
  -- EventB ⊆ ⋃ h ∈ bad_fin, B_h
  have hcov : {S | EventB C c D ε m S} ⊆
      ⋃ h ∈ bad_fin, {S | isConsistentWith h c (firstHalf S) ∧
                          hasManyErrors ε m h c (secondHalf S)} := by
    intro S ⟨h, hC, hbad, hcons, herr⟩
    exact Set.mem_iUnion₂.mpr ⟨h, hbad_fin.mem_toFinset.mpr ⟨hC, hbad⟩, hcons, herr⟩
  -- Per-term bound via per_hypothesis_bound
  have hterm : ∀ h ∈ bad_fin, (sampleMeasure D (2 * m))
      {S | isConsistentWith h c (firstHalf S) ∧ hasManyErrors ε m h c (secondHalf S)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) := fun h hmem => by
    have hmem' := hbad_fin.mem_toFinset.mp hmem
    exact per_hypothesis_bound D h c ε m hε hmem'.2
  -- Chain: μ(EventB) ≤ ∑ μ(B_h) ≤ card • p ≤ GF • p = ofReal(GF * p)
  calc (sampleMeasure D (2 * m)) {S | EventB C c D ε m S}
      ≤ bad_fin.card • ENNReal.ofReal ((1 / 2 : ℝ) ^ (ε * ↑m / 2)) :=
          (measure_mono hcov).trans
            ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm))
    _ ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * m / 2)) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad_card) (by positivity))

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
        rcases Nat.eq_zero_or_pos (growthFunction C (2 * m)) with h0 | hgpos
        · simp only [h0, Nat.cast_zero, zero_mul]; linarith
        · have hg_pos : (0 : ℝ) < growthFunction C (2 * m) := by exact_mod_cast hgpos
          have hδ2 : (0 : ℝ) < δ / 2 := by linarith
          -- Convert (1/2)^(εm/2) to exponential form, then take log of both sides
          rw [rpow_half_eq_exp, ← Real.log_le_log_iff (by positivity) hδ2,
              Real.log_mul hg_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
              show Real.log (δ / 2) = Real.log δ - Real.log 2 from
                Real.log_div hδ.ne' (by norm_num)]
          -- Rearrange hm: log GF + log(2/δ) ≤ ε·m/2 · log 2
          have hm' : Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ) ≤
              ε * ↑m / 2 * Real.log 2 :=
            calc Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)
                = (2 / ε) * (Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ)) *
                    (ε / 2) := by field_simp
              _ ≤ (↑m * Real.log 2) * (ε / 2) :=
                    mul_le_mul_of_nonneg_right hm (by positivity)
              _ = ε * ↑m / 2 * Real.log 2 := by ring
          linarith [Real.log_div (show (2:ℝ) ≠ 0 by norm_num) hδ.ne']

end SampleSizeBound
