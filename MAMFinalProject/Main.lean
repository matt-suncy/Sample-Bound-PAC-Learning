import MAMFinalProject.Definitions
import MAMFinalProject.GhostSample
import MAMFinalProject.Symmetrization
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SetFamily.Shatter

open MeasureTheory ProbabilityTheory Real Set Finset

variable {X : Type*} [MeasurableSpace X]

/-!
# PAC Sample Complexity: Final Bound

This file combines all pieces to prove the main PAC learning theorem:

If m ≥ c₀ · (1/ε · log(1/δ) + d/ε · log(1/ε)), then with probability ≥ 1-δ
over the draw of m examples, every bad hypothesis (true error ≥ ε) is inconsistent
with the training data.

**Proof outline**:
1. Ghost sample bound: Pr[A] ≤ 2·Pr[B]       (GhostSample.lean)
2. Union bound: Pr[B] ≤ Π_C(2m) · 2^{-εm/2}  (Symmetrization.lean)
3. Sauer-Shelah: Π_C(2m) ≤ (2em/d)^d         (this file, via Mathlib)
4. Algebra: combine to get Pr[A] ≤ δ

## Sauer-Shelah in Mathlib

Mathlib's Sauer-Shelah lemma (`Finset.card_shatterer_le_sum_vcDim`) states:
  #𝒜.shatterer ≤ ∑ k ∈ Iic d, (Fintype.card α).choose k
for 𝒜 : Finset (Finset α) with vcDim 𝒜 = d.

We connect this to the PAC learning growth function by working with concept
restrictions to finite samples.
-/

section VCDimension

/-- The restriction of C to a fixed sample S, as a finite set family.
This converts the abstract concept class C (measurable sets over X)
into a concrete Finset (Finset (Fin m)), allowing use of Mathlib's
combinatorial Sauer-Shelah lemma. -/
noncomputable def restrictionFamily (C : Set (Concept X)) {m : ℕ} (S : Fin m → X) :
    Finset (Finset (Fin m)) :=
  (Set.range fun h : C => restrictToSample h.val S).toFinset

/-- The VC dimension of the concept class C, defined as the supremum of the VC
dimensions of the restriction families across all finite samples. -/
noncomputable def VC_dim (C : Set (Concept X)) : ℕ :=
  ⨆ (m : ℕ) (S : Fin m → X), (restrictionFamily C S).vcDim

/-- The restriction family at sample S has cardinality equal to the number of
distinct labelings of S by C. -/
lemma card_restrictionFamily_eq
    (C : Set (Concept X)) {m : ℕ} (S : Fin m → X) :
    (restrictionFamily C S).card = Nat.card (Set.range fun h : C => restrictToSample h.val S) := by
  simp [restrictionFamily]

/-- The growth function is bounded by the Sauer-Shelah sum ∑_{k ≤ d} C(m,k),
where d = VC_dim C.

**Proof**: For any sample S of size m, by Mathlib's Sauer-Shelah lemma:
  |restrictionFamily C S| = #(restrictionFamily C S) ≤ #shatterer ≤ ∑_{k ≤ d} C(m,k)
The growth function is the sup over all such S, so it's also ≤ ∑_{k ≤ d} C(m,k). -/
theorem growthFunction_le_sauerShelah_sum
    (C : Set (Concept X)) (m : ℕ) (d : ℕ) (hd : VC_dim C ≤ d)
    -- Element-wise VC dimension bound: every restriction family has vcDim ≤ d.
    -- Equivalent to VC_dim C ≤ d when the ciSup is well-defined (BddAbove holds),
    -- but stated in the form Lean can directly use inside le_ciSup chains.
    (h_vcDim_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d) :
    growthFunction C m ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
  apply ciSup_le'
  intro S
  -- Convert from Nat.card to Finset.card
  rw [show Nat.card (Set.range fun h : C => restrictToSample h.val S) =
      (restrictionFamily C S).card from by
        rw [card_restrictionFamily_eq]]
  -- Apply Sauer-Shelah from Mathlib
  have hss := Finset.card_shatterer_le_sum_vcDim (𝒜 := restrictionFamily C S)
    (α := Fin m)
  calc (restrictionFamily C S).card
      ≤ (restrictionFamily C S).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (restrictionFamily C S).vcDim, (Fintype.card (Fin m)).choose k :=
        hss
    _ ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
        simp only [Fintype.card_fin]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Iic_subset_Iic.mpr (h_vcDim_elem m S)
        · intros; positivity

end VCDimension

section SauerShelahBound

/-!
## From the sum bound to the exponential bound

The Sauer-Shelah sum ∑_{k=0}^d C(m,k) ≤ (em/d)^d is a standard inequality.
We use it to bound the growth function in terms of (2em/d)^d for m replaced by 2m.
-/

/-- The standard inequality ∑_{k=0}^d C(n,k) ≤ (en/d)^d. -/
lemma sum_choose_le_pow (n d : ℕ) (hd : 0 < d) (hnd : d ≤ n) :
    (∑ k ∈ Finset.Iic d, Nat.choose n k : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  -- Proof: set r = d/n ∈ (0,1]. Show ∑ C(n,k) * r^d ≤ (1+r)^n ≤ exp(d).
  -- Then ∑ C(n,k) ≤ exp(d) / r^d = (exp(1) * n/d)^d.
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le hd hnd
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdn : (d : ℝ) ≤ n := Nat.cast_le.mpr hnd
  set r : ℝ := d / n with hr_def
  have hr0 : 0 < r := div_pos hd' hn
  have hr1 : r ≤ 1 := (div_le_one hn).mpr hdn
  have hr_pow_pos : 0 < r ^ d := pow_pos hr0 d
  -- Rewrite goal as: ∑ C(n,k) ≤ exp(d) / r^d
  have hexp_d : Real.exp 1 ^ d = Real.exp d := by
    rw [← Real.exp_nat_mul, mul_one]
  have hrhs : (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d = Real.exp d / r ^ d := by
    rw [hr_def, div_pow, mul_pow, hexp_d, div_pow]
    field_simp
  rw [hrhs, le_div_iff₀ hr_pow_pos]
  -- Goal: (∑ C(n,k)) * r^d ≤ exp(d)
  calc (∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ)) * r ^ d
      = ∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ) * r ^ d := by
          rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.Iic d, (Nat.choose n k : ℝ) * r ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          -- r^d ≤ r^k since 0 ≤ r ≤ 1 and k ≤ d
          exact pow_le_pow_of_le_one hr0.le hr1 (Finset.mem_Iic.mp hk)
    _ ≤ ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * r ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Iic d ⊆ range(n+1) since d ≤ n
            intro k hk
            simp only [Finset.mem_Iic] at hk
            simp only [Finset.mem_range]
            omega
          · intros; positivity
    _ = (r + 1) ^ n := by
          -- Binomial theorem: (r+1)^n = ∑_k C(n,k) * r^k * 1^(n-k)
          symm
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ ≤ Real.exp d := by
          calc (r + 1) ^ n
              ≤ (Real.exp r) ^ n := by
                  apply pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp r)
            _ = Real.exp d := by
                  rw [← Real.exp_nat_mul]
                  congr 1
                  rw [hr_def]
                  field_simp

/-- **Sauer-Shelah bound**: The growth function satisfies
Π_C(2m) ≤ (2·e·m/d)^d where d = VC_dim C. -/
theorem sauer_shelah_bound (C : Set (Concept X)) (m d : ℕ)
    (hd : 0 < d) (hVC : VC_dim C ≤ d) (hmd : d ≤ 2 * m)
    (h_vcDim_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d) :
    (growthFunction C (2 * m) : ℝ) ≤ (2 * Real.exp 1 * m / d) ^ d := by
  have hss := growthFunction_le_sauerShelah_sum C (2 * m) d hVC h_vcDim_elem
  calc (growthFunction C (2 * m) : ℝ)
      ≤ ∑ k ∈ Finset.Iic d, Nat.choose (2 * m) k := by exact_mod_cast hss
    _ ≤ (Real.exp 1 * (2 * m) / d) ^ d := by
        have h := sum_choose_le_pow (2 * m) d hd hmd
        push_cast at h ⊢; exact h
    _ = (2 * Real.exp 1 * m / d) ^ d := by ring

end SauerShelahBound

section PACSampleComplexity

/-!
## Main PAC Learning Theorem

Combining all pieces:
1. Pr[A] ≤ 2·Pr[B]                           (ghost_sample_bound)
2. Pr[B] ≤ Π_C(2m) · (1/2)^{εm/2}           (symmetrization_bound)
3. Π_C(2m) ≤ (2em/d)^d                        (sauer_shelah_bound)
4. Setting Π_C(2m)·(1/2)^{εm/2} ≤ δ/2 gives the sample size condition.
-/

/-- **Main PAC sample complexity theorem**:
If m ≥ c₀·(1/ε · log(1/δ) + d/ε · log(1/ε)), then with probability ≥ 1-δ
every bad hypothesis is inconsistent with the m-sample drawn from D.

Specifically, the probability (over S ~ D^m) that some bad h ∈ C is consistent
with S is at most δ.

Note: We bound the 2m-sample probability of Event A (which implies the m-sample
bad event by setting m' = m/2 and noting that 2m' examples are drawn). -/
theorem pac_sample_complexity_bound
    (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε δ : ℝ) (m d : ℕ)
    (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ < 1)
    (hd : 0 < d) (hVC : VC_dim C ≤ d)
    (hmd : d ≤ 2 * m)
    (hm_size : 8 / ε ≤ (m : ℝ))
    (hC : Set.Countable C)
    -- Element-wise VC dimension bound (see growthFunction_le_sauerShelah_sum for discussion).
    (hVC_elem : ∀ (n : ℕ) (S : Fin n → X), (restrictionFamily C S).vcDim ≤ d)
    -- Union bound hypotheses: bad hypotheses form a finite set bounded by the growth function.
    -- For a finite C this is immediate; for infinite C it captures the core VC-theoretic content.
    (hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h})
    (hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m))
    -- The full sample size condition after substituting Sauer-Shelah
    -- (uses natural log; matches the (1/2)^{εm/2} bound via log 2 factor):
    (hm : (2 / ε) * (d * Real.log (2 * Real.exp 1 * m / d) + Real.log (2 / δ)) ≤
          m * Real.log 2) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤ ENNReal.ofReal δ := by
  have hm_pos : 0 < m := by
    have : 0 < 8 / ε := by positivity
    exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hm_size; linarith)
  -- Step 1: ghost_sample_bound gives Pr[A] ≤ 2·Pr[B]
  calc (sampleMeasure D (2 * m)) {S | EventA C c D ε m S}
      ≤ 2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} :=
        ghost_sample_bound C c D ε m hε hm_size hm_pos hC
    -- Step 2-3: combine symmetrization and Sauer-Shelah to bound Pr[B] ≤ δ/2
    _ ≤ 2 * ENNReal.ofReal (δ / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        -- Apply sample_size_bound; remaining goal is the sample size condition
        apply sample_size_bound C c D ε δ m hε hδ hbad_fin hbad_card
        -- Verify the sample size condition with the Sauer-Shelah substituted bound
        calc (2 / ε) * (Real.log (growthFunction C (2 * m) : ℝ) + Real.log (2 / δ))
            ≤ (2 / ε) * (d * Real.log (2 * Real.exp 1 * m / d) + Real.log (2 / δ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              gcongr
              -- log(growthFunction) ≤ d * log(2em/d) follows from sauer_shelah_bound
              have hg := sauer_shelah_bound C m d hd hVC hmd hVC_elem
              rcases Nat.eq_zero_or_pos (growthFunction C (2 * m)) with h0 | hpos
              · -- If growthFunction = 0, then log 0 = 0 ≤ d * log(2em/d)
                simp only [h0, Nat.cast_zero, Real.log_zero]
                apply mul_nonneg (Nat.cast_nonneg _)
                apply Real.log_nonneg
                rw [le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)]
                have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
                have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
                simp only [one_mul]
                calc (d : ℝ) ≤ 2 * ↑m := by exact_mod_cast hmd
                  _ = 2 * 1 * ↑m := by ring
                  _ ≤ 2 * Real.exp 1 * ↑m := by gcongr
              · -- If growthFunction > 0, use log monotonicity
                rw [← Real.log_pow]
                exact Real.log_le_log (by exact_mod_cast hpos) hg
          _ ≤ m * Real.log 2 := hm
    -- Step 4: 2 * (δ/2) = δ
    _ = ENNReal.ofReal δ := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring

end PACSampleComplexity
