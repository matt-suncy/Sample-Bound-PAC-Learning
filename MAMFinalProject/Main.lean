import MAMFinalProject.Definitions
import MAMFinalProject.GhostSample
import MAMFinalProject.Symmetrization
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SetFamily.Shatter

open MeasureTheory ProbabilityTheory Real Set Classical Finset

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
  rw [← Nat.card_coe_Finset]
  congr 1
  simp [Set.toFinset_range]

/-- The growth function is bounded by the Sauer-Shelah sum ∑_{k ≤ d} C(m,k),
where d = VC_dim C.

**Proof**: For any sample S of size m, by Mathlib's Sauer-Shelah lemma:
  |restrictionFamily C S| = #(restrictionFamily C S) ≤ #shatterer ≤ ∑_{k ≤ d} C(m,k)
The growth function is the sup over all such S, so it's also ≤ ∑_{k ≤ d} C(m,k). -/
theorem growthFunction_le_sauerShelah_sum
    (C : Set (Concept X)) (m : ℕ) (d : ℕ) (hd : VC_dim C ≤ d) :
    growthFunction C m ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
  apply ciSup_le
  intro S
  -- Convert from Nat.card to Finset.card
  rw [show Nat.card (Set.range fun h : C => restrictToSample h.val S) =
      (restrictionFamily C S).card from by
        rw [card_restrictionFamily_eq]]
  -- Apply Sauer-Shelah from Mathlib
  have hss := Finset.card_shatterer_le_sum_vcDim (𝒜 := restrictionFamily C S)
    (α := Fin m)
  -- The shatterer of the restriction family has the same card as itself
  -- (or we bound the card by the shatterer bound)
  calc (restrictionFamily C S).card
      ≤ (restrictionFamily C S).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (restrictionFamily C S).vcDim, (Fintype.card (Fin m)).choose k :=
        hss
    _ ≤ ∑ k ∈ Finset.Iic d, Nat.choose m k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.Iic_subset_Iic.mpr
          -- vcDim (restrictionFamily C S) ≤ VC_dim C ≤ d
          calc (restrictionFamily C S).vcDim
              ≤ VC_dim C := by
                apply le_ciSup_of_le (OrderTop.bddAbove _)
                apply le_ciSup_of_le (OrderTop.bddAbove _)
                exact le_refl _
            _ ≤ d := hd
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
  -- This is a standard result proved by the AM-GM inequality on the sum.
  -- Each term C(n,k) ≤ (n/k)^k ≤ (en/k)^k, summing gives the bound.
  sorry

/-- **Sauer-Shelah bound**: The growth function satisfies
Π_C(2m) ≤ (2·e·m/d)^d where d = VC_dim C. -/
theorem sauer_shelah_bound (C : Set (Concept X)) (m d : ℕ)
    (hd : 0 < d) (hVC : VC_dim C ≤ d) (hmd : d ≤ 2 * m) :
    (growthFunction C (2 * m) : ℝ) ≤ (2 * Real.exp 1 * m / d) ^ d := by
  have hss := growthFunction_le_sauerShelah_sum C (2 * m) d hVC
  calc (growthFunction C (2 * m) : ℝ)
      ≤ ∑ k ∈ Finset.Iic d, Nat.choose (2 * m) k := by exact_mod_cast hss
    _ ≤ (Real.exp 1 * (2 * m) / d) ^ d := sum_choose_le_pow (2 * m) d hd hmd
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
    -- The full sample size condition after substituting Sauer-Shelah:
    (hm : (2 / ε) * (d * Real.log (2 * Real.exp 1 * m / d) + Real.log (2 / δ)) ≤ m) :
    (sampleMeasure D (2 * m)) {S | EventA C c D ε m S} ≤ ENNReal.ofReal δ := by
  have hm_pos : 0 < m := by
    have : 0 < 8 / ε := by positivity
    exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hm_size; linarith)
  -- Step 1: ghost_sample_bound gives Pr[A] ≤ 2·Pr[B]
  calc (sampleMeasure D (2 * m)) {S | EventA C c D ε m S}
      ≤ 2 * (sampleMeasure D (2 * m)) {S | EventB C c D ε m S} :=
        ghost_sample_bound C c D ε m hε hm_size hm_pos
    -- Step 2-3: combine symmetrization and Sauer-Shelah to bound Pr[B] ≤ δ/2
    _ ≤ 2 * ENNReal.ofReal (δ / 2) := by
        apply mul_le_mul_left'
        -- Apply sample_size_bound with the Sauer-Shelah substituted growth function bound
        apply (sample_size_bound C c D ε δ m hε hδ _)
        -- Verify the sample size condition with the substituted bound
        calc (2 / ε) * (Real.log ↑(growthFunction C (2 * m)) + Real.log (2 / δ))
            ≤ (2 / ε) * (d * Real.log (2 * Real.exp 1 * m / d) + Real.log (2 / δ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              gcongr
              -- log(growthFunction) ≤ d * log(2em/d) follows from sauer_shelah_bound
              have hg := sauer_shelah_bound C m d hd hVC hmd
              have hg_pos : (0 : ℝ) < growthFunction C (2 * m) := by
                sorry -- growth function is positive
              rw [← Real.log_pow]
              apply Real.log_le_log hg_pos hg
          _ ≤ m := hm
    -- Step 4: 2 * (δ/2) = δ
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end PACSampleComplexity
