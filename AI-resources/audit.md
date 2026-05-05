# Auditing the PAC Complexity Proof

## Definitions (Definitions.lean)

### Definitions
| Name | Description |
|---|---|
| `Concept X` | A measurable subset of the instance space `X`. Both hypotheses and the target concept are represented this way, so that we can take measures of their symmetric difference. |
| `trueError D h c` | The probability under `D` that `h` and `c` disagree on a random point. This is the quantity we want to make small through learning. Returns `ENNReal` so it plays well with measure theory. |
| `isError h c x` | Whether `h` and `c` classify `x` differently. The building block for both `trueError` and `errorCount`. |
| `isError.decidable` | Classical decidability instance for `isError`. Needed so we can use `Finset.filter` to count errors over a finite sample. |
| `errorCount h c S` | The number of points in sample `S` where `h` makes a mistake relative to `c`. This is the finite-sample analogue of `trueError`. |
| `empiricalError h c S` | The empirical error rate, i.e., `errorCount` divided by sample size. Not used in the main proofs but included for completeness. |
| `restrictToSample h S` | The labeling of sample `S` induced by `h`: which indices get classified as positive. Used to define the growth function — two hypotheses are "equivalent on S" iff they produce the same labeling. |
| `sampleMeasure D m` | The product measure `D^m`, modeling `m` iid draws from `D`. Almost all probability statements in the proof are over this measure. |
| `firstHalf S` | Extracts the first `m` points of a `2m`-sample. Used to split the ghost sample into two halves for the symmetrization argument. |
| `secondHalf S` | Extracts the last `m` points of a `2m`-sample. The "ghost" half — it is never seen by the learner but used to witness many errors. |
| `combineHalves S₁ S₂` | Concatenates two `m`-samples into a `2m`-sample. Inverse of the `(firstHalf, secondHalf)` split; needed to verify that splitting and recombining is the identity. |

### Lemmas
| Name | Description |
|---|---|
| `firstHalf_combineHalves` | Splitting a combined sample recovers the first half. Used as a simp lemma when verifying the split-combine identity. |
| `secondHalf_combineHalves` | Splitting a combined sample recovers the second half. Symmetric to the above. |
| `sampleMeasure_isProbability` | The product measure `D^m` is a probability measure whenever `D` is. Needed throughout since many Mathlib lemmas require `IsProbabilityMeasure`. |

---

## Ghost Sample Lemma (GhostSample.lean)

### Section: Events

| Name | Description |
|---|---|
| `isBadHypothesis D c ε h` | Says that `h` has true error at least `ε`. This is the set of hypotheses we want to rule out — they generalize poorly but might still be empirically consistent. |
| `isConsistentWith h c S₁` | Says `h` makes no mistakes on the sample `S₁`. A learner that outputs `h` would see zero training error. |
| `hasManyErrors ε m h c S₂` | Says `h` makes at least `εm/2` errors on the ghost half `S₂`. This is the condition that lets us "catch" a bad hypothesis using the second half of the double sample. |
| `EventA C c D ε m S` | There exists some bad hypothesis in `C` that is consistent with the first half of `S`. This is the event we ultimately want to bound — it means the learner could be fooled. |
| `EventB C c D ε m S` | There exists some bad hypothesis in `C` that is both consistent with the first half and makes many errors on the second half. This is a strictly stronger event used as an intermediate: it implies A but is easier to bound via a union argument. |
| `eventB_implies_eventA` | EventB implies EventA. This is immediate from the definitions; it is used to chain the ghost sample bound and the symmetrization bound together. |

### Shared Measurability Helpers

| Name | Description |
|---|---|
| `isError_set_symmDiff` | **Private.** The set of error points for `h` vs `c` equals the symmetric difference of their underlying sets. This bridges the predicate `isError` with the measure-theoretic notion `symmDiff`, which is what `trueError` is defined in terms of. |
| `isError_measurableSet` | The error set is measurable. Required any time we want to take its measure or integrate over it, which happens repeatedly throughout the proof. |

### Section: BernoulliErrorBound

#### `errIndicator` infrastructure (all private)
| Name | Description |
|---|---|
| `errIndicator h c` | **Private def.** The `{0,1}`-valued indicator of whether a point is an error. Converting the boolean `isError` predicate into a real-valued function lets us compute means and variances using standard Mathlib integral/variance machinery. |
| `errIndicator_eq_indicator` | **Private.** Rewrites `errIndicator` as a `Set.indicator`, which is the canonical Mathlib form. Needed to apply Mathlib's integral lemmas for indicator functions. |
| `errIndicator_measurable` | **Private.** Measurability of `errIndicator`. Required for integration and for `MemLp`. |
| `errIndicator_mem_Icc` | **Private.** `errIndicator` takes values in `[0, 1]`. Used to verify the boundedness condition needed for `MemLp` and for the variance bound. |
| `errIndicator_memlp` | **Private.** `errIndicator ∈ Lp(2, D)`. Required as a hypothesis for Chebyshev's inequality and for `variance_sum_pi`. |
| `errIndicator_integral` | **Private.** The expectation of `errIndicator` under `D` equals the true error probability. This is what connects the mean of the error sum to `trueError`. |
| `errIndicator_variance_le` | **Private.** The variance of `errIndicator` is at most the true error probability `p`. Uses the fact that a Bernoulli(p) variable has variance `p(1-p) ≤ p`. |
| `errIndicator_integrable_coord` | **Private.** The function `S ↦ errIndicator h c (S i)` is integrable under `D^m`. Needed to swap the sum and integral in `errorSum_integral`. |

#### Error sum infrastructure (all private)
| Name | Description |
|---|---|
| `errorSum_range` | **Private.** The sum of error indicators over a sample lies in `[0, m]`. This range bound is the key input to `memLp_of_bounded` that gives us `MemLp` for the whole sum. |
| `errorSum_memlp` | **Private.** The error sum `S ↦ Σᵢ errIndicator(Sᵢ)` is in `Lp(2, D^m)`. This is the main measurability-and-integrability certificate required to apply Chebyshev's inequality to the sum. |
| `hasManyErrors_iff_errorSum` | **Private.** `hasManyErrors` holds for `S` iff the error indicator sum reaches `εm/2`. This bridge between the domain predicate and the numeric sum is what lets `notManyErrors_subset_chebyshev_dev` use `hasManyErrors_iff_errorSum` to enter the Chebyshev framework. |
| `errorSum_integral` | **Private.** The expected error count under `D^m` is `m · p`. This is the mean used in the Chebyshev bound — we need it to be `mp` so that the deviation threshold `mp/2` is half the mean. |
| `errorSum_variance_le` | **Private.** The variance of the error sum under `D^m` is at most `m · p`. Uses independence of coordinates via `variance_sum_pi`. Together with the mean, this gives us control over the Chebyshev ratio `Var/t²`. |
| `many_errors_measurableSet` | **Private.** The event `\{S | hasManyErrors \}` is measurable. Required when we compute its complement probability and apply `prob_compl_eq_one_sub`. |

#### Pure math helpers (all private)
| Name | Description |
|---|---|
| `mp_le_half_mp_div2_sq` | **Private.** If `μ ≥ 8` then `μ ≤ (1/2)(μ/2)²`. This is the purely algebraic inequality that makes the Chebyshev ratio `Var/(μ/2)²` collapse to `≤ 1/2`. |
| `eight_le_mul_of_div_le` | **Private.** If `8/ε ≤ m`, `ε ≤ p`, and `m > 0`, then `8 ≤ mp`. Converts the sample size hypothesis into the `mp ≥ 8` form needed by `var_div_sq_le_half`. |
| `var_div_sq_le_half` | **Private.** If `Var ≤ μ` and `8 ≤ μ`, then `Var/(μ/2)² ≤ 1/2`. This is the crux of the Chebyshev argument — it shows the probability of a large deviation is at most 1/2. |
| `one_sub_ofReal_half` | **Private.** `1 - ofReal(1/2) = ofReal(1/2)` in `ENNReal`. Used to flip between "complement ≤ 1/2" and "event ≥ 1/2" in the final step of `bernoulli_error_lower_bound`. |
| `notManyErrors_subset_chebyshev_dev` | **Private.** Any sample that fails the many-errors threshold must have its error sum far below the mean, and is therefore inside the Chebyshev large-deviation set. This inclusion is what lets us bound `P(¬hasManyErrors)` using the Chebyshev tail bound. |
| `prob_ge_half_of_compl_le_half` | **Private.** In any probability space, if `P(Eᶜ) ≤ 1/2` then `P(E) ≥ 1/2`. This is the final flip that converts the upper bound on the complement into the lower bound we actually want. |

#### Main lemmas
| Name | Description |
|---|---|
| `error_indicator_mean_ge` | For a bad hypothesis, the probability of an error at a random point is at least `ε`. This is an immediate restatement of `isBadHypothesis` in terms of the error set measure; it is essentially a sanity lemma bridging definitions. |
| `bernoulli_error_lower_bound` | **Key lemma.** For any bad hypothesis `h` and sample size `m ≥ 8/ε`, a fresh `m`-point sample will contain at least `εm/2` errors with probability at least `1/2`. This is the probabilistic heart of the ghost sample argument — it guarantees that the ghost half "witnesses" the bad hypothesis with good probability. |

### Section: GhostSampleBound

#### Helpers
| Name | Description |
|---|---|
| `sampleMeasure_eq_prod` | The push-forward of the `2m`-sample measure along the half-split map equals `D^m ⊗ D^m`. This is the measure-theoretic fact that allows us to treat the two halves of the double sample as independent, enabling the Fubini-style integration argument. |
| `event_prob_eq_prod` | For any measurable product-space event `E`, the `2m`-sample probability of `$\{$S | (firstHalf S, secondHalf S) ∈ E $\}$` equals `(D^m ⊗ D^m)(E)`. This is a convenience corollary of `sampleMeasure_eq_prod` that avoids repeating the map-apply calculation every time we translate between the `2m`-space and the product space. |
| `consistent_set_eq_pi` | **Private.** The set of samples consistent with `h` is a product set (each coordinate must lie outside the error set). This pi-set form is what Mathlib needs to compute its measure as a product of individual coordinate measures. |
| `A_prod_measurable` | **Private.** The product-space version of EventA is measurable. Required to apply Fubini (via `Measure.prod_apply`) and to form the slice measures. |
| `B_prod_measurable` | **Private.** The product-space version of EventB is measurable. Same reason as above. |
| `two_mul_ofReal_half` | **Private.** `2 · ofReal(1/2) = 1` in `ENNReal`. Used to convert the lower bound `P(B-slice) ≥ 1/2` into `1 ≤ 2 · P(B-slice)` in the final pointwise comparison. |

#### Main theorem
| Name | Description |
|---|---|
| `ghost_sample_bound` | **Theorem.** `P[EventA] ≤ 2 · P[EventB]` under the iid double-sample measure. The proof decomposes the double sample into a product, applies Fubini to reduce to a pointwise bound, and then uses `bernoulli_error_lower_bound` to show that whenever EventA holds for a first-half `S₁`, the second-half probability of EventB is at least `1/2`. |

---

## Hypergeometric Bound (Hypergeometric.lean)

> **Note:** Imported by `Symmetrization.lean` but not currently used in any proof. It provides an alternative combinatorial approach — bounding the probability that all errors land in the second half using the hypergeometric ratio — whereas the current proofs use the exponential `(1-p)^m` route instead.

| Name | Description |
|---|---|
| `two_mul_sub_le` | **Private.** `2(m-l) ≤ 2m - l` for `l ≤ m`. A small natural number arithmetic fact needed in the inductive step to ensure the numerator and denominator of the combinatorial ratio move in the right direction. |
| `hypergeometric_bound_nat_succ` | **Private.** The inductive step: if the bound `2^l · C(m,l) ≤ C(2m,l)` holds at `l`, it holds at `l+1`. The proof uses the Pascal-type recurrences for `C(m,l+1)` and `C(2m,l+1)`. |
| `hypergeometric_bound_nat` | **Private.** The full induction: `2^l · C(m,l) ≤ C(2m,l)` for all `l ≤ m`. This is the core combinatorial inequality underlying the hypergeometric bound. |
| `hypergeometric_bound_cast` | **Private.** Casts `hypergeometric_bound_nat` from `ℕ` to `ℝ`. A routine but necessary type-coercion step before we can do real division. |
| `choose_2m_pos` | **Private.** `C(2m, l) > 0` in `ℝ` when `l ≤ m`. Needed to divide safely by `C(2m, l)` in `hypergeometric_bound`. |
| `half_pow_mul_two_pow` | **Private.** `(1/2)^l · 2^l = 1` in `ℝ`. Used to rewrite the combinatorial inequality into the ratio form `C(m,l)/C(2m,l) ≤ (1/2)^l`. |
| `hypergeometric_bound` | **Main lemma.** `C(m,l) / C(2m,l) ≤ (1/2)^l` for `l ≤ m`. Probabilistically: if we randomly split `2m` points into two halves, the chance that all `l` error points land in the second half is at most `(1/2)^l`. |

---

## Symmetrization Lemma (Symmetrization.lean)

### Section: GrowthFunction

| Name | Description |
|---|---|
| `growthFunction C m` | The growth function `Π_C(m)`: the maximum number of distinct ways that `C` can classify an `m`-point sample. It is the key complexity measure of the concept class — the Sauer-Shelah lemma bounds it in terms of VC dimension. |
| `card_labelings_le_growthFunction` | For any fixed sample `S`, the number of distinct labelings is at most `growthFunction C m`. This justifies the definition by confirming the supremum is indeed an upper bound for each individual sample. |
| `growthFunction_le_two_pow` | `growthFunction C m ≤ 2^m`. A trivial upper bound used to confirm the supremum in the definition is finite, which is needed for `le_ciSup` to be applicable. |

### Section: UnionBound

#### Pure math helpers (all private)
| Name | Description |
|---|---|
| `log_two_le_two` | **Private.** `log 2 ≤ 2`. Needed in `one_sub_pow_le_rpow_half` to convert the `exp(-εm)` bound into the `(1/2)^(εm/2)` form required by the union bound. |
| `rpow_half_eq_exp` | **Private.** `(1/2)^(εm/2) = exp(-(εm/2) · log 2)`. This bridges the probabilistic expression `(1/2)^{εm/2}` with the exponential form needed to chain the `exp(-pm)` bound. |
| `one_sub_pow_le_rpow_half` | **Private.** `(1-p)^m ≤ (1/2)^(εm/2)` when `0 < ε ≤ p ≤ 1`. This is the key analytic fact that bounds the consistency probability for bad hypotheses. It chains three steps: `(1-p)^m ≤ exp(-pm)` (from `1-x ≤ exp(-x)`), `exp(-pm) ≤ exp(-εm)` (since `p ≥ ε`), and `exp(-εm) ≤ (1/2)^(εm/2)` (since `log 2 ≤ 2`). |

#### Main lemmas
| Name | Description |
|---|---|
| `consistent_firstHalf_prob` | The probability that a hypothesis `h` is consistent with the first half of a double sample equals `(1-p)^m`, where `p` is its true error. This computation, via the product structure of the measure and independence across coordinates, is what makes `per_hypothesis_bound` work. |
| `per_hypothesis_bound` | For any bad hypothesis `h`, the probability that a `2m`-sample has `h` consistent with the first half and making many errors on the second half is at most `(1/2)^(εm/2)`. This is the per-hypothesis contribution to the union bound. |
| `symmetrization_bound` | **Theorem.** `P[EventB] ≤ growthFunction C (2m) · (1/2)^(εm/2)`. Proved by covering EventB with a union over bad hypotheses, bounding each term with `per_hypothesis_bound`, and then noting there are at most `growthFunction` such hypotheses. |

### Section: SampleSizeBound

| Name | Description |
|---|---|
| `sample_size_bound` | **Theorem.** If the sample size condition `(2/ε) · (log(growthFunction) + log(2/δ)) ≤ m · log 2` holds, then `P[EventB] ≤ δ/2`. Proved by taking the logarithm of the symmetrization bound and rearranging. |

---

## PAC Sample Complexity Bound (Main.lean)

### Section: VCDimension

| Name | Description |
|---|---|
| `restrictionFamily C S` | The labeling family of `C` on sample `S`, as a `Finset (Finset (Fin m))`. Translating from the measure-theoretic concept class into a finite combinatorial object is what allows us to invoke Mathlib's Sauer-Shelah lemma. |
| `VC_dim C` | The VC dimension of `C`, defined as the supremum of the combinatorial VC dimensions of its restriction families. This is the complexity parameter that determines sample complexity. |
| `card_restrictionFamily_eq` | The cardinality of the restriction family equals `Nat.card` of the labeling range. A routine conversion needed to move between the `Finset.card` required by Sauer-Shelah and the `Nat.card` appearing in `growthFunction`. |
| `growthFunction_le_sauerShelah_sum` | **Theorem.** `growthFunction C m ≤ Σ_{k ≤ d} C(m, k)` when `VC_dim C ≤ d`. The key step connecting VC dimension to a concrete polynomial bound on the growth function, via Mathlib's `Finset.card_shatterer_le_sum_vcDim`. |

### Section: SauerShelahBound

| Name | Description |
|---|---|
| `rpow_exp_div_form` | **Private.** `(exp(1) · n/d)^d = exp(d) / (d/n)^d`. A pure algebra bridge that rewrites the goal of `sum_choose_le_pow` into a form amenable to the `le_div_iff` step, avoiding repeated inline algebra. |
| `sum_choose_le_pow` | `Σ_{k ≤ d} C(n, k) ≤ (en/d)^d`. The standard analytic inequality bounding the Sauer-Shelah sum by an exponential. Proved by setting `r = d/n`, bounding the partial sum by the full binomial sum `(1+r)^n`, and then using `1+r ≤ exp(r)`. |
| `sauer_shelah_bound` | **Theorem.** `growthFunction C (2m) ≤ (2em/d)^d`. The final Sauer-Shelah bound in the form needed by `pac_sample_complexity_bound`. |

### Section: PACSampleComplexity

| Name | Description |
|---|---|
| `m_pos_of_size_condition` | **Private.** If `8/ε ≤ m` and `ε > 0` then `m > 0`. A positivity side-goal factored out to keep the main theorem clean. |
| `one_le_two_exp_mul_div` | **Private.** `1 ≤ 2·exp(1)·m/d` when `d ≤ 2m` and `m ≥ 1`. Needed when the growth function is zero and we must show `d · log(2em/d) ≥ 0` by proving the argument of the log is at least 1. |
| `log_growthFunction_le_sauerShelah` | **Private.** `log(growthFunction C (2m)) ≤ d · log(2em/d)`. Converts the polynomial Sauer-Shelah bound into the logarithmic form required by `sample_size_bound`. Requires a case split because `log 0` needs separate treatment. |
| `two_mul_ofReal_div2` | **Private.** `2 · ofReal(δ/2) = ofReal(δ)` in `ENNReal`. The final arithmetic step that collapses `2 · (δ/2)` back to `δ` after bounding `P[EventB] ≤ δ/2`. |
| `pac_sample_complexity_bound` | **Main theorem.** Under the sample complexity condition, the probability that any bad hypothesis is consistent with the training sample is at most `δ`. Chains `ghost_sample_bound → sample_size_bound → log_growthFunction_le_sauerShelah` to connect VC dimension, sample size, and generalization probability. |
