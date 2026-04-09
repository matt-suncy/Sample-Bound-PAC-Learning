# Error Log — PAC Learning Lean 4 Formalization

Last updated: 2026-04-08

Tracks errors, type mismatches, failed approaches, and gotchas encountered during formalization.
Update this file as new errors are found or resolved.

---

## Resolved Errors

### [RESOLVED] `axiom` / `opaque` declarations not allowed
**File:** Various (early commits)
**Error:** Project requires all theorems proven from Mathlib; `axiom` and `opaque` stubs were used initially.
**Resolution:** Replaced all axioms/opaques with proper Lean 4 definitions grounded in Mathlib4. Definitions now use `noncomputable def` with real Mathlib types.

### [RESOLVED] Build type mismatches in `growthFunction` definition
**File:** `Symmetrization.lean`
**Error:** Type errors when trying to define `growthFunction` using `Finset.card` vs `Nat.card`; universe issues with `Set.range`.
**Resolution:** Defined as `⨆ S : Fin m → X, Nat.card (Set.range fun h : C => restrictToSample h.val S)`. Introduced `restrictionFamily` in `Main.lean` as the `Finset (Finset (Fin m))` version for use with Mathlib's Sauer-Shelah.

### [RESOLVED] `Finset.card_le_card_shatterer` missing / wrong name
**File:** `Main.lean`
**Error:** Could not find the right Mathlib lemma name for `|𝒜| ≤ |𝒜.shatterer|`.
**Resolution:** Correct name is `Finset.card_le_card_shatterer`.

### [RESOLVED] `Finset.card_shatterer_le_sum_vcDim` argument structure
**File:** `Main.lean`
**Error:** Incorrect argument passing to Mathlib's Sauer-Shelah; `α` type argument needed explicit instantiation.
**Resolution:** Passed explicitly as `(α := Fin m)`.

### [RESOLVED] `sum_choose_le_pow` — `add_pow` direction
**File:** `Main.lean`
**Error:** `(r+1)^n = ∑ C(n,k) * r^k` needed `symm` before `rw [add_pow]` because the binomial theorem states the sum equals the power.
**Resolution:** Added `symm` before rewrite; adjusted `push_cast` / `ring` finishing.

### [RESOLVED] `Real.rpow_def_of_pos` signature change
**File:** `Symmetrization.lean`
**Error:** `(1/2 : ℝ) ^ (ε * m / 2)` is `HPow.hPow` (real power), needed `rpow_def_of_pos` to convert to `exp`/`log` form, but signature was called incorrectly.
**Resolution:** Used `Real.rpow_def_of_pos (by norm_num)` with `show` to clarify the base.

### [RESOLVED] `sampleMeasure_eq_prod` — proved 2026-04-08
**File:** `GhostSample.lean`
**Resolution:** Composed two measure-preserving maps:
1. `(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm` using `f = finSumFinEquiv.trans (Fin.castOrderIso h2m).toEquiv : Fin m ⊕ Fin m ≃ Fin (2*m)`
2. `MeasurableEquiv.sumPiEquivProdPi`
Key lemma: `Equiv.piCongrLeft_symm_apply (fun _ => X) f S j` (note: `P` and `e` are both explicit in the variable section — must pass both).
Function equality proved via `Prod.ext` + `funext i` + `simp only [firstHalf/secondHalf]` + `congr 1` (which closes by definitional equality of `Fin` values).

### [RESOLVED] `bernoulli_error_lower_bound` — proved 2026-04-08
**File:** `GhostSample.lean`
**Resolution:** Full Chebyshev proof using:
- `variance_sum_pi (ι := Fin m) (μ := ...) (X := ...)` for variance additivity (explicit named args needed)
- `integral_finset_sum` + `integral_comp_eval` for E[Y] = mp (term-mode calc to avoid simp matching issues)
- `memLp_of_bounded` for L² membership of the indicator function
- `div_le_iff₀` (not `div_le_iff`) for the Chebyshev arithmetic step
- `tsub_le_tsub_left` (not `ENNReal.tsub_le_tsub_left`) for the ENNReal complement step
- `measurableSet_le measurable_const hY_meas` (standalone, not dot notation)
- `ENNReal.one_ne_top` (fully qualified, not `one_ne_top`)
- `set_option maxHeartbeats 800000 in` placed BEFORE the docstring

### [RESOLVED] `ghost_sample_bound` — structure proved 2026-04-08
**File:** `GhostSample.lean`
**Resolution:** Structure complete with:
- `measurable_measure_prodMk_left` (not `measurable_measure_prod_mk_left`) for slice measurability
- `mul_le_mul_right hBsec_lb 2` (not `ENNReal.mul_le_mul_left'`, which is deprecated since 2025-11-27)
- `ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top` for `2 * (1/2) = 1`
- `show` before `by_cases` to beta-reduce the lambda from `lintegral_mono`
- 2 sorries remain: `hA_meas`, `hB_meas` (measurability of C-existential sets)

### [RESOLVED] `symmetrization_bound` structure — 2026-04-08
**File:** `Symmetrization.lean`
**Resolution:** Proof structure written with:
- `per_h_bound` subproof showing `P[B_h] ≤ (1/2)^{εm/2}` via:
  - `pow_le_pow_left₀` (not `pow_le_pow_left`, which doesn't exist) for `(1-p)^m ≤ exp(-p)^m`
  - `Real.one_sub_le_exp_neg` from `Mathlib.Analysis.Complex.Exponential`
  - `Real.exp_nat_mul` + `ring_nf` for `exp(-p)^m = exp(-pm)`
  - `Real.exp_le_exp.mpr` for monotonicity
  - `Real.add_one_le_exp 2` + `Real.log_le_log` + `Real.log_exp` for `log 2 ≤ 2`
  - `Real.rpow_def_of_pos` to convert `(1/2)^{εm/2}` to exp form
  - `nlinarith` for the final numeric inequality
- 2 sorries remain: `hconsist_bound` and the union bound step (see below)

### [RESOLVED] `simp_rw [integral_finset_sum]` pattern matching
**File:** `GhostSample.lean`
**Error:** `rw [integral_finset_sum ...]` failed because the syntactic pattern `∑ i ∈ s, f i a` didn't match `∑ i : Fin m, errInd (S i)`.
**Resolution:** Used `integral_finset_sum _ (fun i _ => hint i)` in term-mode inside a `calc` block instead of `rw`.

### [RESOLVED] `integral_comp_eval` application
**File:** `GhostSample.lean`
**Error:** `simp_rw [integral_comp_eval herrInd_aesm]` failed — couldn't unify `(fun _ : Fin m => D) i` with `D`.
**Resolution:** Used `apply Finset.sum_congr rfl; intro i _; exact (integral_comp_eval (μ := ...) (i := i) herrInd_aesm).trans hEerrInd`.

### [RESOLVED] `variance_sum_pi` typeclass inference
**File:** `GhostSample.lean`
**Error:** `variance_sum_pi` failed to infer `ι`; also the function parameter is named `X` not `f`.
**Resolution:** Used explicit `(ι := Fin m) (μ := ...) (X := ...)` named arguments; rewrote `Y` to explicit sum form via `funext` + `simp [Finset.sum_apply]`.

### [RESOLVED] `one_sub_le_exp_neg` location
**File:** `Symmetrization.lean`
**Note:** `Real.one_sub_le_exp_neg` is in `Mathlib.Analysis.Complex.Exponential`, not `Mathlib.Analysis.SpecialFunctions.Exp`. Imported via `MAMFinalProject.GhostSample` which imports `Mathlib.MeasureTheory.Integral.Pi`.

### [RESOLVED] `pow_le_pow_left` → `pow_le_pow_left₀`
**File:** `Symmetrization.lean`
**Error:** `pow_le_pow_left` is not in scope (it's `pow_le_pow_left'` in unbundled setting, but that's for ordered monoids without `0 ≤`).
**Resolution:** Use `pow_le_pow_left₀` from `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic` — signature `(ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a^n ≤ b^n`.

### [RESOLVED] `Main.lean` calc `lhs is ↑d but expected 1 * ↑d`
**File:** `Main.lean:243`
**Error:** After `rw [le_div_iff₀ ...]`, the goal had `1 * ↑d ≤ ...` but the `calc` started with `(d : ℝ)`.
**Resolution:** Added `simp only [one_mul]` before the `calc` block to normalize `1 * ↑d` to `↑d`.

---

## Open / Unresolved Errors and Known Risks

### [IN PROGRESS] `hA_meas`, `hB_meas` — measurability of C-existential sets
**File:** `GhostSample.lean` inside `ghost_sample_bound`
**Approach:** Added `(hC : Set.Countable C)` to `ghost_sample_bound` and `pac_sample_complexity_bound`. Proof uses `MeasurableSet.biUnion hC`, with `by_cases hbad` per concept:
- Bad case: set = `Prod.fst ⁻¹' Set.pi Set.univ (fun _ => {x | isError}ᶜ)` — measurable via `measurable_fst (MeasurableSet.univ_pi ...)`
- hB_meas bad case: additionally intersect with `Prod.snd ⁻¹' {S₂ | εm/2 ≤ errorCount}` — measurable via `measurable_snd (measurableSet_le measurable_const herr_meas)` where `herr_meas` uses `Finset.measurable_sum` + `indicator`
- Not-bad case: set is empty, trivially measurable
**Status:** Proof written, compiling errors remain (see active errors below)
**Risk:** Low — approach is correct, just fixing Lean syntax issues

### [RESOLVED] `hconsist_bound` — computing P[consistent with S₁] = (1-p)^m (proved 2026-04-08)
**File:** `Symmetrization.lean` inside `symmetrization_bound`
**Proof:**
1. `sampleMeasure_eq_prod` + `Measure.map_apply` + `Measure.prod_prod` + `measure_univ` to reduce to `P₁ {S₁ | consistent}`
2. `{S₁ | consistent} = Set.pi univ (fun _ => {x | isError}ᶜ)` via `ext` + `simp`
3. `MeasurableSet.univ_pi` for measurability
4. `Measure.pi_pi` + `Finset.prod_const` + `Finset.card_univ` + `Fintype.card_fin` → `D {x | ¬error}^m`
5. `prob_compl_eq_one_sub` → `(1 - D {x | error})^m`
6. `ENNReal.ofReal_toReal` to get `D {x | error} = ENNReal.ofReal p`
7. `ENNReal.ofReal_sub` + `ENNReal.ofReal_one` → `1 - ENNReal.ofReal p = ENNReal.ofReal (1-p)`
8. `ENNReal.ofReal_pow` → `ENNReal.ofReal (1-p)^m = ENNReal.ofReal ((1-p)^m)`

### [OPEN] Union bound step — disintegration argument
**File:** `Symmetrization.lean` inside `symmetrization_bound`
**Issue:** Need to show P[EventB] ≤ growthFunction(C,2m) · (1/2)^{εm/2} by:
1. Expressing EventB as a union over at most growthFunction distinct labeling classes
2. Applying a union bound
**Risk (HIGH):** For uncountable C, the union over labeling classes requires either:
- Disintegration / RegularConditionalKernel (hard)
- A measurable selection theorem
- `Countable C` hypothesis (simplest workaround)

---

## Notes on Naming / API Gotchas

- Mathlib uses `Finset.Iic d` for `{0, 1, ..., d}` (not `Finset.range (d+1)`), but both work.
- `Nat.card` vs `Finset.card`: `growthFunction` uses `Nat.card` on a `Set.range`; the Sauer-Shelah bound uses `Finset.card` on a `Finset`. The bridge is `card_restrictionFamily_eq`.
- `IsProbabilityMeasure` is an instance, not a hypothesis in the usual sense — it needs to be in scope as `[IsProbabilityMeasure D]`.
- `ENNReal.ofReal` is needed whenever converting `ℝ`-valued probability bounds to `ENNReal` (the type of `Measure.apply`).
- `Real.rpow` vs `HPow.hPow`: `(x : ℝ) ^ (y : ℝ)` uses `rpow`; `(x : ℝ) ^ (n : ℕ)` uses `HPow`. Be careful in the `symmetrization_bound` where `ε * m / 2 : ℝ` appears as an exponent.
- `mul_le_mul_left'` is deprecated since 2025-11-27 in Mathlib; use `mul_le_mul_right` instead.
- `pow_le_pow_left` does not exist in the expected form; use `pow_le_pow_left₀` (with subscript 0).
- `measurable_measure_prod_mk_left` is wrong; the correct name is `measurable_measure_prodMk_left`.
- `ENNReal.mul_div_cancel (h₀ : a ≠ 0) (h∞ : a ≠ ∞) : a * (b / a) = b` — correct form for `2 * (1/2) = 1`.
- `set_option maxHeartbeats N in` must appear BEFORE the docstring of a declaration, not after.
- `MeasurableSet.univ_pi [Countable δ] {t : ∀ i, Set (X i)} (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (Set.pi Set.univ t)` — use this for pi-sets over all indices.
- `ENNReal.ofReal_sub (a : ℝ) {b : ℝ} (hb : 0 ≤ b) : ENNReal.ofReal (a - b) = ENNReal.ofReal a - ENNReal.ofReal b` — note the first arg is explicit, second implicit.
- `ENNReal.ofReal_toReal {a : ℝ≥0∞} (h : a ≠ ⊤) : ENNReal.ofReal a.toReal = a` — use `.symm` to go from ENNReal to `ofReal p` form.
- `Measure.pi_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) : Measure.pi μ (Set.pi Set.univ s) = ∏ i, μ i (s i)` — IsProbabilityMeasure gives SigmaFinite automatically.
- `variance_sum_pi` requires explicit named args `(ι := ...) (μ := ...) (X := ...)` to avoid typeclass inference failure.
- `integral_comp_eval` for `∫ S, f(S i) ∂Measure.pi μ = ∫ f ∂μ i` — named args `(μ := ...) (i := ...)` recommended.
- `Measurable f` is defined as `∀ ⦃t⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)`, so apply it directly: `measurable_fst (hs : MeasurableSet s) : MeasurableSet (Prod.fst ⁻¹' s)`. Do NOT write `measurable_fst.measurableSet_preimage` (that name does not exist).
- `MeasurableSet.biUnion (hs : s.Countable) (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b)` — key lemma for proving measurability of C-existential sets with `Countable C`.
- When rewriting `{p | ∃ h ∈ C, P h p} = ⋃ h ∈ C, {p | P h p}`, use `show` to unfold `let` bindings first (simp won't unfold local `let` definitions), then `ext p; simp only [Set.mem_biUnion, Set.mem_setOf_eq]` to close the goal. Do NOT use `simp [Set.mem_iUnion]` — it reorders conjuncts in `∃ h ∈ C, ...` leaving an open goal.
- `tauto` in Lean 4 handles only propositional logic (no quantifiers). Use explicit `constructor; rintro ...; exact ...` for goals with ∃ and ∧ reordering.
- `∃ h ∈ C, P h` desugars to `∃ h, h ∈ C ∧ P h` (not `∃ h, ∃ _ : h ∈ C, P h`). However `p ∈ ⋃ h ∈ C, s h` unfolds to `∃ h, ∃ _ : h ∈ C, p ∈ s h`. Use `Set.mem_biUnion` to convert between these forms.
