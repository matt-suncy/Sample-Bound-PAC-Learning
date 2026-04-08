# Error Log — PAC Learning Lean 4 Formalization

Last updated: 2026-04-07

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

---

## Open / Unresolved Errors and Known Risks

### [RESOLVED] `sampleMeasure_eq_prod` — proved 2026-04-08
**File:** `GhostSample.lean`
**Resolution:** Composed two measure-preserving maps:
1. `(MeasurableEquiv.piCongrLeft (fun _ => X) f).symm` using `f = finSumFinEquiv.trans (Fin.castOrderIso h2m).toEquiv : Fin m ⊕ Fin m ≃ Fin (2*m)`
2. `MeasurableEquiv.sumPiEquivProdPi`
Key lemma: `Equiv.piCongrLeft_symm_apply (fun _ => X) f S j` (note: `P` and `e` are both explicit in the variable section — must pass both).
Function equality proved via `Prod.ext` + `funext i` + `simp only [firstHalf/secondHalf]` + `congr 1` (which closes by definitional equality of `Fin` values).

### [OPEN] `bernoulli_error_lower_bound` — Chebyshev in Mathlib4
**File:** `GhostSample.lean:104`
**Issue:** Need Chebyshev's inequality for a sum of iid Bernoulli indicators under `sampleMeasure D m` (which is `Measure.pi`). Mathlib has `ProbabilityTheory.meas_ge_le_chebyshev_div_sq` but connecting it to the sum-of-coordinates function over `Measure.pi` requires:
1. Defining the sum function `fun S => errorCount h c S` as a measurable function
2. Computing its expectation and variance under `Measure.pi`
3. Applying Chebyshev
**Risk (HIGH):** This is the most technically demanding sorry. May need `ProbabilityTheory.iIndepFun` to establish that coordinate projections are independent under `Measure.pi`, then use `Finset.sum` measurability and variance additivity. Several intermediate lemmas may be needed.

### [OPEN] `ghost_sample_bound` — Fubini / disintegration
**File:** `GhostSample.lean:149`
**Issue:** Need to integrate the function `fun S₁ => P₂ {S₂ | EventB(combineHalves S₁ S₂)}` against `P₁` and compare to `P₁ {S₁ | EventA S₁}`. Requires:
1. `sampleMeasure_eq_prod` to be proved first
2. Measurability of `{S | EventA ...}` and `{S | EventB ...}` (existential over `C`)
3. `MeasureTheory.lintegral_prod` or `Measure.prod_apply` for the Fubini step
**Risk (MEDIUM):** Measurability of `EventA`/`EventB` (existentials over possibly uncountable `C`) is non-trivial. May need to assume or add a `Countable C` hypothesis, or restrict to countably-generated concept classes.

### [OPEN] `symmetrization_bound` — union bound over labelings
**File:** `Symmetrization.lean:87`
**Issue:** The union bound `Pr[B] ≤ Π_C(2m) · (1/2)^{εm/2}` requires:
1. Conditioning on the 2m-sample S
2. For each of the (≤ growthFunction) distinct labelings of S, bounding the probability it falls in EventB by (1/2)^{εm/2}
3. Summing (union bound): `Measure.measure_iUnion_le` or `Finset.sum`-based estimate
**Risk (HIGH):** This requires a conditional measure argument (disintegration of `sampleMeasure D (2m)` over the 2m-sample). This is the most structurally complex sorry. One possible shortcut: work entirely in the "fixed sample" world and use `Measure.count` or a finset-level argument, but this may not typecheck cleanly with the existing `sampleMeasure` setup.

### [WATCH] Measurability of event sets
**Files:** `GhostSample.lean`, `Symmetrization.lean`
**Issue:** The sets `{S | EventA C c D ε m S}` and `{S | EventB C c D ε m S}` involve existential quantification over `h ∈ C`. For these to be measurable (needed for `sampleMeasure` to apply), either:
- `C` must be countable (so the union over `h ∈ C` is countable), or
- A measurable selection argument is needed.
**Status:** Currently no measurability hypothesis on `C` is assumed. This may cause issues when trying to apply measure theory lemmas that require measurable sets. **Keep this in mind for all four remaining sorries.**

---

## Notes on Naming / API Gotchas

- Mathlib uses `Finset.Iic d` for `{0, 1, ..., d}` (not `Finset.range (d+1)`), but both work.
- `Nat.card` vs `Finset.card`: `growthFunction` uses `Nat.card` on a `Set.range`; the Sauer-Shelah bound uses `Finset.card` on a `Finset`. The bridge is `card_restrictionFamily_eq`.
- `IsProbabilityMeasure` is an instance, not a hypothesis in the usual sense — it needs to be in scope as `[IsProbabilityMeasure D]`.
- `ENNReal.ofReal` is needed whenever converting `ℝ`-valued probability bounds to `ENNReal` (the type of `Measure.apply`).
- `Real.rpow` vs `HPow.hPow`: `(x : ℝ) ^ (y : ℝ)` uses `rpow`; `(x : ℝ) ^ (n : ℕ)` uses `HPow`. Be careful in the `symmetrization_bound` where `ε * m / 2 : ℝ` appears as an exponent.
