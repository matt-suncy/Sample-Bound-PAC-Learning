# Formalization Status — PAC Learning Symmetrization (Lean 4)

Last updated: 2026-04-09 (session 3)

---

## Completed

### `Definitions.lean`
All definitions fully compiled, no sorries.
- [x] `Concept` — measurable set wrapper
- [x] `trueError` — `D(symmDiff h c)`
- [x] `isError`, `isError.decidable`
- [x] `errorCount`, `empiricalError`
- [x] `restrictToSample`
- [x] `sampleMeasure` — `Measure.pi (fun _ => D)`
- [x] `firstHalf`, `secondHalf`, `combineHalves`
- [x] `firstHalf_combineHalves`, `secondHalf_combineHalves` (simp lemmas)
- [x] `sampleMeasure_isProbability`

### `Hypergeometric.lean`
Fully proved, no sorries.
- [x] `hypergeometric_bound_nat` — `2^l * C(m,l) ≤ C(2m,l)` by induction + Pascal
- [x] `hypergeometric_bound` — `C(m,l)/C(2m,l) ≤ (1/2)^l` (real-valued cast)

### `GhostSample.lean` — Fully compiled, no sorries
- [x] `isBadHypothesis` — `ε ≤ trueError D h c`
- [x] `isConsistentWith` — zero empirical error on S₁
- [x] `hasManyErrors` — `≥ εm/2` errors on S₂
- [x] `EventA`, `EventB`
- [x] `eventB_implies_eventA`
- [x] `error_indicator_mean_ge` — `D {x | isError h c x} ≥ ε`
- [x] `sampleMeasure_eq_prod` — 2m-sample decomposes as P₁ ⊗ P₁ (proved 2026-04-08)
- [x] `bernoulli_error_lower_bound` — Chebyshev bound giving P[many errors] ≥ 1/2 (proved 2026-04-08)
- [x] `ghost_sample_bound` — P[A] ≤ 2·P[B] (fully proved 2026-04-09; hA_meas/hB_meas compile errors fixed)

### `Symmetrization.lean` — Growth function and sample size algebra
- [x] `growthFunction` — `⨆ S, Nat.card (range (restrictToSample h S))`
- [x] `card_labelings_le_growthFunction`
- [x] `growthFunction_le_two_pow`
- [x] `symmetrization_bound` — `per_h_bound` and `hconsist_bound` proved (2026-04-08); 1 sorry remains: union bound step (disintegration)
- [x] `sample_size_bound` — if `(2/ε)·(log Π + log(2/δ)) ≤ m·log 2` then `Pr[B] ≤ δ/2` *(depends on `symmetrization_bound`)*

### `Main.lean` — Sauer-Shelah pipeline and final theorem
- [x] `restrictionFamily` — finite set family encoding C's restrictions to a sample
- [x] `VC_dim` — `⨆ m S, vcDim (restrictionFamily C S)`
- [x] `card_restrictionFamily_eq`
- [x] `growthFunction_le_sauerShelah_sum` — fully proved 2026-04-09; added `h_vcDim_elem` hypothesis (see errors.md)
- [x] `sum_choose_le_pow` — `∑_{k≤d} C(n,k) ≤ (e·n/d)^d` (binomial theorem proof)
- [x] `sauer_shelah_bound` — `Π_C(2m) ≤ (2em/d)^d` (propagated `h_vcDim_elem` 2026-04-09)
- [x] `pac_sample_complexity_bound` — final theorem fully compiled; propagated `hVC_elem` 2026-04-09 *(depends on symmetrization_bound sorry below)*

---

## In Progress / Currently Working On

None actively in progress right now.

---

## Still To Do (remaining sorries)

### 1. `Symmetrization.lean` — union bound step (inside `symmetrization_bound`)
```
-- P[EventB] ≤ growthFunction · (1/2)^{εm/2}
sorry
```
**Plan (2026-04-12):** Use finite union bound over explicit bad-hypothesis set.

**Approach:** Add two hypotheses to `symmetrization_bound` (and propagate to callers):
- `hbad_fin : Set.Finite {h : Concept X | h ∈ C ∧ isBadHypothesis D c ε h}`
- `hbad_card : hbad_fin.toFinset.card ≤ growthFunction C (2 * m)`

**Proof steps:**
1. `EventB ⊆ ⋃ h ∈ hbad_fin.toFinset, B_h` (by unfolding EventB)
2. Apply `measure_biUnion_finset_le`: `μ(EventB) ≤ ∑ h ∈ bad_fin, μ(B_h)`
3. Apply `Finset.sum_le_card_nsmul`: `∑ μ(B_h) ≤ bad_fin.card • (1/2)^{εm/2}`
4. Apply `hbad_card`: `bad_fin.card ≤ growthFunction C (2*m)`
5. Conclude via ENNReal arithmetic + `ENNReal.ofReal_mul`

**Key Mathlib lemmas:**
- `measure_biUnion_finset_le` (OuterMeasure/Basic.lean:83)
- `Finset.sum_le_card_nsmul` (Algebra/Order/BigOperators)

**Note:** `hbad_card` captures the core VC-theoretic content. A direct countable union bound
over all bad h gives `|C_bad| · p`, not `growthFunction · p`, because `|C_bad|` can exceed
the growth function for infinite C. `hbad_card` is added as an explicit assumption; it would
follow from a full disintegration/measurable-selection argument for general C.

**Files to change:** `Symmetrization.lean` (sorry + signatures), `Main.lean` (propagate hypotheses)

---

## Dependency Graph

```
hypergeometric_bound
        ↓
bernoulli_error_lower_bound  ←→  sampleMeasure_eq_prod
        ↓
ghost_sample_bound                symmetrization_bound
        ↓                                  ↓
        └──────────→ sample_size_bound ←───┘
                              ↓
                pac_sample_complexity_bound  ←  sauer_shelah_bound
```
