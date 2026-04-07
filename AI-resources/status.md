# Formalization Status — PAC Learning Symmetrization (Lean 4)

Last updated: 2026-04-07

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

### `GhostSample.lean` — Event definitions and helper
- [x] `isBadHypothesis` — `ε ≤ trueError D h c`
- [x] `isConsistentWith` — zero empirical error on S₁
- [x] `hasManyErrors` — `≥ εm/2` errors on S₂
- [x] `EventA`, `EventB`
- [x] `eventB_implies_eventA`
- [x] `error_indicator_mean_ge` — `D {x | isError h c x} ≥ ε`

### `Symmetrization.lean` — Growth function and sample size algebra
- [x] `growthFunction` — `⨆ S, Nat.card (range (restrictToSample h S))`
- [x] `card_labelings_le_growthFunction`
- [x] `growthFunction_le_two_pow`
- [x] `sample_size_bound` — if `(2/ε)·(log Π + log(2/δ)) ≤ m·log 2` then `Pr[B] ≤ δ/2` *(depends on `symmetrization_bound`)*

### `Main.lean` — Sauer-Shelah pipeline and final theorem
- [x] `restrictionFamily` — finite set family encoding C's restrictions to a sample
- [x] `VC_dim` — `⨆ m S, vcDim (restrictionFamily C S)`
- [x] `card_restrictionFamily_eq`
- [x] `growthFunction_le_sauerShelah_sum` — uses Mathlib's `Finset.card_shatterer_le_sum_vcDim`
- [x] `sum_choose_le_pow` — `∑_{k≤d} C(n,k) ≤ (e·n/d)^d` (binomial theorem proof)
- [x] `sauer_shelah_bound` — `Π_C(2m) ≤ (2em/d)^d`
- [x] `pac_sample_complexity_bound` — final theorem *(structurally complete; chains all lemmas; depends on 4 sorries below)*

---

## In Progress / Currently Working On

None actively in progress right now. Next session should begin with `sampleMeasure_eq_prod`.

---

## Still To Do (4 sorries)

Priority order (easiest → hardest):

### 1. `GhostSample.lean:133` — `sampleMeasure_eq_prod`
```
(sampleMeasure D (2 * m)).map (fun S => (firstHalf S, secondHalf S)) =
(sampleMeasure D m).prod (sampleMeasure D m)
```
**What's needed:** Show that `Measure.pi (fun _ : Fin (2m) => D)` mapped through the
`Fin(2m) ≅ Fin(m) ⊕ Fin(m)` bijection equals the product of two `Measure.pi`s.
Likely approach: `MeasureTheory.Measure.pi_map_piEquiv` or `Measure.pi_prod`.

### 2. `GhostSample.lean:104` — `bernoulli_error_lower_bound`
```
ENNReal.ofReal (1/2) ≤ (sampleMeasure D m) {S₂ | hasManyErrors ε m h c S₂}
```
**What's needed:** Chebyshev's inequality on the sum of m iid Bernoulli(p) variables (p ≥ ε).
- Mean ≥ εm, Var ≤ m/4
- Chebyshev: P[errors < εm/2] ≤ 4/(εm) ≤ 1/2 (using m ≥ 8/ε)
Likely approach: `ProbabilityTheory.variance_le_of_...` or Mathlib's Chebyshev lemma.

### 3. `GhostSample.lean:149` — `ghost_sample_bound`
```
(sampleMeasure D (2*m)) {S | EventA C c D ε m S} ≤
2 * (sampleMeasure D (2*m)) {S | EventB C c D ε m S}
```
**What's needed:** Fubini / product measure disintegration.
- Use `sampleMeasure_eq_prod` to split 2m-sample as P₁ ⊗ P₂
- For any S₁ where EventA holds, use `bernoulli_error_lower_bound` to get P₂[B(S₁,·)] ≥ 1/2
- Integrate: P[B] ≥ (1/2)·P₁[A], so P[A] ≤ 2·P[B]
Likely approach: `MeasureTheory.lintegral_prod` (Fubini), `Measure.prod_apply`.

### 4. `Symmetrization.lean:87` — `symmetrization_bound`
```
(sampleMeasure D (2*m)) {S | EventB C c D ε m S} ≤
ENNReal.ofReal (growthFunction C (2*m) * (1/2)^(ε*m/2))
```
**What's needed:** Union bound over all (≤ growthFunction) labelings of the 2m-sample.
- For each labeling/hypothesis, the hypergeometric bound gives probability ≤ (1/2)^l ≤ (1/2)^{εm/2}
- Sum over at most growthFunction C (2m) labelings
Likely approach: `MeasureTheory.measure_iUnion_le` (union bound), conditioning on the 2m-sample.
This is the hardest sorry — may require a conditional measure / disintegration argument.

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
