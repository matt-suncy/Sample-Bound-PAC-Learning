import MAMFinalProject.Definitions
import MAMFinalProject.Hypergeometric
import MAMFinalProject.GhostSample
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Real

variable {X : Type*} [MeasurableSpace X]
variable (C : Set (Concept X))
variable (c : Concept X)
variable (D : Measure X) [IsProbabilityMeasure D]
variable (ε δ : ℝ)
variable (m : ℕ)

/-- The growth function, bounding the number of possible labelings of a generic sample of size m. -/
opaque growthFunction (C : Set (Concept X)) (m : ℕ) : ℕ

/-- The combined union bound and hypergeometric bound. Shows that Pr[Event B] 
is bounded by the growth function times the permutation probability. -/
axiom symmetrization_bound
    (h_ε : ε > 0)
    (P : Measure (Fin (2 * m) → X)) [IsProbabilityMeasure P] :
    P {S | EventB m C c D ε S} ≤ ENNReal.ofReal ((growthFunction C (2 * m) : ℝ) * (1 / 2 : ℝ) ^ (ε * (m : ℝ) / 2))

/-- Solving for m gives the partial sample complexity bound. -/
axiom sample_size_bound
    (h_ε : ε > 0)
    (P : Measure (Fin (2 * m) → X)) [IsProbabilityMeasure P]
    (hm : m ≥ (2 / ε) * (log (growthFunction C (2 * m)) + log (2 / δ))) :
    P {S | EventB m C c D ε S} ≤ ENNReal.ofReal (δ / 2)
