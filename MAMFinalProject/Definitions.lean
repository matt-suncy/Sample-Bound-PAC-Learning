import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set

variable {X : Type*} [MeasurableSpace X]

-- A concept or hypothesis is represented as a measurable set over X.
def Concept (X : Type*) [MeasurableSpace X] := { s : Set X // MeasurableSet s }

/-- The error of a hypothesis `h` with respect to a target concept `c` under probability measure `D`. 
It is defined as the measure of the symmetric difference. -/
noncomputable def trueError (D : Measure X) (h c : Concept X) : ENNReal :=
  D (symmDiff h.val c.val)

/-- The property that an instance `x` is misclassified by `h` relative to `c`. -/
def isError (h c : Concept X) (x : X) : Prop :=
  (x ∈ h.val) ≠ (x ∈ c.val)

/-- The empirical error of a hypothesis `h` on a sample sequence `S` of size `m`. -/
opaque empiricalError {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℝ
