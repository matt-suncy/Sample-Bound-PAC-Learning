import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set

variable {X : Type*} [MeasurableSpace X]

/-!
# Core Definitions for PAC Learning Formalization

Instance space: measurable space X with probability measure D.
Concepts and hypotheses: measurable subsets of X.
-/

/-- A concept or hypothesis is a measurable set over X. -/
def Concept (X : Type*) [MeasurableSpace X] := { s : Set X // MeasurableSet s }

/-- The true error of h relative to target c under D: the measure of points where h and c disagree. -/
noncomputable def trueError (D : Measure X) (h c : Concept X) : ENNReal :=
  D (symmDiff h.val c.val)

/-- Point x is a classification error: h and c disagree on x. -/
def isError (h c : Concept X) (x : X) : Prop :=
  (x ∈ h.val) ≠ (x ∈ c.val)

/-- Classical decidability for the error predicate (needed for Finset.filter). -/
noncomputable instance isError.decidable {h c : Concept X} :
    DecidablePred (isError h c) :=
  fun _ => Classical.propDecidable _

/-- The number of indices i ∈ Fin m where h and c disagree on S i. -/
noncomputable def errorCount {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℕ :=
  (Finset.univ.filter fun i => isError h c (S i)).card

/-- The empirical error rate of h on c for sample S. -/
noncomputable def empiricalError {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℝ :=
  (errorCount h c S : ℝ) / m

/-- The restriction of h to sample S: the set of indices i where S i ∈ h. -/
noncomputable def restrictToSample {m : ℕ} (h : Concept X) (S : Fin m → X) : Finset (Fin m) :=
  letI : DecidablePred (fun i : Fin m => S i ∈ h.val) := fun _ => Classical.propDecidable _
  Finset.univ.filter fun i => S i ∈ h.val

/-- The iid product measure: m independent draws from D. -/
noncomputable def sampleMeasure (D : Measure X) (m : ℕ) : Measure (Fin m → X) :=
  Measure.pi (fun _ : Fin m => D)

/-- The first half of a 2m-sample (indices 0 to m-1). -/
def firstHalf {m : ℕ} (S : Fin (2 * m) → X) : Fin m → X :=
  fun i => S ⟨i.val, by omega⟩

/-- The second half of a 2m-sample (indices m to 2m-1). -/
def secondHalf {m : ℕ} (S : Fin (2 * m) → X) : Fin m → X :=
  fun i => S ⟨m + i.val, by omega⟩

/-- Combine two m-samples into a 2m-sample (first half = S₁, second half = S₂). -/
def combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) : Fin (2 * m) → X :=
  fun i => if h : i.val < m then S₁ ⟨i.val, h⟩ else S₂ ⟨i.val - m, by omega⟩

@[simp]
lemma firstHalf_combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) :
    firstHalf (combineHalves S₁ S₂) = S₁ := by
  funext i
  simp only [firstHalf, combineHalves, dif_pos i.isLt]

@[simp]
lemma secondHalf_combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) :
    secondHalf (combineHalves S₁ S₂) = S₂ := by
  funext i
  simp only [secondHalf, combineHalves]
  have hlt : ¬ (m + i.val < m) := by omega
  rw [dif_neg hlt]
  exact congrArg S₂ (Fin.ext (by simp [Nat.add_sub_cancel_left]))

/-- sampleMeasure is a probability measure when D is. -/
instance sampleMeasure_isProbability (D : Measure X) [IsProbabilityMeasure D] (m : ℕ) :
    IsProbabilityMeasure (sampleMeasure D m) := by
  unfold sampleMeasure
  infer_instance
