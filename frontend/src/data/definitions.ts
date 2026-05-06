// All `def` / `noncomputable def` items from all Lean files, including private ones.
// Update leanCode strings here when the Lean formalization changes.
// PLACEHOLDER: description strings should be replaced with precise natural-language definitions.

export interface DefinitionEntry {
  id: string
  name: string           // human-readable bold name
  description: string    // PLACEHOLDER — fill in manually
  leanCode: string       // full declaration
  file: string
  isPrivate?: boolean
}

export const definitions: DefinitionEntry[] = [
  // ── Definitions.lean ──────────────────────────────────────────────────────
  {
    id: 'Concept',
    name: 'Concept',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'A concept or hypothesis: a measurable subset $C \\subseteq X$ of the instance space. Point $x$ is classified positive iff $x \\in C$.',
    leanCode:
`def Concept (X : Type*) [MeasurableSpace X] := { s : Set X // MeasurableSet s }`,
  },
  {
    id: 'trueError',
    name: 'True Error',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'The true error $\\mathrm{error}_{\\mathcal{D}}(h,c) = \\mathcal{D}(h \\triangle c)$: the probability under $\\mathcal{D}$ that $h$ and $c$ classify a random point differently.',
    leanCode:
`noncomputable def trueError (D : Measure X) (h c : Concept X) : ENNReal :=
  D (symmDiff h.val c.val)`,
  },
  {
    id: 'isError',
    name: 'Is Error',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'Point $x$ is a classification error if $h$ and $c$ disagree: $(x \\in h) \\neq (x \\in c)$, equivalently $x \\in h \\triangle c$.',
    leanCode:
`def isError (h c : Concept X) (x : X) : Prop :=
  (x ∈ h.val) ≠ (x ∈ c.val)`,
  },
  {
    id: 'isError.decidable',
    name: 'Is Error (Decidable)',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'Classical decidability for the predicate $\\texttt{isError}(h,c,\\cdot)$. Required to use $\\texttt{Finset.filter}$ when counting errors over a finite sample.',
    leanCode:
`noncomputable instance isError.decidable {h c : Concept X} :
    DecidablePred (isError h c) :=
  fun _ => Classical.propDecidable _`,
  },
  {
    id: 'errorCount',
    name: 'Error Count',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'The empirical error count: $|\\{i \\in [m] : x_i \\in h \\triangle c\\}|$. The finite-sample analogue of $\\mathrm{error}_{\\mathcal{D}}(h,c)$.',
    leanCode:
`noncomputable def errorCount {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℕ :=
  (Finset.univ.filter fun i => isError h c (S i)).card`,
  },
  {
    id: 'empiricalError',
    name: 'Empirical Error',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'The empirical error rate $\\frac{1}{m}\\sum_{i=1}^m \\mathbf{1}[x_i \\in h \\triangle c]$. The fraction of training points where $h$ disagrees with $c$.',
    leanCode:
`noncomputable def empiricalError {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℝ :=
  (errorCount h c S : ℝ) / m`,
  },
  {
    id: 'restrictToSample',
    name: 'Restrict to Sample',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'The labeling of $S$ induced by $h$: $\\{i \\in [m] : x_i \\in h\\} \\subseteq [m]$. Two hypotheses are equivalent on $S$ iff they produce the same labeling.',
    leanCode:
`noncomputable def restrictToSample {m : ℕ} (h : Concept X) (S : Fin m → X) : Finset (Fin m) :=
  letI : DecidablePred (fun i : Fin m => S i ∈ h.val) := fun _ => Classical.propDecidable _
  Finset.univ.filter fun i => S i ∈ h.val`,
  },
  {
    id: 'sampleMeasure',
    name: 'Sample Measure',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'The i.i.d. product measure $\\mathcal{D}^m$ over $X^m$, modeling $m$ independent draws from $\\mathcal{D}$. Almost all probability statements in the proof are over this measure.',
    leanCode:
`noncomputable def sampleMeasure (D : Measure X) (m : ℕ) : Measure (Fin m → X) :=
  Measure.pi (fun _ : Fin m => D)`,
  },
  {
    id: 'firstHalf',
    name: 'First Half',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'Extracts the first $m$ points of a $2m$-sample: $S_1 = (x_0, \\ldots, x_{m-1})$. The "training" half seen by the learner.',
    leanCode:
`def firstHalf {m : ℕ} (S : Fin (2 * m) → X) : Fin m → X :=
  fun i => S ⟨i.val, by omega⟩`,
  },
  {
    id: 'secondHalf',
    name: 'Second Half',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'Extracts the last $m$ points of a $2m$-sample: $S_2 = (x_m, \\ldots, x_{2m-1})$. The ghost half — never seen by the learner, used to witness that bad hypotheses make many errors.',
    leanCode:
`def secondHalf {m : ℕ} (S : Fin (2 * m) → X) : Fin m → X :=
  fun i => S ⟨m + i.val, by omega⟩`,
  },
  {
    id: 'combineHalves',
    name: 'Combine Halves',
    file: 'Definitions.lean',
    // PLACEHOLDER:
    description: 'Concatenates $S_1, S_2 \\in X^m$ into a $2m$-sample. Left inverse of the $(\\mathrm{firstHalf}, \\mathrm{secondHalf})$ split.',
    leanCode:
`def combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) : Fin (2 * m) → X :=
  fun i => if h : i.val < m then S₁ ⟨i.val, h⟩ else S₂ ⟨i.val - m, by omega⟩`,
  },

  // ── GhostSample.lean ──────────────────────────────────────────────────────
  {
    id: 'isBadHypothesis',
    name: 'Is Bad Hypothesis',
    file: 'GhostSample.lean',
    // PLACEHOLDER:
    description: '$h$ is "bad" if $\\mathrm{error}_{\\mathcal{D}}(h,c) \\geq \\varepsilon$. These hypotheses generalize poorly but may appear consistent on a small training sample.',
    leanCode:
`def isBadHypothesis (D : Measure X) [IsProbabilityMeasure D] (c : Concept X) (ε : ℝ)
    (h : Concept X) : Prop :=
  ε ≤ (trueError D h c).toReal`,
  },
  {
    id: 'isConsistentWith',
    name: 'Is Consistent With',
    file: 'GhostSample.lean',
    // PLACEHOLDER:
    description: '$h$ is consistent with $S_1$ if $\\forall i\\in[m],\\ x_i \\notin h \\triangle c$ (zero empirical error on $S_1$). A learner outputting $h$ sees no training mistakes.',
    leanCode:
`def isConsistentWith (h c : Concept X) {m : ℕ} (S₁ : Fin m → X) : Prop :=
  ∀ i : Fin m, ¬ isError h c (S₁ i)`,
  },
  {
    id: 'hasManyErrors',
    name: 'Has Many Errors',
    file: 'GhostSample.lean',
    // PLACEHOLDER:
    description: '$h$ makes at least $\\varepsilon m/2$ errors on $S_2$: $\\sum_{i=1}^m \\mathbf{1}[x_i \\in h \\triangle c] \\geq \\varepsilon m/2$. The condition that lets us "catch" a bad hypothesis using the ghost half.',
    leanCode:
`def hasManyErrors (ε : ℝ) (m : ℕ) (h c : Concept X) (S₂ : Fin m → X) : Prop :=
  ε * m / 2 ≤ errorCount h c S₂`,
  },
  {
    id: 'EventA',
    name: 'Event A',
    file: 'GhostSample.lean',
    // PLACEHOLDER:
    description: '$A = \\{\\exists h \\in \\mathcal{C}: \\mathrm{error}(h)\\geq\\varepsilon \\text{ and } h \\text{ consistent with } S_1\\}$. The event we ultimately bound — a bad hypothesis that looks consistent to the learner.',
    leanCode:
`def EventA (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c (firstHalf S)`,
  },
  {
    id: 'EventB',
    name: 'Event B',
    file: 'GhostSample.lean',
    // PLACEHOLDER:
    description: '$B \\Rightarrow A$: as $A$, but also requiring $\\geq \\varepsilon m/2$ errors on $S_2$. $B$ is easier to bound via the union bound over labelings and the Bernoulli error lower bound.',
    leanCode:
`def EventB (C : Set (Concept X)) (c : Concept X) (D : Measure X) [IsProbabilityMeasure D]
    (ε : ℝ) (m : ℕ) (S : Fin (2 * m) → X) : Prop :=
  ∃ h ∈ C, isBadHypothesis D c ε h ∧ isConsistentWith h c (firstHalf S)
           ∧ hasManyErrors ε m h c (secondHalf S)`,
  },
  {
    id: 'errIndicator',
    name: 'Error Indicator',
    file: 'GhostSample.lean',
    isPrivate: true,
    // PLACEHOLDER:
    description: '(Private) The $\\{0,1\\}$-valued indicator $\\mathbf{1}[\\mathrm{isError}(h,c,x)]$. Converting the Boolean predicate to a real-valued function enables computing means ($= p$) and variances ($\\leq p$) via Mathlib\'s integral machinery.',
    leanCode:
`private noncomputable def errIndicator (h c : Concept X) : X → ℝ :=
  fun x => if isError h c x then 1 else 0`,
  },

  // ── Symmetrization.lean ───────────────────────────────────────────────────
  {
    id: 'growthFunction',
    name: 'Growth Function',
    file: 'Symmetrization.lean',
    // PLACEHOLDER:
    description: 'The growth function $\\Pi_{\\mathcal{C}}(m) = \\sup_{x_1,\\ldots,x_m}|\\{h\\cap\\{x_1,\\ldots,x_m\\}: h\\in\\mathcal{C}\\}|$. The maximum number of distinct labelings of any $m$-point sample. Sauer-Shelah bounds this by $(em/d)^d$.',
    leanCode:
`noncomputable def growthFunction (C : Set (Concept X)) (m : ℕ) : ℕ :=
  ⨆ S : Fin m → X, Nat.card (Set.range fun h : C => restrictToSample h.val S)`,
  },

  // ── Main.lean ─────────────────────────────────────────────────────────────
  {
    id: 'restrictionFamily',
    name: 'Restriction Family',
    file: 'Main.lean',
    // PLACEHOLDER:
    description: 'The labeling family $\\{h|_S : h\\in\\mathcal{C}\\}$ of $\\mathcal{C}$ restricted to sample $S$, encoded as a $\\texttt{Finset}$ so that Mathlib\'s $\\texttt{card\\_shatterer\\_le\\_sum\\_vcDim}$ (Sauer-Shelah) applies directly.',
    leanCode:
`noncomputable def restrictionFamily (C : Set (Concept X)) {m : ℕ} (S : Fin m → X) :
    Finset (Finset (Fin m)) :=
  (Set.range fun h : C => restrictToSample h.val S).toFinset`,
  },
  {
    id: 'VC_dim',
    name: 'VC Dimension',
    file: 'Main.lean',
    // PLACEHOLDER:
    description: '$d = \\mathrm{VCdim}(\\mathcal{C}) = \\sup_m\\sup_S\\,\\mathrm{vcDim}(\\mathcal{C}|_S)$. The complexity parameter that determines sample complexity: $m = O\\!\\left(\\frac{d}{\\varepsilon}\\log\\frac{1}{\\varepsilon}+\\frac{1}{\\varepsilon}\\log\\frac{1}{\\delta}\\right)$ suffices.',
    leanCode:
`noncomputable def VC_dim (C : Set (Concept X)) : ℕ :=
  ⨆ (m : ℕ) (S : Fin m → X), (restrictionFamily C S).vcDim`,
  },
]
