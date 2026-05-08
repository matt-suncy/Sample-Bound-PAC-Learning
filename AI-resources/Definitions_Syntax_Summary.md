# Lean 4 Syntax and Logic Summary: `Definitions.lean`

This document provides a plain-language explanation of the Lean 4 syntax, types, and logic used in the `Definitions.lean` file of the PAC Learning Formalization project.

## 1. General Lean 4 Concepts

*   **`variable {X : Type*} [MeasurableSpace X]`**: This line declares `X` as a generic type (think of it as the set of all possible instances, like images or vectors). `Type*` just means it can be a type in any universe. The bracket notation `[MeasurableSpace X]` tells Lean to automatically assume that `X` is equipped with a probability/measure theory structure, allowing us to define probabilities over subsets of `X`.
*   **`def` / `noncomputable def`**: A `def` provides a concrete, executable definition. When a definition relies on strictly mathematical concepts (like real numbers, probabilities, or infinite sets) that a computer cannot literally "run" or evaluate in finite time, Lean requires us to mark it as `noncomputable def`.
*   **`lemma`**: A lemma is exactly like a theorem; it is a mathematical statement that requires a proof. In Lean, we use `lemma` for smaller helper theorems and `theorem` for major results.
*   **`Prop`**: The type of logical propositions. If something has type `Prop`, it is a statement that is mathematically either True or False.
*   **`@[simp]`**: This attribute tells Lean's built-in `simp` (simplifier) tactic to automatically use this lemma as a rewrite rule in future proofs.

## 2. Core Definitions line-by-line

### `Concept`
```lean
def Concept (X : Type*) [MeasurableSpace X] := { s : Set X // MeasurableSet s }
```
*   **`Set X`**: A subset of the instance space `X` (e.g., all images of cats).
*   **`{ ... // ... }` (Subtype)**: Double slashes define a *Subtype*. It pairs some mathematical object with a proof that it satisfies a specific property. Here, `Concept` is not just *any* subset of `X`, but specifically a subset paired with a guarantee (`MeasurableSet s`) that we can compute its probability. 
*   **`.val`**: Later in the file, you see `h.val` and `c.val`. Because `h` is a Subtype (a set paired with a proof), `.val` extracts just the underlying set so we can do operations on it.

### `trueError`
```lean
noncomputable def trueError (D : Measure X) (h c : Concept X) : ENNReal :=
  D (symmDiff h.val c.val)
```
*   **`Measure X`**: A mathematical function `D` that assigns probabilities/sizes to subsets of `X`.
*   **`ENNReal`**: The Extended Non-Negative Reals. Measure theory naturally deals with probabilities ranging from $0$ to $\infty$ (including infinity), so Lean uses `ENNReal` instead of standard `ℝ` for the output of measures.
*   **`symmDiff`**: The symmetric difference of two sets ($A \triangle B$). It represents the set of elements where hypotheses `h` and `c` disagree (an element is in `h` or `c`, but not both).

### `isError` and Decidability
```lean
def isError (h c : Concept X) (x : X) : Prop :=
  (x ∈ h.val) ≠ (x ∈ c.val)
```
*   This determines if `h` makes an error on a specific point `x` relative to `c`. The `≠` on propositions acts as an exclusive-OR (XOR).
*   **`DecidablePred` / `instance`**: By default, Lean doesn't assume you can always calculate whether a `Prop` is true or false. To use functions that "filter" or "count" elements (which algorithms require), Lean demands a proof of "decidability." The `isError.decidable` instance uses `Classical.propDecidable` to force Lean to accept that every error is either True or False analytically, sidestepping the need for a computable algorithm.

### `errorCount` and Vectors
```lean
noncomputable def errorCount {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℕ :=
  (Finset.univ.filter fun i => isError h c (S i)).card
```
*   **`Fin m → X`**: This is Lean's way of representing an array or vector of size `m` with elements of type `X`. `Fin m` is the type of natural numbers strictly less than `m` (e.g., $0, 1, ..., m-1$). A function from indices `Fin m` to `X` is exactly a sample dataset $S$.
*   **`Finset.univ.filter`**: Takes the "universe" of all indices from $0$ to $m-1$ and filters out only the ones where `isError` evaluates to true.
*   **`.card`**: Computes the cardinality (count/size) of that filtered set, returning a natural number `ℕ`.

### `empiricalError`
```lean
noncomputable def empiricalError {m : ℕ} (h c : Concept X) (S : Fin m → X) : ℝ :=
  (errorCount h c S : ℝ) / m
```
*   **`( ... : ℝ)` (Type Coercion)**: Since `errorCount` outputs a natural number `ℕ`, and `m` is a natural number, division would default to integer floor-division (e.g., $1/2 = 0$). Adding `: ℝ` tells Lean to "cast" the integer into a continuous Real number so division behaves normally.

### `restrictToSample`
```lean
noncomputable def restrictToSample {m : ℕ} (h : Concept X) (S : Fin m → X) : Finset (Fin m) :=
  letI : DecidablePred (fun i : Fin m => S i ∈ h.val) := fun _ => Classical.propDecidable _
  Finset.univ.filter fun i => S i ∈ h.val
```
*   **`letI`**: A localized `instance` declaration. It temporarily tells Lean within this specific function "pretend we clearly know how to compute if $S[i]$ is inside `h`", which allows the `.filter` command on the next line to work.

### `sampleMeasure`
```lean
noncomputable def sampleMeasure (D : Measure X) (m : ℕ) : Measure (Fin m → X) :=
  Measure.pi (fun _ : Fin m => D)
```
*   **`Measure.pi`**: This is the formal mathematical construction of a Product Measure. If you have $m$ independent draws from the same distribution `D`, the joint probability distribution over the entire dataset of size $m$ is given by `Measure.pi`.

## 3. Data Shuffling proofs (Halves & Combines)

The definitions `firstHalf`, `secondHalf`, and `combineHalves` split a $2m$ sized dataset into two datasets of size $m$, or stitch them together.

### The `by omega` Tactic
```lean
def firstHalf {m : ℕ} (S : Fin (2 * m) → X) : Fin m → X :=
  fun i => S ⟨i.val, by omega⟩
```
*   `S` expects an index strictly less than $2m$. The function is given `i`, which is of type `Fin m` (meaning $i < m$). 
*   **`⟨ ... , ... ⟩`**: The constructor for a Subtype (similar to the `//` notation earlier). It provides the raw value (`i.val`) and a proof that the value fits the requirement.
*   **`by omega`**: A powerful Lean numeric automation tactic. It proves linear arithmetic goals automatically. Here, if Lean needs a proof that $i < 2m$, the fact that $i < m$ makes it completely obvious. `omega` connects those dots implicitly.

### Proving Properties (`firstHalf_combineHalves`)
```lean
@[simp]
lemma firstHalf_combineHalves {m : ℕ} (S₁ S₂ : Fin m → X) :
    firstHalf (combineHalves S₁ S₂) = S₁ := by
  funext i
  simp only [firstHalf, combineHalves, dif_pos i.isLt]
```
*   **`funext i`**: Extensionality for functions. To prove two functions are exactly equal, you just need to prove their outputs are equal for any arbitrary input `i`.
*   **`simp only [...]`**: Tells the simplifier to unfold the definitions of `firstHalf` and `combineHalves`.
*   **`dif_pos`**: In `combineHalves`, there's an `if h : i.val < m then ... else ...` conditional. Since `i` is from `S₁`, we know `i` is strictly less than $m$. `dif_pos i.isLt` resolves the if/else statement strictly to the positive (then) branch conceptually.
