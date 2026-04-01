# Lean 4 Formalization Plan: The Symmetrization Argument in PAC Learning

This document outlines the requirements and architectural steps for formalizing the Vapnik-Chervonenkis Symmetrization Argument (also known as the Double Sample Trick) using Lean 4 and Mathlib4.

## 1. Ultimate Goal
The objective is to formalize the sample complexity upper bound for PAC learning. Specifically, you must prove that for a concept class $\mathcal{C}$ and a target concept $c$, given a dataset $S_1$ of $m$ examples drawn from $EX(c, \mathcal{D})$, if the sample size $m$ satisfies both $m \ge \frac{8}{\epsilon}$ and $m \ge \frac{2}{\epsilon}(\log(\Pi_\mathcal{C}(2m)) + \log\frac{2}{\delta})$, then with probability at least $1-\delta$, all "bad" hypotheses $h \in \mathcal{C}$ (where $error(h) \ge \epsilon$) are inconsistent with the dataset. 

By applying the bound on the growth function $\Pi_\mathcal{C}(2m)$, this eventually simplifies to the overarching theorem that $m \ge c_0(\frac{1}{\epsilon}\log\frac{1}{\delta} + \frac{d}{\epsilon}\log\frac{1}{\epsilon})$ examples are sufficient.

## 2. Modular Lemmas
Do not attempt to prove the main theorem in a single declaration. Break the proof down into the following specific, isolated lemmas:

* **The Ghost Sample Lemma (Conditional Probability):**
  * Define **Event A** as the event that some bad $h \in \mathcal{C}$ gets all of $S_1$ right. 
  * Define **Event B** as the event that some $h \in \mathcal{C}$ gets all of $S_1$ right AND is wrong on at least $\frac{\epsilon}{2}m$ elements of an independent ghost sample $S_2$.
  * Formalize the probability relationship: $Pr[B] \ge Pr[A \cap B] = Pr[A] \cdot Pr[B|A]$. 
  * Prove that $Pr[B|A] \ge \frac{1}{2}$. This holds because if A holds, a bad hypothesis $h^*$ makes $\ge \epsilon m$ errors on average; for $m \ge \frac{8}{\epsilon}$, the probability it makes fewer than $\frac{\epsilon}{2}m$ mistakes on $S_2$ is $\le \frac{1}{2}$.
  * Conclude that $Pr[A] \le 2Pr[B]$.

* **The Hypergeometric Symmetrization Bound:**
  * Consider a combined fixed sample $S$ of $2m$ instances.
  * Fix a labeling of $S$ where a hypothesis makes $l \ge \frac{\epsilon m}{2}$ errors.
  * Formalize the combinatorial probability that a random split of $S$ into $S_1$ and $S_2$ places all $l$ errors entirely into $S_2$. 
  * Prove the inequality for choosing $l$ items out of $2m$ to fall in the second half: $\frac{\binom{m}{l}}{\binom{2m}{l}} = \frac{m(m-1)...(m-l+1)}{2m(2m-1)...(2m-l+1)} \le \frac{1}{2^l}$. 
  * Conclude this probability is bounded by $2^{-\frac{\epsilon m}{2}}$.

* **The Union Bound Synthesis:**
  * Conditioned on the $2m$ sample, apply a union bound over all possible labelings projected onto $S$, which is bounded by the growth function $\Pi_\mathcal{C}(2m)$. 
  * Combine this with the hypergeometric bound to establish that $Pr[B] \le \Pi_\mathcal{C}(2m) \cdot 2^{-\frac{\epsilon m}{2}}$.
  * Setting this $\le \frac{\delta}{2}$ requires $m \ge \frac{2}{\epsilon}(\log(\Pi_\mathcal{C}(2m)) + \log\frac{2}{\delta})$.

## 3. Measure Theory Setup
The probability theory must be strictly grounded in Mathlib4's measure theory library.
* Define the instance space as a measurable space $X$ with a probability measure $\mathcal{D}$.
* Concepts and hypotheses should be represented as measurable sets (or measurable boolean indicator functions) over $X$.
* Instead of defining $S_1$ and $S_2$ as separate draws initially, you must formalize the Symmetrization equivalent: Draw a sequence $S$ of $2m$ independent and identically distributed (iid) random variables from $\mathcal{D}$, and then define $S_1$ and $S_2$ as a random, uniform partition of $S$. You will need to leverage Mathlib's definitions for independent random variables (`ProbabilityTheory.IndepFun`).

## 4. Mathlib Context (Lean 4)
You are operating strictly in **Lean 4** and utilizing the **Mathlib4** library.
* Mathlib4 already contains a formalization of the Sauer-Shelah Lemma, which bounds the growth function: $\Pi_\mathcal{C}(m) \le \sum_{i=0}^d \binom{m}{i} \le (\frac{em}{d})^d$. Do not reinvent this combinatorial bound.
* Your task is to build the necessary computational learning theory, probability and symmetrization architecture, and then seamlessly invoke Mathlib's existing Sauer-Shelah result to bound $\Pi_\mathcal{C}(2m) \le (\frac{2em}{d})^d$ to complete the final algebraic substitution required for the ultimate sample complexity bound.

## 5. Watch for Syntax Hallucinations
You must write idiomatic Lean 4 code.
* **Do not use Lean 3 syntax.** For example, use `fun x \mapsto` instead of `\lambda x,`. Use Lean 4's `set_option` directives if necessary, but avoid deprecated tactics.
* **Strict API Adherence:** Rely exclusively on existing Mathlib4 structures for `MeasureSpace`, `ProbabilityMeasure`, and combinatorial functions (`Nat.choose`). Do not hallucinate intermediate measure-theoretic helper lemmas; if you need a standard property of iid variables or union bounds, search for the correct Mathlib4 theorem name.