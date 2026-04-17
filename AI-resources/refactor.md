# Refactor Plan

## Guidelines
- Never mix pure algebraic manipulation with domain-specific structures. If you have a calc block proving an inequality, abstract the specific terms (like Nat.choose or empiricalError) into generic variables (like a and b) and extract it as a standalone algebraic lemma.
- Isolate Side-Goals: Extract multi-step proofs of positivity, non-negativity, or index bounds into their own lemmas. Your main theorems should read like a high-level assembly of logical steps, not a graveyard of positivity and omega wrestling matches.
- Bridge the Casting Gap: Create dedicated, atomic helper lemmas whose sole purpose is to cast bounds from one type to another (e.g., moving a combinatorial bound from ℕ to ℝ).
- Keep lemmas/theorems short and focused. If a proof requires more than/ 3-4 distinct logical steps, consider whether it can be decomposed into smaller, reusable lemmas.

## Lemmas that are ready for refactroing
Hypgergeometric.lean:
- *everything*

