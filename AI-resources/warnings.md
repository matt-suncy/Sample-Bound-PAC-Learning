# MAM Project - Warnings
Warnings as of April 13, 2026

## Definitions.lean
### Trivial
- 20: line character limit exceeded
- 74: simp argument unused
### Medium
- 63: automatically included section variable(s) unused in theorem
    - consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them
- 69: automatically included section variable(s) unused in theorem
    - consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them

## Symmetrization.lean
### Trivial
- 125: simp argument unused
- 155: simp argument unused
- 141: line character limit exceeded
- 286: line character limit exceeded
### Medium
- 11: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.

## Hypergeometric.lean
No issues!

## GhostSample.lean
### Trivial
- 82: simp argument unused
- 110: simp argument unused
- 123: simp argument unused
- 186: simp argument unused
- 294: line character limit exceeded
- 333: simp argument unused
- 424: simp argument unused
- 428: simp argument unused
- 455: simp argument unused
- 463: simp argument unused
- 475: simp argument unused
### Medium
- 9: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
- 86: modified the maxHeartbeat limit, in “set_option maxHeartbeats 800000” (outside theorems or lemmas)
### BAD
lemma bernoulli_error_lower_bound:
- 153: show tactic changed the goal
- 179: show tactic changed the goal

theorem ghost_sample_bound
- 344: show tactic changed the goal
- 450: show tactic changed the goal

## Main.lean
### Trivial
- 146: push_cast' tactic does nothing
### Medium
- 8: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
- 66: in statement for theorem growthFunction_le_sauerShelah_sum - unused variable (hypothesis) ‘hd’
- 198: in statement for theorem pac_sample_complexity_lower_bound - unused variable (hypothesis) ‘hδ1’