# Hex multivariate polynomial Horner proof

## Accomplished

- Proved that `Mono.powBySq` agrees with ordinary semiring exponentiation.
- Proved that Horner collection and sorting preserve the input terms, that
  each group contains exactly terms with its exponent, and that sorting
  produces descending exponent groups.
- Proved the sparse Horner fold equals its weighted term sum.
- Proved recursive fixed-variable-order Horner evaluation equals direct term
  evaluation and discharged `eval₂Horner_eq` without axioms or sorries.
- Added kernel-reduction tests for repeated squaring and a sparse polynomial
  with exponent gaps.
- Obtained an independent Claude Opus review, which found no soundness blocker.
- Strengthened `eval₂Horner` and `evalHorner` to commutative semirings, factored
  the shared sparse-Horner step, documented its descending-order contract, and
  added zero-variable and nonzero-trailing-exponent kernel tests.
- Updated the SPEC to record the direct-versus-Horner typeclass distinction and
  its factor-reordering reason.
- Obtained a final post-fix Claude Opus review, which found no blocker.
- Audited `powBySq_eq_pow`, `eval₂Horner_eq`, and `evalHorner_eq` with
  `#print axioms`; they depend only on Lean's standard
  quotient/extensionality axioms and not `sorryAx`.

## Current frontier

- Nine implementation proof obligations remain: the three monomial-order
  instances, the polynomial power recurrence, partial evaluation versus
  substitution, and four recursive-view coefficient/round-trip laws.
- PR #9084 merged after its single CI job completed successfully.

## Next step

- Rebase this follow-up onto `main`, rerun validation, and open the next
  intermediate PR.
- Continue with the independent recursive-view coefficient laws while that PR
  runs.

## Blockers

- None.
