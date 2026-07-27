# HexNumberField reduced fixed-field arithmetic

## Accomplished

- Added one canonical rational-polynomial reduction boundary modulo the cast
  defining polynomial.
- Implemented coordinate equality and zero, zero/one, addition, subtraction,
  negation, multiplication, and rational scalar action through reduced
  representatives.
- Implemented checked-irreducible inversion from polynomial extended gcd,
  including gcd-scalar normalization and `0⁻¹ = 0`, plus division.
- Added compiled regressions for reduction, multiplication, nontrivial
  inversion, and zero inversion in `ℚ[X]/(X²-2)`.
- Built `HexNumberField` and passed DAG, copyright, line-count,
  forbidden-form, and whitespace checks.

## Current frontier

The algebraic fixed-field operations are executable and use canonical reduced
coordinates. One propositional degree-bound obligation remains explicit. The
threaded approximation API still needs a reusable rational-polynomial ball
evaluator.

An independent review of the parent resultant stack found a genuine
positive-characteristic discriminant formal-degree bug; work here is
checkpointed while that parent contract is repaired.

## Next step

Repair the parent discriminant contract and executable correction, propagate
it through the stack, then publish this fixed-field milestone and implement
rational-polynomial ball evaluation.

## Blockers

No local arithmetic blocker. Publication waits only for the parent resultant
repair to be incorporated into the stacked base.
