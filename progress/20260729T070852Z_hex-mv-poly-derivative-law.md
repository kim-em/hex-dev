# Hex multivariate polynomial derivative law

## Accomplished

- Proved the componentwise interaction between `predAt` and `Mono.succAt`.
- Proved `coeff_derivative` by reducing the derivative fold to the unique
  successor monomial in the canonical term list.
- Rebuilt `HexMvPoly.Structural` successfully after each proof step.
- Confirmed the independently reviewed SPEC follow-up merged as PR #9075.

## Current frontier

- The Mathlib-free core has 11 remaining `sorry` obligations: three named
  monomial orders, multiplication and power coefficients, Horner evaluation,
  partial evaluation as substitution, and four recursive-view laws.

## Next step

- Rebase the implementation commits onto the merged SPEC and publish the core
  milestone for CI and independent review.
- Continue with conformance scaffolding and the remaining coefficient laws
  while that milestone is under review.

## Blockers

- None.
