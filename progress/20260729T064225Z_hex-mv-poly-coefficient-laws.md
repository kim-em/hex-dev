# Hex multivariate polynomial coefficient laws

## Accomplished

- Removed an incoherent global `[Zero R]` binder from the semantic part of
  `Basic.lean`; semiring and ring declarations now use the zero supplied by
  their algebraic class.
- Proved canonical-term coefficient recovery and the coefficient laws for
  addition, negation, and subtraction.
- Proved exact monomial-division correctness, coefficient preservation under
  reordering and renaming, the substitution fold equation, and the derived
  `evalHorner` equation.
- Proved that total degree and variable renaming preserve monomial
  multiplication.
- Reworked recursive monomial splitting around exact-arity `dropHead` and
  `prepend` helpers, then proved that `splits` enumerates exactly all
  multiplicative decompositions.
- Narrowed `derivative` to its computational `Zero`/`NatCast`/`Add`/`Mul`
  requirements and removed the elevated local-instance priority.
- Rebuilt all affected modules and the downstream kernel replay target.

## Current frontier

Twelve theorem obligations remain: three monomial-order laws, two polynomial
arithmetic laws, one sparse-Horner law, two structural laws, and four
recursive-view laws.

## Next step

Rebase this implementation series onto the merged SPEC follow-up and publish
the core milestone for review. Continue with multiplication coefficients and
the recursive-view coefficient laws while that review runs.

## Blockers

None.
