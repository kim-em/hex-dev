# RCF carrier and generalized isolations

## Accomplished

- Added deterministic collection of nonconstant atom polynomials and their
  recomputed product from arbitrary reflected sentences.
- Added a multiplication-only carrier certificate checker for the factor and
  derivative identities, with soundness proving carrier/product root equality,
  squarefreeness, and the atom-root union.
- Added raw generalized isolation certificates whose checker validates literal
  replay counts, adjacent dyadic ordering, and total completeness.
- Bridged accepted raw intervals to the existing literal-isolation semantics,
  exposing both one-root-per-interval and every-root-isolated theorems.
- Added positive and adversarial tests, including a genuine repeated factor,
  a factor-valid carrier that drops a root and fails the derivative identity,
  constant atoms, malformed scales/factors/replays, touching intervals,
  overlaps, duplicates, reversed order, incompleteness, and an empty valid
  isolation set for a polynomial with no real roots.
- Updated the RCF umbrella and SPEC file-organization notes. Full `HexRCF` and
  `HexRealRootsMathlib` builds and repository policy checks pass.

## Current frontier

The kernel checker now has a certified square-free carrier whose roots are
exactly the nonconstant atom roots, plus ordered complete literal isolations of
that carrier. The strict separation, endpoint classification, and cell
partition layers have not yet been implemented.

## Next step

Implement the structurally fuel-bounded separation pass and a strict-gap
certificate checker, then define root/open cells and prove their partition and
bounded-endpoint classification facts.

## Blockers

None.
