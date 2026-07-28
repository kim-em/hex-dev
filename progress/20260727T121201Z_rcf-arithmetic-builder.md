# RCF arithmetic builder

## Accomplished

- Added exact rational-polynomial denominator clearing and integral conversion
  for compiled certificate preparation.
- Added checker-retained carrier construction from the recomputed sentence
  product and primitive square-free decomposition.
- Added checker-retained rational-xgcd common-root construction, including
  exact factor conversion, one common denominator for the scaled Bezout
  identity, and optional generalized replay construction.
- Added first-occurrence-preserving construction of one common-root package per
  distinct nonconstant atom, aligned with the sign-matrix checker order.
- Proved that every emitted carrier, common-root package, and aligned package
  list passes its corresponding checker.
- Added compiled regressions for signed/nonprimitive content, repeated factors,
  exact derivative quotients, coprime/shared/equal roots, nonunit Bezout scale,
  duplicate alignment, constants, and zero-gcd failure.
- Updated the umbrella and RCF SPEC file map. Focused builds, the full 9479-job
  build, DAG/copyright/trust-surface checks, and diff checks pass.
- Merged the preceding certificate/soundness PR after hosted CI completed
  successfully.

## Current frontier

The arithmetic preparation layer required before top-level certificate
assembly is complete locally and ready to publish as the issue #8952 PR.

## Next step

Rebase onto the merged certificate/soundness milestone, publish issue #8952,
then implement compiled isolation/separation/endpoint/sign-matrix/certificate
assembly and the public one-way-sound decision wrapper.

## Blockers

The fresh Opus review launcher could not authenticate because its OAuth session
expired. The independent Sol audit completed; both of its required findings
were addressed. There is no implementation blocker.
