# RCF cached common-root packages

## Accomplished

- Added `CommonRootCert` with externally supplied atom/carrier inputs,
  multiplication-checked factor identities, a scaled Bezout identity, and
  exact constant/nonconstant replay validation.
- Proved that every accepted gcd candidate is nonzero and has exactly the
  common real roots of the atom and carrier.
- Added the cached `hasRoot` query, a generic count-one equivalence for any
  certified carrier root in an isolation, and a strict-`RootModel` corollary.
- Proved the interval bound with multiplicity-aware root-multiset divisibility,
  so a cached gcd replay reports one precisely when the atom vanishes at the
  corresponding carrier root.
- Added a carrier replay accessor and a reusable additive real-cast lemma.
- Added shared-factor, coprime constant-gcd, equal-polynomial, nonunit-scale,
  proper-divisor, wrong-replay-head, zero-scale, and malformed identity/replay
  regressions.
- Updated the umbrella and SPEC to document the actual package API and defer
  deduplication/alignment explicitly to the sign-matrix checker.
- Addressed two fresh Claude reviews; both reported no blockers after tracing
  the trust boundary and count proof.
- Completed a green full `lake build` at the final commit point (9472 jobs).

## Current frontier

Issue #8936 is implemented and locally verified. The branch is ready for its
commit, rebase, PR, hosted CI, and merge gates.

## Next step

Publish and merge the common-root milestone, then implement open-cell sign
constancy, root-cell sign transfer, executable sign reflection, distinct-atom
package alignment, and formula folding.

## Blockers

None.
