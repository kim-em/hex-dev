# Tower flattening recovery review

## Accomplished

- Reproduced the independent review's mathematical distinction between
  primitive-element degree collisions and incompatible-conjugate recovery
  collisions.
- Changed the shift search so a full-degree candidate with a non-linear exact
  recovery gcd advances to the next deterministic shift instead of aborting a
  valid flattening.
- Raised the finite search budget to
  `2 * choose(d, 2) + 1`, covering both collision classes, and reconciled the
  tower SPEC.
- Strengthened the returned certificate: in addition to the tower-basis
  coordinate round trip, it now checks that the tower element representing the
  primitive generator zeros its claimed minimal polynomial. This supplies the
  missing multiplicativity premise.
- Strengthened the relative-degree-two fourth-root regression by pinning the
  primitive polynomial and recovered coordinate and by checking
  `fourthRoot² = sqrtTwo` after conversion.
- Removed the stale direct `HexRowReduce` dependency from `libraries.yml`.
- Built `HexNumberFieldTower`, ran the DAG checker, and passed `git diff
  --check`.

## Current frontier

The implementation and local SPEC now address every blocking or medium finding
from the focused flattening review. The concrete cyclotomic example identified
by the reviewer motivates the control-flow change; the general finite bound is
stated independently of that one example.

## Next step

Publish this repair, start a focused independent re-review without waiting on
it, then rebase the conformance branch and repair its arithmetic and PARI
oracle coverage.

## Blockers

None.
