# HexMvPoly Mathlib companion

## Accomplished

- Added the `HexMvPolyMathlib` representation equivalence, transported algebra
  structures, algebra-hom evaluation, recursive-view ring equivalences, and
  correspondence lemmas for the public semantic operations.
- Strengthened the existing `HexPolyMathlib.equiv` to its actual `Semiring`
  assumptions and added a cross-universe `mapEquiv` used by recursive
  coefficient views.
- Proved the Mathlib-free `rename_eq_subst` bridge needed by both the
  correspondence layer and a structural kernel probe.
- Added downstream, build-only `decide +kernel` probes over production `Int`
  and `Rat` inputs, together with a canonical sorted-list adapter and a paired
  fresh-module sweep driver.
- Verified every measured theorem reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Recorded a complete release-quality six-sample paired sweep on `chungus2`.
  The sorted adapter never approached the predeclared 2×/two-family threshold
  and was slower at the larger cancellation point, so the evidence selects the
  single ExtTreeMap representation.
- Compiled the `sos` verifier and all affected modules after migrating its
  compatibility surface to `Hex.MvPoly`.
- Compiled CompPoly's univariate and bivariate recursive-view equivalence files
  after migrating their equivalence chains to the public
  `isEmptyRingEquiv`, `finSuccEquiv`, and dense-polynomial bridges.
- Recorded all eleven native HexMvPoly benchmark ladders, with every declared
  complexity verdict passing.
- Added reproducible adapters for the pinned CompPoly `CMvPolynomial` and a
  canonical sorted-list proxy for the still-unavailable Mathlib
  `MvSparsePoly`, then recorded all five native comparator families.
- Added deterministic, dependency-free SVG plots for the five comparator
  families.
- Kept the reusable tree-algorithm boundary explicit: generic joint traversal
  and merge operations live in `HexBasic/ExtTreeMap.lean`; the comparator and
  polynomial layers add only representation adapters and monomial policy.

## Current frontier

The companion and proof-probe targets build locally, and the release-quality
paired kernel sweep is committed. Native comparator exports, adapters, and
plots are ready to commit. Five representative compiled profiles and the two
Phase 4 reports remain.

## Next step

Commit the native comparator evidence, capture one filtered profile per input
family, then write and validate the Phase 4 reports.

## Blockers

The referenced Mathlib `MvSparsePoly` PR series is still open and is absent
from the pinned Mathlib revision. The kernel comparison therefore uses a local
canonical sorted-list adapter implementing the intended traversal shape; the
final report must identify this limitation rather than claiming measurement of
the unavailable upstream implementation.
