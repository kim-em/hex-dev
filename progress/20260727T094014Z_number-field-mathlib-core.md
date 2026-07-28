# Number-field Mathlib semantic core

## Accomplished

- Activated `HexNumberFieldMathlib` in the library graph, Lake build, and the
  existing single-job CI target list.
- Added the semantic complex interpretations for `AlgebraicRoot`,
  `AlgebraicNumber`, and checked `QAdjoin` presentations, together with the
  first proof-level contracts for roots, arithmetic maps, injectivity,
  canonical equality, and zero recognition.
- Added the library umbrella and moved its SPEC beside the source.
- Corrected the stale SPEC assumption that factorization-lazy
  `AlgebraicRoot` has executable Boolean equality; comparison proceeds through
  canonical exactification instead.
- Built `HexNumberFieldMathlib.Basic` successfully.

## Current frontier

The semantic core is a green checkpoint. Its proof obligations intentionally
remain visible as Phase-1 `sorry`s; no computational data or structure is
postulated.

Independent review of tower flattening completed while this work was in
progress and found that a full-degree primitive candidate can still have a
non-linear coordinate-recovery gcd. That completeness defect takes priority
over adding the remaining companion modules.

## Next step

Repair flattening so failed recovery advances to another shift, strengthen its
finite search bound and checked certificate, then rebase the tower conformance
and this companion branch before expanding the exactification and lazy
arithmetic contracts.

## Blockers

None for the semantic core. Tower flattening has a review-blocking completeness
defect that is locally actionable.
