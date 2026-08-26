# Resultant testing milestone

## Accomplished

- Added core conformance coverage for the full `HexResultant` executable API:
  exact-division helpers, pseudo-division, Brown chains, resultants, and
  discriminants, including totality and defective-drop cases.
- Added a deterministic seed-`0xC0FFEE` emitter for 30 degree-10 polynomial
  pairs and committed all 60 resultant/discriminant results.
- Added a python-flint/PARI oracle that recomputes every result from the
  original inputs, plus a local independent Sylvester/Bareiss replay that
  agreed on all 60 values.
- Added Mathlib-free `resultant` and `disc` LeanBench registrations with the
  specified quadratic coefficient-operation model and wired their build,
  list, and verify paths into the existing single Ubuntu CI job.
- Built `HexResultant.Conformance`, `HexConformance`, the fixture emitter, and
  the bench executable; both benchmark registrations pass `verify`.

## Current frontier

- Independent review of `HexNumberFieldTowerMathlib` found three false
  contracts and one vacuous level-invariant theorem in the preceding stack
  layer. The counterexamples are concrete and require corrections before
  proof work begins.

## Next step

- Publish this isolated resultant-testing milestone, then repair the reviewed
  tower-mathlib contracts and rebase the documentation/testing stack before
  proceeding to `HexNumberField` conformance and benchmarks.

## Blockers

- `HexNumberFieldTowerMathlib` PR #8941 must be corrected for the review's
  validity, irreducibility, factor-selection, and relative-level-invariant
  findings.
