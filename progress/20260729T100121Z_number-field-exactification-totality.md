# Number-field exactification totality

## Accomplished

- Proved totality and soundness of normalized algebraic-number construction and irreducible-factor exactification.
- Reworked fixed-presentation relation discovery around direct Krylov powers and proved span-solver soundness and completeness.
- Proved the first relation returned by `QAdjoin.minpoly?` has minimal-polynomial degree and yields the required primitive, positive-leading, irreducible, and simple-root certificates.
- Proved fixed-presentation exactification survives isolation, refinement, guarded approximation, candidate matching, and canonical normalization, with the total wrapper preserving its selected complex value.
- Added the public factorization, refinement, geometry, coordinate, and algebra-equivalence bridges needed by those proofs.
- Recorded the fixed-presentation totality and semantic headline in the permanent Mathlib SPEC.
- Reworked the executable relation search to share one linear-multiplication Krylov orbit, added its coordinate proof, and registered a degree-10 minimal-relation benchmark after review caught repeated power recomputation.
- Added axiom guards for all four exactification totality/headline theorems and deduplicated refined-level totality through the lower HexRootsMathlib theorem.
- Built `HexNumberFieldMathlib.Exact` successfully with no new `sorry` declarations.
- Monitored and repaired the preceding approximation-radius PR through CI; PR #9080 is merged.

## Current frontier

The fixed-presentation exactification milestone is rebased onto merged PR #9080,
reviewed, and locally complete. The review's performance blocker is fixed, and
the final whole-project, conformance, and benchmark checks pass.

## Next step

Publish this milestone as the sole NumberField PR, monitor its CI, and begin the
next NumberField stage locally without opening another PR before this one merges.

## Blockers

None.
