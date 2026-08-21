# Determinant identity audit and Sylvester terminology (issue #9316)

## Accomplished

Audited `HexDeterminant`, `HexDeterminantMathlib`, both umbrellas, and both
SPECs against the actual declarations, then amended the documentation to match.

**Export surface.** No umbrella export change was needed. `HexDeterminantMathlib.lean`
imports only `Core`, but `desnanot_jacobi` still reaches the umbrella:
`Core` publicly imports `CoreTransport`, which publicly imports `DesnanotJacobi`.
Confirmed by elaborating 55 `#check`s against `import HexDeterminant` and
`import HexDeterminantMathlib` alone, in a scratch file that was then deleted.
Every declaration named in the amended SPECs and READMEs resolves that way.

**Terminology.** Four names were being used interchangeably. They are now fixed
to one sense each:

- *Desnanot-Jacobi* (Dodgson condensation): rows and columns deleted. Proved
  only over Mathlib matrices, in `DesnanotJacobi.lean`, with three transported
  forms in `CoreTransport`/`CorePlucker`.
- *Jacobi's adjugate-minor identity at `2 x 2`*, in row-replacement form. This is
  `Hex.Matrix.det_setRow_setRow_mul_det`, Mathlib-free, hypothesis `a != b` only.
  Basis-vector substitution recovers Desnanot-Jacobi for an arbitrary row/column
  pair, so it is at least as strong.
- *Grassmann-Plücker three-term relation*: about maximal minors of a tall
  matrix. `det_plucker_three_term` (arbitrary `p1 < p2 < p3`, Mathlib layer) and
  `det_plucker_three_term_consecutive_top` (Mathlib-free specialisation).
- *Sylvester's determinant identity*: absent from the project.

The one place labelling a determinant identity "Sylvester" was the docstring on
`cofactorRowPairing_setRow_plucker`, which called it "the quadratic Sylvester
relation". Corrected in place rather than propagated.

**Sylvester specified, not proved.** `HexDeterminantMathlib/SPEC` now carries the
exact formula, the proposed home (`HexDeterminantMathlib/Sylvester.lean`,
following the `DesnanotJacobi.lean` upstream-inline precedent), and the finding
that nothing needs it: fraction-free elimination uses only the `m = 1` case,
which `desnanot_jacobi_borderedMinor` already provides. The proposed statement
was checked to elaborate, and the formula checked by `decide +kernel` over `Z` at
`(k, m) = (1, 1)`, `(1, 2)`, `(2, 1)`.

**Stale documentation found and fixed.**

- The `hex-determinant` SPEC listed modules `Index`, `Expansion`, `Selection`,
  none of which exist, and omitted `LastRow`, `RowOps`, `Triangular`, `Gram`.
- The SPEC and README both cited `det_one : det 1 = 1`. The theorem is
  `det_identity : det (Matrix.identity n) = 1`; there is no matrix `One`
  instance (dropped in #8437).
- `HexDeterminant/README.md` and the manual chapter both called
  `det_plucker_three_term_consecutive_top` a "Plücker / Desnanot-Jacobi"
  identity, and the manual described it as relating "a matrix and its bordered
  minors", which is Sylvester's shape, not Plücker's.
- `HexDeterminantMathlib/README.md` said `det_plucker_three_term` was "assembled
  for the Bareiss correctness proof". Nothing in the tree consumes it; the
  Bareiss path uses `desnanot_jacobi_borderedMinor`.

**Recorded, not acted on.** `Hex.Matrix.det_setRow_setRow_mul_det` (Mathlib-free,
PR #6111) and `HexMatrixMathlib.det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub`
(via Mathlib's adjugate, PR #6048) are the same statement proved twice, with the
subtracted products in opposite factor order. The Mathlib-side copy could now be
re-derived from the Mathlib-free one. That is a refactor with no correctness
content, so the SPEC records it and the code was left alone.

Added `{docstring Hex.Matrix.det_setRow_setRow_mul_det}` to the manual chapter:
it is a headline public theorem that had no manual coverage.

## Current frontier

Documentation for the determinant libraries now matches the declarations. No
`sorry`, `axiom`, or export change was introduced; the only Lean edits are
docstrings and one manual chapter.

## Next step

If someone wants the general Sylvester identity, the SPEC entry is a complete
work item: statement, home, and the reason it is not urgent. It is a good
candidate for upstreaming to Mathlib rather than living here.

## Blockers

None.
