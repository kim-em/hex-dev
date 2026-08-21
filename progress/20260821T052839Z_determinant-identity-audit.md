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

## Second-opinion round

A Codex review confirmed the mathematics (the basis-vector specialisation and
its signs, the `det_sylvester` statement and its `m = 0` and `m = 1` cases, the
Grassmann-Plücker naming, the export chain, and the no-nondegeneracy claim) and
flagged wording that was too absolute or imprecise. Acted on all of it:

- "It is not Sylvester's identity" contradicted the SPEC's own statement that
  Desnanot-Jacobi *is* Sylvester's `2 × 2` case. Narrowed to "not the general
  Sylvester determinant identity" throughout.
- "would remove `desnanot_jacobi` from the published library" overstated private
  imports. It would remove it from the umbrella's export surface; the module
  stays directly importable, which is what makes such a regression easy to miss.
- The reindexing direction in `desnanot_jacobi_matrixEquiv_reindex` was stated
  backwards. In `A.submatrix row col`, `row` maps *new* indices to original
  ones, so you want `row 0 = r1` and `row (Fin.last _) = r2`.
- `DesnanotJacobi.lean`'s header claimed verbatim-upstream status and said this
  project "still uses plain `import`". Neither is true: the file was migrated to
  the module system and had two `simp` sets repaired across toolchain bumps
  (#8436, plus a style pass), and upstream has moved past `bbe9ab491bc1`. The
  header and SPEC now say so and warn against assuming a drop-in swap.
- The proof-mechanism paragraph named `mul_adjugate` and `adjugate_mul` as
  directly used. The code calls `adjugate_mul_apply` on one association and
  `setRow_mul_adjugate_apply_self`/`_ne` on the other, resting on
  `cofactorRowPairing_self` and `cofactorRowPairing_alien_eq_zero`.
- "That restriction is what keeps the proof Mathlib-free" implied a mathematical
  dependency. It only removes the `q > p3` case.
- "maximal minors of a tall matrix" hid that the relation mixes `mDet` of
  `[B | v]` with `nDet` of `B`. Spelled out in both READMEs and the manual.
- "`k`-fold Sylvester identity" clashed with the proposed statement's use of `k`
  for the core size. Now "the general `m × m` bordered-minor statement".

The sign claim was independently checked outside Lean over 200 random integer
matrices of sizes 3, 4 and 5, across every row pair and column pair: the
replacement identity at basis vectors, the
`(-1)^(a + b + j1 + j2)` double-replacement sign, and generalized
Desnanot-Jacobi all hold with no failures.

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
