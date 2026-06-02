# HexMatrix Determinant/Bareiss API Phase 6 Review

Scope: `HexMatrix/Determinant.lean`, `HexMatrix/Bareiss.lean`, the
determinant/Bareiss checks in `HexMatrix/Conformance.lean`, and the root
import `HexMatrix.lean`, checked against `SPEC/Libraries/hex-matrix.md` and
`PLAN/Phase6.md`.

## Findings

Follow-up needed. Phase 6 should not close for the determinant/Bareiss surface
until the placement issue below is resolved.

- `HexMatrix/Determinant.lean` exposes public Desnanot-Jacobi and adjugate
  assembly in the Mathlib-free layer, despite the SPEC table forbidding
  Desnanot-Jacobi in `hex-matrix` in scaled, unscaled, or bordered-minor form.
  The public declarations include `det_desnanot_jacobi_mul`,
  `det_desnanot_jacobi_int`, `auxAdjugateM`, `auxP`,
  `det_mul_auxAdjugateM`, `det_auxP`, and `det_auxAdjugateM`. These names are
  not just harmless local helpers: their statements connect `Hex.det` of
  submatrices through the adjugate construction, which is exactly the forbidden
  bridge family. The immediate repair should either relocate this cluster to
  `HexMatrixMathlib` or narrow it to private/local structural equalities that do
  not expose a Desnanot-Jacobi theorem surface from `HexMatrix`.

- The determinant API has good named high-level facts for normal callers:
  `det_one`, `det_rowSwap`, `det_rowScale`, `det_rowAdd`, transpose,
  triangular, cofactor, Laplace, column-replacement, Cauchy-Binet, and Gram
  nonnegativity lemmas. However, the file also publicly exposes many
  implementation objects from the Leibniz encoding and Cauchy-Binet machinery
  (`insertAt`, `emptyVec`, `permutationVectors`, `inversionCount`, `detSign`,
  `detProduct`, `detTerm`, `columnTupleVectors`, `columnTupleCoeff`, and
  several sorting/reconstruction helpers). This makes the caller-facing API
  harder to distinguish from proof infrastructure. Phase 6 should either
  document these as intended public combinatorial utilities or make the
  nonessential ones private / namespace-local behind the named determinant
  lemmas.

- The public row-operation determinant lemmas match the SPEC statement shape,
  but `det_one`, `det_rowSwap`, `det_rowScale`, and `det_rowAdd` have no
  declaration docstrings and no automation attributes. They should have concise
  docstrings because they are the advertised Mathlib-free row-operation API.
  `@[grind]` is worth testing on the four wrapper facts; broad `@[simp]` should
  be used cautiously, especially for `det_rowSwap` and conditional `det_rowAdd`,
  because unconditional rewriting can obscure goals rather than normalize them.

- `HexMatrix/Bareiss.lean` keeps the executable algorithm separate from the
  determinant bridge in most of its theorem surface: `bareiss`,
  `bareissData`, `bareiss_eq_bareissData_det`,
  `bareissData_eq_finish_pivotLoop`, pivot-search facts, and loop branch lemmas
  characterize the executable state without proving `bareiss = det`. That
  split is correct. The module comment, however, says the root library exposes
  the theorem surface relating the executable path to the generic determinant;
  in this layer that wording is misleading and should be changed to say the
  packaged state is provided for the bridge proof.

- `BareissData` and `BareissState` are public structures, but their fields are
  only documented at the structure level. `matrix`, `rowSwaps`, and
  `singularStep` are central to downstream bridge proofs and conformance
  checks, so they need field-level documentation or small public projection
  lemmas that explain the meaning of `some k`, the sign convention, and the
  final-diagonal determinant encoding. The existing `BareissData.det_succ_eq`
  and `BareissData.det_zero_eq` are useful but do not fully document the
  singular-step and swap-count story.

- `HexMatrix/Conformance.lean` currently checks `Matrix.bareiss M =
  Matrix.det M` on committed fixtures by evaluation. This is useful executable
  coverage, but the conformance module comment should make clear these are
  fixture checks, not a Lean theorem establishing the forbidden
  `bareiss_eq_det` bridge in `HexMatrix`. The 6x6 row-operation Bareiss guards
  are also only value-level checks, so they do not violate the SPEC placement
  rule by themselves.

- The root import `HexMatrix.lean` imports `Determinant` before `Bareiss`, which
  matches the implementation dependency and keeps `Bareiss` from importing
  row-reduction or conformance machinery. No root-import fan-out issue was
  found.

## Overlap With PR #6247

PR #6247 is titled `feat: add consecutive-top Plucker theorem` and touches
`HexMatrix/Determinant.lean`. This review does not require implementing or
changing that theorem. The overlap risk is conceptual: the current public
Plucker/cofactor-row surface (`cofactorRowPairing_setRow_plucker`,
`det_setRow_setRow_mul_det`, `mDet`, `nDet`, `twoColDet`) is already large, and
new consecutive-top helpers should be reviewed after #6247 lands to ensure they
do not deepen the same public-infrastructure sprawl or rely on the forbidden
Desnanot-Jacobi cluster.

## Proposed Follow-Up Issues

- `HexMatrix Phase 6: relocate Mathlib-free Desnanot-Jacobi public surface`
  Target declarations: `det_desnanot_jacobi_mul`, `det_desnanot_jacobi_int`,
  `auxAdjugateM`, `auxP`, `det_mul_auxAdjugateM`, `det_auxP`,
  `det_auxAdjugateM`, and their public endpoint-collapse helpers.

- `HexMatrix Phase 6: classify determinant proof infrastructure visibility`
  Target declarations: Leibniz helpers (`insertAt`, `emptyVec`,
  `permutationVectors`, `inversionCount`, `detSign`, `detProduct`, `detTerm`)
  and Cauchy-Binet / selected-column tuple helpers.

- `HexMatrix Phase 6: add docstrings and tested grind coverage for determinant row-operation wrappers`
  Target declarations: `det_one`, `det_rowSwap`, `det_rowScale`, `det_rowAdd`.

- `HexMatrix Phase 6: clarify Bareiss module comments and data projections`
  Target declarations: `BareissData`, `BareissState`, `BareissData.sign`,
  `BareissData.det`, `bareissData`, `bareiss_eq_bareissData_det`, and
  `bareissData_eq_finish_pivotLoop`.

- `HexMatrix Phase 6: annotate conformance fixture claims for Bareiss vs det`
  Target file: determinant/Bareiss section of `HexMatrix/Conformance.lean`.

## Checks

- The public determinant row-operation facts promised by the SPEC exist with
  the expected statement shape.
- The executable Bareiss API exposes pivot search, exact-division, branch, data
  packaging, and array-erasure facts without a public `bareiss_eq_det` theorem.
- `HexMatrix.lean` keeps a simple root import sequence and does not introduce
  extra determinant/Bareiss namespace machinery.
- Source edits are intentionally deferred to follow-up issues; this review only
  adds the report.

## Residual Risk

This review audited API shape, theorem placement, docstring coverage,
automation opportunities, and conformance wording. It did not replay the full
12k-line determinant proof or verify whether PR #6247's new consecutive-top
Plucker theorem changes the public surface after it lands.
