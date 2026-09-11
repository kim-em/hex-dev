# hex-row-reduce-mathlib (depends on hex-row-reduce + hex-matrix-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexRowReduce`
Computational performance owner: `HexRowReduce`

Mathlib correspondence for `hex-row-reduce`: connects our computable RREF / rank / span /
nullspace machinery to Mathlib's noncomputable linear-algebra definitions, via
the base `matrixEquiv` from `hex-matrix-mathlib`.

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with Mathlib's
`Matrix.rank` (noncomputable, `finrank R (LinearMap.range M.mulVecLin)`):
```lean
theorem rank_eq [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M)
```

This is deliberately a theorem about a reduced row-echelon witness, not an
arbitrary `IsEchelonForm`: the proof obtains the kernel dimension from the
computed nullspace basis, whose completeness and independence require
`IsRowReduced`. The correspondence theorem uses Mathlib's `Field`; the executable
row-reduction, span, and nullspace APIs in `HexRowReduce` use
`Lean.Grind.Field` (and `DecidableEq` where computation requires it).

**Nullspace:** Our computed nullspace basis spans exactly the kernel of the
Mathlib matrix:
```lean
theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    Submodule.span R
        (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M))
```

**Span:** The executable `IsEchelonForm.spanContains` test, called through a
reduced row-echelon witness, agrees with membership in the span of the Mathlib
matrix's rows:
```lean
theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      vectorEquiv v ∈
        Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M)))
```

This makes our row-reduction computations computable witnesses for Mathlib's
noncomputable rank/kernel/span definitions.

**Span coefficients:** The soundness theorem accepts an `IsEchelonForm`;
completeness of span testing above requires `IsRowReduced`.

```lean
theorem spanCoeffs_eq_linearCombination [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c →
      vectorEquiv v =
        Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c)
```

All four theorems above exist in
`HexRowReduceMathlib/RankSpanNullspace.lean`, in namespace
`HexMatrixMathlib`. In particular, `rank_eq` and `nullspace_span_eq_ker`
require Mathlib `[Field R]` but no `DecidableEq R` when supplied a reduced
witness; instantiating that witness with executable `rowReduce` additionally
requires `[DecidableEq R]`.

## Field inverse correspondence

The inverse and solve theorems in this section and the next are required
extensions, paired with the computational contracts in
[hex-row-reduce](../../HexRowReduce/SPEC/hex-row-reduce.md#field-inverse-and-complete-linear-solve).
They live in namespace `HexMatrixMathlib`. Their coefficient assumptions
are Mathlib `[Field F] [DecidableEq F]`, using the induced
`Field.toGrindField` instance for the executable calls. Choose that instance
before defining inputs and outputs, for example with
`attribute [local instance 2000] Field.toGrindField` in examples. Do not assume
it equals a separately installed `Lean.Grind.Field F` instance, or that
results computed at another instance are directly accepted by these theorems.
Use `matrixEquiv` for matrices and `vectorEquiv` for vectors throughout.

```lean
theorem inverse?_eq_inv [Field F] [DecidableEq F]
    (A B : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = some B → matrixEquiv B = (matrixEquiv A)⁻¹

theorem inverse?_eq_none [Field F] [DecidableEq F]
    (A : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = none ↔ (matrixEquiv A).det = 0
```

Together these require the full specification: under nonzero determinant,
`Option.map matrixEquiv (Hex.Matrix.inverse? A) = some ((matrixEquiv A)⁻¹)`;
under zero determinant the result is `none`. Transport the two product
identities of computational `inverse?_spec` and use uniqueness of inverse.

The pinned Mathlib names the noncomputable `Inv` instance `Matrix.inv`;
`A⁻¹` is its nonsingular inverse, defined using `Ring.inverse A.det` and
the adjugate in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.
There is no separate `Matrix.nonsing_inv` definition in that file. The
existing `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` require
`IsUnit A.det`, over `[CommRing F]` and finite decidable square indices;
a nonzero determinant over a field supplies this hypothesis. At singular
input Mathlib's inverse is zero, whereas the executable returns `none`;
no theorem should identify that `none` with an inverse witness.

For determinant completeness, apply existing `rank_eq` to
`Hex.Matrix.rowReduce_isRowReduced A`, identifying `rowReduce_rank A`
with the Mathlib rank. Existing `Matrix.rank_of_det_ne_zero` in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` gives full rank over
`[CommRing F] [IsDomain F]` with finite decidable square indices. The
computational `inverse?_isSome` then gives success. Conversely, success
and the transported product identity imply nonzero determinant by existing
`Matrix.det_ne_zero_of_right_inverse` (commutative ring, nontrivial
coefficients, finite decidable square indices). Thus `none` is equivalent
to determinant zero without adding a determinant computation or dependency
to `HexRowReduce`.

## Linear solve correspondence and completeness

```lean
theorem solve?_spec [Field F] [DecidableEq F]
    (A : Hex.Matrix F n m) (b : Vector F n) (s : Hex.Matrix.SolveData A) :
    Hex.Matrix.solve? A b = some s →
      (matrixEquiv A).mulVec (vectorEquiv s.1) = vectorEquiv b ∧
      s.2 = Hex.Matrix.nullspaceBasisMatrix A ∧
      ∀ x : Fin m → F,
        (matrixEquiv A).mulVec x = vectorEquiv b ↔
          x - vectorEquiv s.1 ∈
            LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv A))

theorem solve?_eq_none [Field F] [DecidableEq F]
    (A : Hex.Matrix F n m) (b : Vector F n) :
    Hex.Matrix.solve? A b = none ↔
      ¬ ∃ x : Fin m → F, (matrixEquiv A).mulVec x = vectorEquiv b
```

Also require the explicit parameter form of the solution-set theorem:
for every successful result `s` and `x : Fin m → F`,

```lean
(matrixEquiv A).mulVec x = vectorEquiv b ↔
  ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → F,
    x = vectorEquiv s.1 + (matrixEquiv s.2).mulVec c
```

The coefficients are unique because the returned columns are the computed
basis with identity on the free coordinates. Use existing
`nullspace_span_eq_ker (Hex.Matrix.rowReduce_isRowReduced A)` to identify
the span of these columns with the kernel; the existing private
`nullspace_linearIndependent` in `RankSpanNullspace.lean` takes `[Field F]`
and an `IsRowReduced` witness. Reuse it within that module, or expose it
if the new correspondence theorems live in a separate module. This gives
an affine translate of the entire kernel, rather than only a residual
check on one solution. The
existing `vectorEquiv_mulVec` in `HexMatrixMathlib/Vector.lean` transports
matrix-vector products over `[Semiring F]`.

For every `Hex.Matrix.solve A b = .error y`, require
`_root_.Matrix.vecMul (vectorEquiv y) (matrixEquiv A) = 0` and
`dotProduct (vectorEquiv y) (vectorEquiv b) ≠ 0`. Moreover failure is
equivalent to existence of such a left-kernel separator. Prove the
constructive direction using the actual returned row of the RREF
transform, and the converse by applying an arbitrary separating row
functional to a hypothetical solution. No resource bound or additional
consistency hypothesis may appear in these completeness statements.

## Verification and ownership

Check the computational SPEC's boundary cases through these
correspondence theorems:

- For `0 × 0`, Mathlib's determinant is `1`, the inverse is the empty
  identity, and solve returns the unique empty solution with no basis
  columns. No theorem assumes a positive dimension.
- For `0 × m`, the kernel is the full space and the returned basis is the
  standard basis. For `n × 0`, consistency is exactly `b = 0`.
- For singular `[[1, 0], [0, 0]]`, determinant zero forces inverse
  failure, while RHS `[a, 0]` has the affine solution set `[a, t]`.
- For `[[1, 0, 0], [1, 0, 0]]` with RHS `[0, 1]`, the returned separator
  `[-1, 1]` has zero left product and dot product `1`, proving the
  rectangular system inconsistent over any field.

Exercise the carrier interpretations in a monorepo build-only module
`Examples/RowReduce.lean`, registered in `HexReleaseExamples`, outside the
generic companion's imports. These examples contain proof checks, not
fixture emission or oracle tests.

- `Rat`: computational conformance uses Lean's rational field instance.
  Companion examples separately select the Mathlib-induced instance before
  defining the matrices and calling inverse/solve. Equality of the two bundled
  instances is not assumed. Transporting an already computed result between
  them would require an additional explicit agreement proof.
- `RationalFn Rat`: follow
  [hex-rational-fn-mathlib's instance contract](../../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md#coefficient-instances-and-representation).
  Choose the Mathlib-induced lightweight field on `Rat` before forming the
  rational-function type, and the induced field on that type before forming
  row-reduction calls. Use `HexRationalFnMathlib.field` and its equivalence
  with `RatFunc Rat` for these examples. Computational fixtures separately
  exercise the implementation with its executable instances. Changing
  instance priorities does not convert previously defined values.
- `ZMod64 p`: the tree provides an executable field under `Bounds p` and
  `PrimeModulus p`, but no Mathlib `Field (ZMod64 p)`. For these examples,
  transport the computational success and failure equations entrywise through
  the existing `HexModArithMathlib.ZMod64.equiv` to `ZMod p`. Supply the prime
  hypotheses for the executable and Mathlib fields. Multiplication, addition,
  zero preservation and injectivity transport the inverse identities and
  separating witness. Surjectivity also transports the quantified solution
  and coefficient vectors, giving completeness and the affine solution set
  over `ZMod p`. These example-level transport proofs are new obligations.
  They use the ring equivalence without assuming a missing `toZMod_inv` lemma
  or a Mathlib field structure on `ZMod64 p`, and do not require transporting
  the elimination algorithm itself.

`HexRowReduce` owns the exact FLINT/SymPy conformance and dimension/height
benchmarks specified in its SPEC. This companion owns proof checks of the
transported success, failure, and solution-set statements; it adds no
benchmark executable. The domain certificate inverse described in hex-rank
and the direct field inverse agree after transport to a common field and
undoing the certificate's row/column selections, by uniqueness of inverse;
that consumer-level comparison adds no dependency between the libraries.
