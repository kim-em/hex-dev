# hex-invariant-factors (matrix invariant factors, depends on hex-poly-smith)

The invariant factors of a square matrix `A : Matrix F n n` over a field.
They are the monic diagonal entries in the Smith normal form of the
characteristic matrix `xI - A`, ordered so that each divides the next. The
Mathlib-free library constructs that polynomial matrix and calls
[hex-poly-smith](../../HexPolySmith/SPEC/hex-poly-smith.md). It introduces no second polynomial or
polynomial-matrix representation.

The companion `hex-invariant-factors-mathlib` proves that the product of the
factors is the independently computed characteristic polynomial from
[hex-char-poly](hex-char-poly.md), and that the last factor, with value `1` in
dimension zero, is the independently computed minimal polynomial from
[hex-min-poly](hex-min-poly.md). These are comparison theorems. Neither
independent algorithm is used to compute the invariant factors.

Rational canonical form is downstream work. Version one does not specify it,
because the current matrix API has no executable block-diagonal companion
matrix construction with the correspondence theorem that a complete API would
need. See "What is deliberately not here".

## Why this library exists

The three dependencies deliberately solve different problems.

- `hex-poly-smith` computes the canonical diagonal of an arbitrary polynomial
  matrix and can certify its transforms.
- `hex-char-poly` computes `det (xI - A)` by Samuelson-Berkowitz without
  division.
- `hex-min-poly` computes the monic generator of the annihilator of `A` from
  Krylov sequences.

Applying the first algorithm to `xI - A` produces all invariant factors at
once. Comparing its product and last factor with the other two computations
checks two independent descriptions of the same operator. The comparison is
valuable precisely because the Smith computation is not implemented through
either answer.

The full ordered list distinguishes matrices that characteristic and minimal
polynomials together do not. Over an algebraic closure, it records the sizes of
all primary cyclic summands rather than only their total multiplicities and
their largest exponents. It is also the input from which elementary divisors
and rational canonical blocks can later be obtained.

## Dependencies and the one-way graph

The computational library depends only on `hex-poly-smith`. That dependency
already supplies `Hex.Matrix`, `Hex.DensePoly`, the field hypotheses, and the
Smith API. It does not depend on either independent polynomial algorithm.

The Mathlib companion depends on `hex-invariant-factors`,
`hex-poly-smith-mathlib`, `hex-char-poly-mathlib`, and
`hex-min-poly-mathlib`. The last two dependencies point into this comparison
layer and never in the reverse direction:

```text
hex-poly-smith ─────────────── hex-invariant-factors
       │                               │
       └── hex-poly-smith-mathlib ─────┤
                                       ├── hex-invariant-factors-mathlib
hex-char-poly ── hex-char-poly-mathlib ┤
hex-min-poly ─── hex-min-poly-mathlib ─┘
```

In particular, neither `Hex.Matrix.charPoly` nor `Hex.Matrix.minPoly` occurs in
the definition of `Hex.Matrix.invariantFactors`. They first occur in the
companion's comparison file.

## Conventions

```lean
variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}
```

**The characteristic matrix is `xI - A`.** Its `(i,j)` entry is

```text
x - A[i,j]   when i = j,
  - A[i,j]   when i != j,
```

where every scalar is embedded by `Hex.DensePoly.C` and
`x = Hex.DensePoly.monomial 1 1`. The executable definition uses the O(1)
entry accessor `A[(i,j)]`, not the noncomputable row accessor `A[i][j]`. This
agrees entry by entry with Mathlib's `Matrix.charmatrix` after applying
`HexPolyMathlib.toPolynomial`.

**All factors are retained.** A monic unit in `F[x]` is exactly `1`, and unit
factors contain real information about the number of cyclic summands. The
vector therefore has exactly `n` entries and may begin with one or more `1`s.
There is no filtered public answer that drops them.

**The ordering is increasing divisibility.** For factors
`d_0, ..., d_(n-1)`, every `d_i` is monic and nonzero, and
`d_i | d_(i+1)`. Units consequently form a prefix. This is exactly the order
returned by `Hex.PolyMatrix.invariantFactors`, not a reversal chosen for
canonical-form notation.

**The largest factor has a total convention.** `largestFactor A` is the last
factor when `n > 0` and is `1` when `n = 0`. For positive dimension the last
factor has positive degree, so it is the largest nonunit invariant factor. The
dimension-zero convention is forced by the minimal polynomial of the unique
endomorphism of the zero vector space, which is `1`.

**No factor is zero.** The scalar matrix `xI - A` is nonsingular over `F(x)`
for every `A`, including a singular or zero matrix. Its determinant is monic of
degree `n`. A zero invariant factor would therefore be a bug.

## The characteristic matrix

The only new construction in the computational library is the entrywise
embedding of `A` into the existing polynomial matrix type.

```lean
namespace Hex.Matrix

/-- The polynomial matrix `xI - A`, using the existing `Matrix (DensePoly F)`
representation. -/
def charMatrix (A : Matrix F n n) : Matrix (DensePoly F) n n :=
  Matrix.ofFn fun i j =>
    if i = j then
      DensePoly.monomial 1 1 - DensePoly.C A[(i, j)]
    else
      -DensePoly.C A[(i, j)]

theorem charMatrix_apply (A : Matrix F n n) (i j : Fin n) :
    (charMatrix A)[(i, j)] =
      if i = j then DensePoly.monomial 1 1 - DensePoly.C A[(i, j)]
      else -DensePoly.C A[(i, j)]

theorem charMatrix_transpose (A : Matrix F n n) :
    charMatrix A.transpose = (charMatrix A).transpose

end Hex.Matrix
```

`charMatrix` is not a second polynomial-matrix abstraction. Its result is
literally the input type of `Hex.PolyMatrix.snf`. There is no wrapper structure,
conversion, sparse form, or characteristic-matrix-specific elimination loop.

Constructing it writes `n^2` polynomials of size at most two. Diagonal scalars
are not special-cased when they are zero, because `DensePoly` normalisation
already turns `x - 0` into `x`. Off-diagonal zeroes are likewise represented by
the canonical zero polynomial.

## Full rank without computing a characteristic polynomial

The computational library needs to know that the Smith rank is `n` in order to
return a `Vector` of length `n`. It proves this directly and does not call
`Hex.Matrix.charPoly`.

In the Leibniz determinant of `xI - A`, the identity permutation contributes a
monic term of degree `n`. Every other permutation uses at least one
off-diagonal entry and therefore has degree at most `n - 1`. Hence the
determinant is monic of degree `n`, including at `n = 0`, where it is `1` of
degree zero under the project's `degree?.getD 0` convention.

```lean
namespace Hex.Matrix

theorem det_charMatrix_monic (A : Matrix F n n) :
    (Matrix.det (charMatrix A)).Monic

theorem degree?_det_charMatrix (A : Matrix F n n) :
    (Matrix.det (charMatrix A)).degree?.getD 0 = n

theorem snfRank_charMatrix (A : Matrix F n n) :
    PolyMatrix.snfRank (charMatrix A) = n

end Hex.Matrix
```

The last theorem uses only the accepted Smith contract. If the Smith rank were
less than `n`, `diagMatrix S.diag n n` would have zero determinant. The
identity `S.left * charMatrix A * S.right = diagMatrix S.diag n n`, together
with the inverse fields in `SmithData`, would then force
`det (charMatrix A) = 0`, contradicting `det_charMatrix_monic`. No
characteristic-polynomial implementation or correspondence theorem occurs in
this proof.

This direct determinant argument is a specification proof, not a duplicate
algorithm. The runtime path never expands a Leibniz determinant. It calls the
polynomial Smith implementation exactly once.

## Algorithm and API

The algorithm is deliberately short.

1. Construct `charMatrix A`.
2. Call `Hex.PolyMatrix.invariantFactors` on it.
3. Cast the result length from `snfRank (charMatrix A)` to `n` using
   `snfRank_charMatrix`.

The product and last-factor operations below are matrix convenience folds, so
each direct call computes the factors. A caller that already holds the vector
uses the displayed folds directly. Version one does not add a result structure
solely to cache the three projections.

```lean
namespace Hex.Matrix

/-- The monic invariant factors of `xI - A`, including leading units, in
increasing-divisibility order. -/
def invariantFactors (A : Matrix F n n) : Vector (DensePoly F) n

/-- Product of all invariant factors. The empty product is `1`. -/
def factorProduct (A : Matrix F n n) : DensePoly F :=
  (invariantFactors A).foldl (fun p q => p * q) 1

/-- The last invariant factor, or `1` for a zero-dimensional matrix. -/
def largestFactor (A : Matrix F n n) : DensePoly F :=
  (invariantFactors A).foldl (fun _ q => q) 1

end Hex.Matrix
```

There is no public `Option` around `largestFactor`. Absence at `n = 0` is not a
failure and the mathematically useful total value is `1`. There is also no
search for the last entry unequal to `1`: positive dimension and the degree
sum below prove that the last entry is already nonunit.

## Computational contracts

The following theorems are Mathlib-free. They are consequences of
`Hex.PolyMatrix.snfData_isSNF`, `IsSNF.rank_eq`, `IsSNF.diag_eq`, and the
full-rank argument above.

```lean
namespace Hex.Matrix

/-- The public vector is exactly the accepted polynomial-Smith diagonal, after
transporting its length from `snfRank (charMatrix A)` to `n`. -/
theorem invariantFactors_heq (A : Matrix F n n) :
    HEq (invariantFactors A)
      (PolyMatrix.invariantFactors (charMatrix A))

theorem invariantFactors_transpose (A : Matrix F n n) :
    invariantFactors A.transpose = invariantFactors A

theorem invariantFactors_conj (A U V : Matrix F n n)
    (h : U * V = Matrix.identity n) :
    invariantFactors (U * A * V) = invariantFactors A

theorem factor_monic (A : Matrix F n n) (i : Fin n) :
    ((invariantFactors A)[i]).Monic

theorem factor_ne_zero (A : Matrix F n n) (i : Fin n) :
    (invariantFactors A)[i] ≠ 0

theorem factor_chain (A : Matrix F n n) (i : Nat) (h : i + 1 < n) :
    (invariantFactors A)[i]'(by omega) ∣
      (invariantFactors A)[i + 1]'h

/-- A monic invariant factor is a unit exactly when it is `1`. -/
theorem factor_unit_iff (A : Matrix F n n) (i : Fin n) :
    ((invariantFactors A)[i]).size = 1 ↔ (invariantFactors A)[i] = 1

/-- Unit entries form a prefix of the ordered vector. -/
theorem factor_unit_prefix (A : Matrix F n n) (i j : Fin n) (hij : j ≤ i)
    (hi : (invariantFactors A)[i] = 1) :
    (invariantFactors A)[j] = 1

theorem factorProduct_eq_det (A : Matrix F n n) :
    factorProduct A = Matrix.det (charMatrix A)

theorem factorProduct_monic (A : Matrix F n n) :
    (factorProduct A).Monic

theorem degree_sum (A : Matrix F n n) :
    (invariantFactors A).foldl
      (fun d p => d + p.degree?.getD 0) 0 = n

theorem largestFactor_empty (A : Matrix F 0 0) : largestFactor A = 1

theorem largestFactor_eq_last (A : Matrix F n n) (hn : 0 < n) :
    largestFactor A =
      (invariantFactors A)[n - 1]'(by omega)

theorem largestFactor_nonunit (A : Matrix F n n) (hn : 0 < n) :
    1 < (largestFactor A).size

end Hex.Matrix
```

The notation in these signatures follows the current `Vector` and
`DensePoly` APIs. The dependent index proofs are the only casts introduced by
the length-`n` public vector.

`factorProduct_eq_det` has no unit ambiguity. The polynomial-Smith theorem
first gives `monicize (det (charMatrix A))`. The determinant is already monic,
so `monicize` is definitionally or propositionally the identity. This is the
normalisation step that turns an associated-product statement into equality.

For transpose invariance, transpose the two Smith transforms, swap their
roles, and transpose their stored inverses. The diagonal matrix is unchanged,
so `IsSNF.diag_eq` gives exact equality in the accepted order. For similarity
invariance, embed `U` and `V` entrywise as constant polynomial matrices. The
one-sided inverse hypothesis gives the other side through
`Hex.Matrix.mul_eq_one_comm`, and

```text
C(U) * (xI - A) * C(V) = xI - C(U * A * V).
```

The constant matrices are therefore admissible Smith transforms. Uniqueness
again gives exact equality of the diagonals. Neither theorem recomputes a
normal form in its proof.

`largestFactor_nonunit` follows from `degree_sum`. If `n > 0` and the last
factor were `1`, divisibility and monicity would make every preceding factor
`1`, contradicting the positive sum of degrees.

## Degenerate cases

Each case below is part of the public contract and has both a Lean-side check
and an oracle fixture where the fixture format permits it.

**Dimension zero.** For `A : Matrix F 0 0`, `charMatrix A` is the empty
polynomial matrix, `invariantFactors A` is the empty vector,
`factorProduct A = 1`, and `largestFactor A = 1`. The independent answers are
also `charPoly A = 1` and `minPoly A = 1`. No definition indexes the vector.

**The zero matrix in positive dimension.** For `n > 0` and `A = 0`, the
characteristic matrix is `xI`, already in Smith form. All `n` invariant factors
are `x`, their product is `x^n`, and the largest factor is `x`. Returning
`1, ..., 1, x^n` would preserve the product and largest-factor comparisons but
would be the wrong Smith form, so this case is essential.

**One-by-one matrices.** For `A = [[a]]`, the only factor is `x - a`. At
`a = 0` this is `x`, not the zero polynomial.

**Unit factors.** A cyclic `n` by `n` matrix has factors
`1, ..., 1, charPoly A`. Units stay in the length-`n` vector. They are not
reported as zeroes and are not omitted. A nonzero constant returned by the raw
elimination is normalised to `1` by the accepted Smith algorithm.

**Singular matrices.** Singularity of `A` means the constant coefficient of
`det (xI - A)` is zero. It does not make `xI - A` singular over `F[x]` or
reduce its Smith rank. Every factor remains monic and nonzero. In positive
dimension the last factor has zero constant coefficient exactly when `A` is
singular:

```lean
theorem singular_iff_coeff_zero
    (A : Matrix F n n) (hn : 0 < n) :
    (largestFactor A).coeff 0 = 0 ↔ Matrix.det A = 0
```

This theorem belongs in the Mathlib companion. It follows from
`largestFactor_eq_minPoly` and the standard fact that a linear operator is
invertible exactly when its minimal polynomial has nonzero constant
coefficient. It is not used to compute the factors.

**Repeated and split factors.** For `diag(a, a, b)` with `a != b`, the factors
are `1`, `x - a`, and `(x - a)(x - b)`. For `aI`, all factors are `x - a`.
These cases distinguish the ordered list from both the product and the largest
factor.

## Executable certificates

The certificate for invariant factors is the accepted polynomial-Smith
certificate applied to `charMatrix A`. There is no weaker
characteristic-matrix-specific checker and no duplicate transform structure.

```lean
namespace Hex.Matrix

/-- Check proposed Smith data and its intermediate left product for `xI - A`. -/
def factorsCert (A : Matrix F n n)
    (S : PolyMatrix.SmithData F n n)
    (T : Matrix (DensePoly F) n n) : Bool :=
  PolyMatrix.snfCert (charMatrix A) S T

theorem factorsCert_sound (A : Matrix F n n)
    (S : PolyMatrix.SmithData F n n)
    (T : Matrix (DensePoly F) n n)
    (h : factorsCert A S T = true) :
    S.rank = n ∧ HEq S.diag (invariantFactors A)

theorem factorsCert_self (A : Matrix F n n)
    (S := PolyMatrix.snfData (charMatrix A)) :
    factorsCert A S (S.left * charMatrix A) = true

end Hex.Matrix
```

Soundness first invokes `Hex.PolyMatrix.snfCert_sound`. Full rank follows from
`snfRank_charMatrix` and `IsSNF.rank_eq`. Diagonal equality follows from
`IsSNF.diag_eq`, including monicity and the divisibility order. Thus an
accepted certificate establishes the complete ordered answer, not only its
product.

The checker forms the same four polynomial matrix products as
`Hex.PolyMatrix.snfCert`. The conditional `mulEqCertAt` optimisation remains
available under its stated distinct-point and degree hypotheses. This library
does not invent points, weaken those hypotheses, or route small fields through
it.

The companion also exposes an executable independent cross-check:

```lean
namespace HexInvariantFactorsMathlib

def crossCheck (A : Hex.Matrix F n n) : Bool :=
  let d := Hex.Matrix.invariantFactors A
  let product := d.foldl (fun p q => p * q) 1
  let largest := d.foldl (fun _ q => q) 1
  (product == Hex.Matrix.charPoly A) &&
    (largest == Hex.Matrix.minPoly A)

theorem crossCheck_sound (A : Hex.Matrix F n n) :
    crossCheck A = true →
      Hex.Matrix.factorProduct A = Hex.Matrix.charPoly A ∧
      Hex.Matrix.largestFactor A = Hex.Matrix.minPoly A

theorem crossCheck_eq_true (A : Hex.Matrix F n n) : crossCheck A = true

end HexInvariantFactorsMathlib
```

`crossCheck` is a cross-check and not a replacement certificate. Equality with
the characteristic and minimal polynomials does not determine all intermediate
invariant factors. For example, several different divisibility chains can
have the same product and last entry. `factorsCert` is what establishes the
whole list.

## The Mathlib layer

The companion has three jobs: transport the characteristic matrix, identify
the product, and identify the largest factor.

```lean
namespace HexInvariantFactorsMathlib

open HexMatrixMathlib HexPolyMathlib HexPolySmithMathlib

variable {F : Type*} [Field F] [DecidableEq F] {n : Nat}

/-- The executable characteristic matrix is Mathlib's `Matrix.charmatrix`. -/
theorem equiv_charMatrix (A : Hex.Matrix F n n) :
    polyMatrixEquiv (Hex.Matrix.charMatrix A) =
      Matrix.charmatrix (matrixEquiv A)

/-- Each executable factor is the corresponding entry in the transported
Smith normal form. -/
theorem equiv_factor (A : Hex.Matrix F n n) (i : Fin n) :
    toPolynomial ((Hex.Matrix.invariantFactors A)[i]) =
      (smithNormalForm (Hex.Matrix.charMatrix A)).a
        (Fin.cast (Hex.Matrix.snfRank_charMatrix A).symm i)

/-- The product agrees with the independently computed characteristic
polynomial. -/
theorem factorProduct_eq_charPoly (A : Hex.Matrix F n n) :
    Hex.Matrix.factorProduct A = Hex.Matrix.charPoly A

/-- The last factor, with the dimension-zero convention, agrees with the
independently computed minimal polynomial. -/
theorem largestFactor_eq_minPoly (A : Hex.Matrix F n n) :
    Hex.Matrix.largestFactor A = Hex.Matrix.minPoly A

end HexInvariantFactorsMathlib
```

### Product correspondence

Transporting `factorProduct_eq_det` through `polyMatrixEquiv` identifies its
right side with `det (Matrix.charmatrix (matrixEquiv A))`, which is
`Matrix.charpoly (matrixEquiv A)`. The theorem
`HexCharPolyMathlib.equiv_charPoly` identifies the independently computed
`Hex.Matrix.charPoly A` with that same Mathlib polynomial. Injectivity of
`HexPolyMathlib.toPolynomial` gives exact equality of the executable dense
polynomials.

This route uses both computations. Defining the characteristic polynomial as
`factorProduct A` would make the theorem reflexive and is forbidden by the
dependency graph.

### Largest-factor correspondence

The proof uses the module presented by `xI - A`. There is one orientation
detail that must not be hidden. `HexPolySmithMathlib.quotientEquiv` presents a
quotient by the submodule spanned by matrix rows, while
`Hex.Matrix.minPoly` uses column-vector multiplication by `A`.

Use the rows of `(charMatrix A).transpose`. Its relation in column `j` is
`x e_j - sum_i A[i,j] e_i`, so multiplication by `x` on the quotient becomes
column multiplication by `A`. The accepted transforms supply the required
transpose invariance: if `S = U M V`, then
`S.transpose = V.transpose M.transpose U.transpose`, and the transposes of the
stored inverses are inverses. The diagonal matrix is unchanged. Applying
`IsSNF.rank_eq` and `IsSNF.diag_eq` proves that `M` and `M.transpose` have the
same ordered invariant factors. No extra canonicity theorem is assumed.

The companion defines the concrete comparison object:

```lean
/-- Polynomial vectors modulo the columns of `xI - A`. -/
noncomputable def operatorQuotient (A : Hex.Matrix F n n) :=
  (Fin n → Polynomial F) ⧸ Submodule.span (Polynomial F)
    (Set.range
      (polyMatrixEquiv (Hex.Matrix.charMatrix A).transpose))

/-- Evaluation at `A` identifies the presented module with the underlying
vector space. -/
noncomputable def operatorEquiv (A : Hex.Matrix F n n) :
    operatorQuotient A ≃ₗ[F] (Fin n → F)

/-- Multiplication by `X` in the quotient is multiplication by `A` on column
vectors. -/
theorem operatorEquiv_X (A : Hex.Matrix F n n) (v : operatorQuotient A) :
    operatorEquiv A (Polynomial.X • v) =
      (matrixEquiv A).mulVec (operatorEquiv A v)
```

In Lean source, the quotient and scalar-action expressions use the exact
Mathlib notation admitted by the selected quotient-module instances. The
signature above fixes the objects and the intertwining equation rather than
requiring a new executable representation.

Applying `HexPolySmithMathlib.quotientEquiv` to the transposed characteristic
matrix decomposes `operatorQuotient A` as the direct sum of
`F[x]/(d_i)`. The annihilator of that direct sum is the intersection of the
ideals `(d_i)`, equivalently the ideal generated by their least common
multiple. Because the factors form a monic divisibility chain, that generator
is the last factor. For the empty direct sum the annihilator is the whole ring
and its monic generator is `1`.

The intertwining theorem says this annihilator is exactly the ideal of
polynomials `p` with `p(A) = 0`. `HexMinPolyMathlib.equiv_minPoly` identifies
its independently computed monic generator with Mathlib's `minpoly`. Monicity
on both sides removes association by a unit and proves
`largestFactor_eq_minPoly` as equality.

This proof requires no new result from `hex-poly-smith`. The transpose Smith
data is constructed from its stored transforms and inverses, and canonicity is
exactly `IsSNF.rank_eq` plus `IsSNF.diag_eq`. The new work is the operator
quotient equivalence and the elementary annihilator calculation, both of which
belong in this application layer.

## Complexity

Let `A` be `n` by `n`. The input polynomial degree to Smith form is `1`, but
that does not make the accepted polynomial-Smith loop constant-degree. At a
later pivot, entries of the working matrix may have grown. Its repetition
count `P` remains bounded by the degree of the pivot on entry to that stage,
not by `2`.

| operation | work beyond `hex-poly-smith` | total bound or status |
|---|---|---|
| `charMatrix` | `n^2` scalar embeddings and subtractions | `O(n^2)` field operations, degree at most `1` |
| `invariantFactors` | one length cast after `PolyMatrix.invariantFactors` | the `snf` bound with square size, rank `n`, initial degree `1` |
| the `factorProduct` fold after factor computation | `n` polynomial multiplications | `O(n^2)` field operations with classical multiplication in the worst degree distribution |
| the `largestFactor` fold after factor computation | one pass retaining the last entry | `O(n)` references, no polynomial arithmetic |
| `factorsCert` | no new checks beyond `snfCert` | four polynomial-matrix product identities and the Smith shape check |
| `crossCheck` | dense-polynomial equality | excludes the cost of independently computing the three inputs |

A direct call to `factorProduct A` or `largestFactor A` includes the
`invariantFactors A` cost before the listed fold cost.

The answer has a sharp degree bound:

```text
sum_i deg d_i = n.
```

There is still no bound here on degrees or coefficient sizes in the working
Smith matrix or its transforms. Over `Rat`, degree growth and rational
coefficient growth are separate measurements. This library inherits both
limitations from `hex-poly-smith` and must not restate the output-degree
identity as an intermediate-growth bound.

Computing all three independent answers for `crossCheck` costs the Smith run,
the `O(n^4)` Samuelson-Berkowitz run, and the `O(n^4)` Krylov basis sweep. The
check itself is cheap relative to producing those values. It is intended for
conformance and user-requested validation, not as the default implementation
of `invariantFactors`.

## Conformance

Per [SPEC/testing.md](../testing.md), extend the existing single oracle script
and the existing single CI job. Do not add a workflow, job, or matrix.

Add `conformance/HexInvariantFactors/EmitFixtures.lean`, exposed as
`lean_exe hexinvariantfactors_emit_fixtures`, and
`conformance/HexInvariantFactors/Conformance.lean`. Commit the snapshot at
`conformance-fixtures/HexInvariantFactors/invariant-factors.jsonl`. Append one
tuple to `ORACLES` in `scripts/ci/run_oracles.sh`:

```text
"HexInvariantFactors|hexinvariantfactors_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexInvariantFactors/invariant-factors.jsonl"
```

The fixture input is the existing integer `matrix` kind. The new handler in
`scripts/oracle/matrix_flint.py` constructs `xI - A` over `QQ[x]`, obtains its
Smith diagonal through the polynomial-Smith oracle selected by
`hex-poly-smith`, normalises every nonzero diagonal entry to monic, and retains
all `n` entries including units. It independently asks FLINT for `charpoly()`
and `minpoly()`. The record contains the factor coefficient lists in ascending
order, followed by the independently computed product and largest-factor
values. The driver checks both comparisons before emitting success.

The Smith oracle comparison is the primary oracle. The product and
largest-factor comparisons are necessary cross-checks and cannot replace it,
because they do not determine the intermediate entries.

**Required oracle cases.** All expected coefficient lists are ascending.

- `n = 0`, handled explicitly if the external Smith implementation rejects an
  empty matrix: factors `[]`, product `1`, largest factor `1`;
- `n = 1` with entries `0` and `7`: factors `[x]` and `[x - 7]`;
- the zero matrix at `n = 3`: factors `[x, x, x]`, not
  `[1, 1, x^3]`;
- the identity at `n = 3`: three copies of `x - 1`;
- `diag(1, 1, 2)`: factors
  `[1, x - 1, (x - 1)(x - 2)]`, which includes a unit and a repeated
  eigenvalue;
- `diag(0, 1, 1)`: a singular matrix with factors
  `[1, x - 1, x(x - 1)]`;
- one nilpotent Jordan block of size `4`: factors
  `[1, 1, 1, x^4]`;
- nilpotent blocks of sizes `2` and `1`: factors `[1, x, x^2]`;
- a companion matrix of a non-palindromic monic degree-`6` polynomial:
  five units followed by that polynomial;
- a matrix and its transpose, checking exact agreement of the ordered lists;
- a matrix conjugated by an elementary transvection and its original, checking
  similarity invariance without computing a general inverse;
- a derogatory block diagonal matrix whose characteristic polynomial stays
  fixed while its invariant-factor partition differs from a cyclic matrix;
- entries near `2^63` over `Rat`, checking scalar embedding and coefficient
  growth.

**Lean-side checks.** These run in
`conformance/HexInvariantFactors/Conformance.lean` and include cases the matrix
fixture cannot encode.

- `factorsCert A S (S.left * charMatrix A) = true` on every small fixture;
- monicity, nonzeroness, divisibility order, factor count `n`, and degree sum
  `n` on every result;
- direct equality of the computed Smith diagonal with
  `PolyMatrix.invariantFactors (charMatrix A)` after the length cast;
- `factorProduct A = charPoly A` and `largestFactor A = minPoly A` in the
  companion conformance target;
- a `ZMod64 2` zero matrix and a repeated-block case, with handwritten expected
  factors. The existing `matrix` JSONL kind has no modulus, so these are not
  sent to the rational oracle;
- the negative check that product and largest factor do not certify the middle
  entries. Two nilpotent blocks of size `2` have factors
  `[1, 1, x^2, x^2]`, while blocks of sizes `2`, `1`, and `1` have factors
  `[1, x, x, x^2]`. Both products are `x^4` and both largest factors are
  `x^2`, but the ordered lists differ.

All conformance targets extend the existing job described in
[SPEC/CI.md](../CI.md).

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), add
`bench/HexInvariantFactors/Bench.lean` with no Mathlib import. The benchmark
imports `hex-invariant-factors` and therefore remains independent of
`hex-char-poly` and `hex-min-poly`.

**Input families.** Each family records wallclock, peak polynomial degree, and
the degree list of the answer. The `Rat` families additionally record peak
coefficient bit size.

- `random-dense-invariants`: random dense matrices over `ZMod64 p` and `Rat`
  across a dimension ladder. Most are cyclic, so the usual output has `n - 1`
  units and one degree-`n` factor.
- `jordan-partitions`: block diagonal nilpotent Jordan matrices with fixed `n`
  and varying block partitions. Their characteristic polynomial is always
  `x^n`, while the invariant-factor degree distribution ranges from all ones
  to one factor of degree `n`.
- `repeated-scalars`: diagonal matrices with controlled eigenvalue
  multiplicities. This measures long nonunit chains without coefficient
  randomness.
- `companion-invariants`: companion matrices of chosen monic polynomials, with
  the closed-form answer `1, ..., 1, p` checked by the driver.
- `singular-dense-invariants`: matrices with a forced zero row or dependent
  rows. Their characteristic matrices remain full polynomial rank and catch
  any mistaken shortcut from scalar rank.
- `similarity-invariants`: known examples conjugated by products of elementary
  transvections. Report the original and conjugated times separately.

Measure `PolyMatrix.snf` and `PolyMatrix.snfData` separately. The public answer
uses the first path, while certificate production needs transforms from the
second. This preserves the performance distinction made by
`hex-poly-smith`.

**Comparators.** Use the same polynomial-Smith implementation selected for
conformance, marked `informational`. Also record FLINT characteristic and
minimal polynomial timings in the external benchmark report, but do not sum
them and present the result as a competing invariant-factor algorithm. Those
operations return less information.

**Decision rules.** The public path remains direct polynomial Smith form.

1. A characteristic-matrix-specialised Smith loop is rejected unless it has a
   separate SPEC, proves agreement with `PolyMatrix.snf`, and wins across the
   upper half of both the dimension and Jordan-partition ladders. Version one
   contains no such loop.
2. A transform-producing public default is considered only if the measured
   `snfData / snf` ratio stays close to `1` across both coefficient types and
   dimensions. Until then, ordinary factor extraction does not accumulate
   transforms.
3. An external candidate may accelerate the computation only through
   `factorsCert`, with deterministic fallback to the native Smith path on
   absence or rejection. Equality of product and largest factor is not a
   sufficient acceptance check.

## Correspondence summary

The companion exposes the following facts together:

- every dense factor transports to the corresponding entry of
  `Module.Basis.SmithNormalForm` for `xI - A`;
- the transported factors are monic and form the divisibility chain that
  Mathlib's Smith structure itself omits;
- their product is `Matrix.charpoly` and also the executable
  `Hex.Matrix.charPoly`;
- the last factor generates the annihilator of the operator module and equals
  both Mathlib's `minpoly` and the executable `Hex.Matrix.minPoly`;
- dimension zero uses the empty direct sum, empty product `1`, and annihilator
  generator `1` throughout.

These statements complete the correspondence requested for version one. They
do not construct a basis in which `A` has rational canonical form.

## What is deliberately not here

**No rational canonical form.** An executable construction would need at
least:

- a companion matrix for each nonunit invariant factor;
- an executable block-diagonal assembly whose dimensions sum to `n`;
- a change-of-basis matrix over `F`, extracted from the polynomial Smith
  transforms or built from cyclic generators;
- a checker for invertibility of that basis and the conjugacy equation;
- a correspondence theorem identifying the blocks with the invariant
  factors.

The accepted Smith transforms alone do not directly provide the required
constant change of basis over `F`. Their entries lie in `F[x]`. Since none of
the remaining construction is specified here, calling a list of companion
blocks "rational canonical form" would be incomplete. It remains downstream
work.

**No characteristic-polynomial implementation.** The direct determinant
monicity lemma exists only to establish full Smith rank. The product comparison
imports and cites `Hex.Matrix.charPoly` in the companion.

**No minimal-polynomial implementation.** The computational layer never runs a
Krylov sequence. The largest-factor comparison imports and cites
`Hex.Matrix.minPoly` in the companion.

**No elementary divisors.** Factoring the invariant factors would restrict the
coefficient field to one with a factorisation implementation. It is a separate
consumer of this library.

**No alternate polynomial representation.** Dense polynomial matrices are the
accepted input of `hex-poly-smith`. A sparse or structured characteristic
matrix may become worthwhile only after a general sparse-matrix SPEC decides
its representation and measures Smith fill-in.

**No rectangular input.** Invariant factors of an arbitrary rectangular
polynomial matrix already belong to `hex-poly-smith`. This library is about a
linear endomorphism and accepts only `Matrix F n n`.

## File organisation

```text
HexInvariantFactors/
  CharacteristicMatrix.lean  -- charMatrix, transpose and determinant facts
  Factors.lean               -- invariantFactors, factorProduct, largestFactor
  Contracts.lean             -- monicity, chain, degree sum and edge cases
  Cert.lean                  -- factorsCert and its soundness
HexInvariantFactors.lean     -- umbrella
HexInvariantFactorsMathlib/
  CharacteristicMatrix.lean  -- equiv_charMatrix and product correspondence
  OperatorModule.lean        -- operatorQuotient, operatorEquiv, X action
  MinimalPolynomial.lean     -- annihilator and largest-factor correspondence
  CrossCheck.lean            -- crossCheck and its theorems
HexInvariantFactorsMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexInvariantFactors:
    deps: [HexPolySmith]
    mathlib: false
    done_through: 0
    status: draft
  HexInvariantFactorsMathlib:
    deps: [HexInvariantFactors, HexPolySmithMathlib,
           HexCharPolyMathlib, HexMinPolyMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

The conformance and bench projects follow the same dependency split. In
particular, the Mathlib-free benchmark does not import either independent
polynomial algorithm merely to perform a cross-check.

## Open questions

- **Whether the operator quotient equivalence should become reusable.** The
  equivalence between a matrix and the module presented by `xI - A` is useful
  beyond this library, but no second current consumer needs it. Keep it in the
  companion until one does.
- **Whether factor products should accept a previously computed vector.** The
  matrix convenience function is sufficient for version one. If consumers
  repeatedly need product, largest factor, and the full vector from one run,
  add a small result structure rather than recomputing Smith form. Benchmark
  evidence and real call sites should decide this API amendment.
