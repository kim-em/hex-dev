import VersoManual

import HexGramSchmidt

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGramSchmidt: Gram-Schmidt orthogonalization" =>
%%%
tag := "hex-gram-schmidt"
%%%

# Introduction
%%%
tag := "hex-gram-schmidt-intro"
%%%

`HexGramSchmidt` is the Gram-Schmidt orthogonalization layer of the
stack. Given a matrix whose rows are the input vectors, it produces the
orthogonal basis obtained by subtracting from each row its projection
onto the earlier rows, together with the lower-unitriangular matrix of
projection coefficients that reconstructs the input. The whole surface
is phrased over the dense {name}`Hex.Matrix` representation: operations
take and return *whole matrices* (`basis b : Matrix Rat n m`,
`coeffs b : Matrix Rat n n`) rather than indexed single-entry
functions, and rows are addressed by `Nat` indices with explicit bounds
rather than `Fin`.

The library carries two parallel surfaces. The `Hex.GramSchmidt.Rat`
namespace orthogonalizes a rational matrix directly; the
`Hex.GramSchmidt.Int` namespace casts an integer matrix into `Rat`
before orthogonalizing, and adds the determinant-driven *integral*
surface — the leading Gram determinants and the integer scaled
coefficient matrix — that downstream lattice code uses to stay in exact
arithmetic. The orthogonal basis and the rational coefficient matrix
involve genuine division, so {name}`Hex.GramSchmidt.Rat.basis` and
{name}`Hex.GramSchmidt.Rat.coeffs` are `noncomputable`; the
determinant surface {name}`Hex.GramSchmidt.Int.gramDet` and
{name}`Hex.GramSchmidt.Int.scaledCoeffs` is computable and drives the
worked examples below.

`HexGramSchmidt` is Mathlib-free and depends only on `HexMatrix`. It is
a dependency of `HexLLL`, supplying the orthogonalization and the
exact-update formulas that lattice reduction needs, but it is logically
independent of LLL; see
{ref "hex-gram-schmidt-cross-references"}[Cross-references].

# Core operations
%%%
tag := "hex-gram-schmidt-core"
%%%

The two fundamental constructions are the orthogonal basis and the
coefficient matrix. The basis rows are mutually orthogonal; the
coefficient matrix is lower-unitriangular and reconstructs the input as
`coeffs · basis`. Both come in a rational and an integer flavour, the
integer one casting its input into `Rat` first.

{docstring Hex.GramSchmidt.Rat.basis}

{docstring Hex.GramSchmidt.Rat.coeffs}

{docstring Hex.GramSchmidt.Int.basis}

{docstring Hex.GramSchmidt.Int.coeffs}

Because the basis and coefficient matrices divide, they are
`noncomputable` and are documented here by signature. The integer
surface adds two *computable* operations that stay in exact arithmetic.
The leading Gram determinants are the determinants of the leading
principal Gram minors `B Bᵀ` — these are the squared volumes of the
prefix sublattices — and the scaled coefficient matrix clears the
denominators of the rational coefficients against them.

{docstring Hex.GramSchmidt.Int.gramDet}

{docstring Hex.GramSchmidt.Int.scaledCoeffs}

The scaled coefficients are packaged together with the Gram-determinant
vector inside {name}`Hex.GramSchmidt.Int.Data`; `scaledCoeffs` projects
out its coefficient matrix.

## Worked example: Gram determinants and scaled coefficients
%%%
tag := "hex-gram-schmidt-worked"
%%%

The block below works over the integer matrix with rows `(1,1,0)`,
`(1,0,1)`, `(0,1,1)`. It reads off the leading Gram determinants and the
scaled coefficient matrix, then exercises a size-reduction row
operation. Each `#guard` is checked when the chapter is built, so the
expected values are guaranteed to match the executable implementation.

```lean
open Hex Hex.GramSchmidt Hex.GramSchmidt.Int

namespace HexGramSchmidtChapter

-- A 3×3 integer matrix with rows
--   (1,1,0), (1,0,1), (0,1,1).
private def m : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 2, 2 => 1
    | _, _ => 0

private abbrev i0 : Fin 3 := ⟨0, by decide⟩
private abbrev i1 : Fin 3 := ⟨1, by decide⟩
private abbrev i2 : Fin 3 := ⟨2, by decide⟩

-- Leading Gram determinants d_0 .. d_3. The empty
-- prefix is 1 by convention; d_k is the determinant
-- of the k×k leading Gram minor of the input.
#guard gramDet m 0 (by decide) = 1
#guard gramDet m 1 (by decide) = 2
#guard gramDet m 2 (by decide) = 3
#guard gramDet m 3 (by decide) = 4

-- scaledCoeffs stores d_{j+1} on the diagonal ...
#guard entry (scaledCoeffs m) i0 i0 = 2
#guard entry (scaledCoeffs m) i1 i1 = 3
#guard entry (scaledCoeffs m) i2 i2 = 4
-- ... the integral coefficients d_{j+1} * μ_{i,j}
-- strictly below it ...
#guard entry (scaledCoeffs m) i1 i0 = 1
#guard entry (scaledCoeffs m) i2 i0 = 1
#guard entry (scaledCoeffs m) i2 i1 = 1
-- ... and zeros above the diagonal.
#guard entry (scaledCoeffs m) i0 i1 = 0
#guard entry (scaledCoeffs m) i1 i2 = 0

-- Size-reducing row 2 against row 0 by 2 replaces
-- b[2] with b[2] - 2·b[0]; here entry (2,0) drops
-- to -2 and the diagonal entry (2,2) is untouched.
#guard entry (sizeReduce m i0 i2 2) i2 i0 = -2
#guard entry (sizeReduce m i0 i2 2) i2 i2 = 1

end HexGramSchmidtChapter
```

# Key correctness theorems
%%%
tag := "hex-gram-schmidt-correctness"
%%%

The defining guarantee is orthogonality: distinct basis rows have zero
dot product. The statement is given over both the rational and the
integer input (the latter taken in `Rat`).

{docstring Hex.GramSchmidt.Rat.basis_orthogonal}

{docstring Hex.GramSchmidt.Int.basis_orthogonal}

The basis and coefficient matrices together factor the input. Each
input row equals its orthogonalized basis row plus the
coefficient-weighted combination of the earlier basis rows — the
triangular factorization `b = coeffs · basis`, stated row by row.

{docstring Hex.GramSchmidt.Rat.basis_decomposition}

{docstring Hex.GramSchmidt.Int.basis_decomposition}

The coefficient matrix is lower-unitriangular, and its strictly
lower entries are exactly the projection coefficients of the input row
onto the earlier basis row.

{docstring Hex.GramSchmidt.Rat.coeffs_diag}

{docstring Hex.GramSchmidt.Rat.coeffs_upper}

{docstring Hex.GramSchmidt.Rat.coeffs_lower_projection}

# Row-operation updates
%%%
tag := "hex-gram-schmidt-updates"
%%%

Lattice reduction modifies the input by elementary row operations and
needs to know how the Gram-Schmidt data changes. `HexGramSchmidt`
packages the two operations LLL uses — size reduction and adjacent swap
— and states the resulting update formulas. The executable row
operations themselves live in `HexMatrix`; this layer supplies the
`HexGramSchmidt`-level API for reasoning about them.

{docstring Hex.GramSchmidt.Int.sizeReduce}

{docstring Hex.GramSchmidt.Int.adjacentSwap}

Size reduction subtracts an integer multiple of an earlier row from a
later one. This is a unimodular operation that preserves the orthogonal
profile, so it leaves the entire Gram-Schmidt basis unchanged — LLL can
size-reduce freely without disturbing the orthogonalized vectors or the
Gram determinants that the swap step depends on.

{docstring Hex.GramSchmidt.Int.basis_sizeReduce}

An adjacent swap exchanges rows `k - 1` and `k`, and the two basis rows
at those positions change. The update formulas give the new vectors as
explicit closed forms in the old data, so a caller can recompute the
updated orthogonal vectors and their norms without rerunning
Gram-Schmidt.

{docstring Hex.GramSchmidt.Int.basis_adjacentSwap_prev}

{docstring Hex.GramSchmidt.Int.basis_adjacentSwap_curr}

# Cross-references
%%%
tag := "hex-gram-schmidt-cross-references"
%%%

`HexGramSchmidt` sits one level above `HexMatrix` and below the lattice
layer:

* `HexMatrix` supplies the dense {name}`Hex.Matrix` representation and
  the row operations (`rowAdd`, `rowSwap`) that the
  {ref "hex-gram-schmidt-updates"}[update formulas] reason about. The
  orthogonalization in this chapter is built entirely on that
  representation.
* `HexGramSchmidtMathlib` is the correspondence library: it re-exports
  this executable theory as theorems about Mathlib's `LinearMap` and
  `Matrix` Gram-Schmidt, so the computational results here transfer to
  the abstract setting. The Mathlib dependency lives entirely on that
  side of the boundary; `HexGramSchmidt` itself imports only `HexMatrix`
  and `Std`.
* `HexLLL` consumes the {ref "hex-gram-schmidt-core"}[integral surface]
  — the Gram determinants and scaled coefficients — and the
  {ref "hex-gram-schmidt-updates"}[exact update formulas] to drive
  lattice reduction in integer arithmetic. `HexGramSchmidt` is logically
  independent of LLL: it states the orthogonalization and its updates
  without reference to the reduction algorithm that uses them.
