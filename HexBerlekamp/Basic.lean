import HexMatrix
import HexPolyFp

/-!
Executable Berlekamp-matrix support for `hex-berlekamp`.

This module builds the Berlekamp matrix `Q_f` for a monic polynomial
`f : FpPoly p` by expressing the Frobenius image of each monomial basis vector
in the quotient basis `{1, X, ..., X^(n - 1)}`. It also exposes the fixed-space
matrix `Q_f - I` together with a kernel wrapper that reuses `HexMatrix`'s
nullspace API and converts basis vectors back into polynomial representatives.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- The basis size used for the Berlekamp matrix of `f`. -/
def basisSize (f : FpPoly p) : Nat :=
  f.degree?.getD 0

/-- Read a polynomial's first `degree f` coefficients as a vector. -/
def coeffVector (f g : FpPoly p) : Vector (ZMod64 p) (basisSize f) :=
  Vector.ofFn fun i => g.coeff i.val

/--
The `j`-th Berlekamp-matrix column, obtained by reducing
`(X^p mod f)^j` modulo `f` and reading the result in the monomial basis.
-/
def berlekampColumn (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (j : Fin (basisSize f)) : Vector (ZMod64 p) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let image := FpPoly.powModMonic frobX f hmonic j.val
  coeffVector f image

/--
Iteratively build the array of Berlekamp-matrix column polynomials
`[1, frobX, frobX^2, …, frobX^(n - 1)]`, each reduced modulo `f`.
Each step costs one polynomial product and one monic reduction, both
quadratic in `n`, so the array of `n` columns is built in `O(n^3)` total.
-/
private def berlekampColumnPolys (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (frobX : FpPoly p) : Nat → FpPoly p → Array (FpPoly p) → Array (FpPoly p)
  | 0, _, acc => acc
  | k + 1, current, acc =>
      berlekampColumnPolys f hmonic frobX k
        (FpPoly.modByMonic f (current * frobX) hmonic) (acc.push current)

/--
The Berlekamp matrix `Q_f`, whose `j`-th column records the coordinates of
`X^(p * j) mod f` in the basis `{1, X, ..., X^(n - 1)}`. Columns are computed
iteratively from the recurrence `column (j + 1) = column j * (X^p mod f) mod f`
to avoid the per-column fast-exponentiation log factor.
-/
def berlekampMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let polys := berlekampColumnPolys f hmonic frobX (basisSize f) 1 #[]
  Matrix.ofFn fun i j => (polys[j.val]?.getD 0).coeff i.val

/-- The fixed-space matrix `Q_f - I` used in Berlekamp's kernel computation. -/
def fixedSpaceMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let Q := berlekampMatrix f hmonic
  Matrix.ofFn fun i j => Q[i][j] - if i = j then 1 else 0

/-- Convert a coefficient vector back to its polynomial representative. -/
def vectorToPoly {n : Nat} (v : Vector (ZMod64 p) n) : FpPoly p :=
  FpPoly.ofCoeffs v.toArray

/--
The fixed-space kernel of `Q_f - I`, reusing `HexMatrix.nullspace` instead of a
Berlekamp-local linear-algebra implementation.
-/
def fixedSpaceKernelVectors (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    Vector (Vector (ZMod64 p) (basisSize f))
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix f hmonic)) :=
  Matrix.nullspace (fixedSpaceMatrix f hmonic)

/-- The fixed-space kernel basis converted back to polynomial representatives. -/
def fixedSpaceKernel (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    Vector (FpPoly p)
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix f hmonic)) :=
  Vector.ofFn fun i => vectorToPoly ((fixedSpaceKernelVectors f hmonic).get i)

end Berlekamp

end Hex
