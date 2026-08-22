# hex-char-poly-mathlib

Mathlib correspondence layer for
[`hex-char-poly`](https://github.com/leanprover/hex-char-poly).  It identifies
the executable Samuelson--Berkowitz output with Mathlib's
`Matrix.charpoly`, then transports the characteristic-polynomial theorems that
are intentionally absent from the Mathlib-free computational package.

## Main correspondence

```lean
namespace HexCharPolyMathlib

theorem equiv_charPoly (A : Hex.Matrix R n n) :
    HexPolyMathlib.equiv (Hex.Matrix.charPoly A) =
      Matrix.charpoly (HexMatrixMathlib.matrixEquiv A)

end HexCharPolyMathlib
```

The proof follows the executable recursion on trailing principal blocks.  Its
step theorem proves the bordered determinant identity through the adjugate
coefficient recurrence, identifies the row--block--column moments with the
Toeplitz column, and then inducts over the block size.  There are no axioms or
unfinished proof obligations.

## Transported results

The public umbrella also provides:

```lean
theorem equiv_evalMatrix (p : Hex.DensePoly R) (A : Hex.Matrix R n n) :
  matrixEquiv (Hex.Matrix.evalMatrix p A) =
    Polynomial.aeval (matrixEquiv A) (HexPolyMathlib.equiv p)

theorem evalMatrix_charPoly (A : Hex.Matrix R n n) :
  Hex.Matrix.evalMatrix (Hex.Matrix.charPoly A) A = 0

theorem eval_charPoly (A : Hex.Matrix R n n) (t : R) :
  (Hex.Matrix.charPoly A).eval t =
    Hex.Matrix.det (t • Hex.Matrix.identity n - A)

theorem coeff_zero_charPoly (A : Hex.Matrix R n n) :
  (Hex.Matrix.charPoly A).coeff 0 = (-1) ^ n * Hex.Matrix.det A

theorem matrixEquiv_trace (A : Hex.Matrix R n n) :
  Hex.Matrix.trace A = Matrix.trace (matrixEquiv A)

theorem charPoly_transpose (A : Hex.Matrix R n n) :
  Hex.Matrix.charPoly A.transpose = Hex.Matrix.charPoly A

theorem charPoly_conj (A U V : Hex.Matrix R n n)
    (h : U * V = Hex.Matrix.identity n) :
  Hex.Matrix.charPoly (U * A * V) = Hex.Matrix.charPoly A
```

Thus the executable polynomial satisfies Cayley--Hamilton, evaluates as the
determinant of `tI-A`, has the expected determinant and trace coefficients,
and is invariant under transpose and conjugation by an explicitly supplied
inverse.
