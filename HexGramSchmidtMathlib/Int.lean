import HexGramSchmidt.Int

/-!
Mathlib bridge lemma for the executable Cramer-style scaled coefficient
matrix and the public Bareiss surface.

The Mathlib-free file `HexGramSchmidt/Int.lean` packages the executable
scaled-coefficient array entry as the no-pivot Bareiss trailing value on
`GramSchmidt.scaledCoeffMatrix` (via `scaledCoeffRows_lower_eq_…`). The
public Bareiss algorithm `Matrix.bareiss`, however, may insert a row swap
when a diagonal pivot is zero, so the executable array entry need not
match the public Bareiss value on the Cramer minor without crossing to
`Matrix.bareiss_eq_det`: the geometric vanishing in the singular branch
is visible only through the Leibniz determinant.

Per `SPEC/Libraries/hex-gram-schmidt.md` ("Proof path governs placement,
not just statement"), this bridge therefore lives in
`HexGramSchmidtMathlib`. The proof consumes the existing
`Matrix.bareiss_eq_det` sorry in `HexMatrix/Bareiss.lean`, which is owned
by `hex-matrix-mathlib`.
-/

namespace Hex
namespace GramSchmidt
namespace Int

/-- Cramer/Bareiss bridge: below the diagonal, the integral scaled
Gram-Schmidt coefficient is exactly the public Bareiss determinant of the
Cramer minor `scaledCoeffMatrix`. This is the `bareiss`-form companion of
the existing Mathlib-free `scaledCoeffs_eq_scaledCoeffMatrix_det`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  rw [scaledCoeffs_eq_scaledCoeffMatrix_det b i j hji,
    Matrix.bareiss_eq_det]

end Int
end GramSchmidt
end Hex
