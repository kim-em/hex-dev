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

/-- Non-singular branch of the Cramer/Bareiss bridge: when the no-pivot
Bareiss pass over the Gram matrix reaches column `j` without recording a
singular step, the executable scaled coefficient agrees with the public
row-pivoted Bareiss determinant of the Cramer minor. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h_rows :=
    scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix b i j hji h_nonsing
  have h_scaled_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState
            (GramSchmidt.scaledCoeffMatrix b i j hji))).singularStep = none := by
    rw [scaledCoeffMatrix_eq_borderedMinor b i j hji]
    have h_sync :=
      (noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        (⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n) i
        (Nat.le_refl _) (Nat.le_of_lt hji)).2
    exact h_sync ▸ h_nonsing
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular
      (GramSchmidt.scaledCoeffMatrix b i j hji) h_scaled_nonsing
  have h_entry :
      GramSchmidt.entry (scaledCoeffs b) i j =
        (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState
            (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
          Fin.last j.val][Fin.last j.val] := by
    rw [scaledCoeffs_entry_eq_getArrayEntry]
    exact h_rows
  exact h_entry.trans h_bareiss.symm

/-- Cramer/Bareiss bridge: below the diagonal, the integral scaled
Gram-Schmidt coefficient is exactly the public Bareiss determinant of the
Cramer minor `scaledCoeffMatrix`. The proof splits on whether the no-pivot
Bareiss pass over `gramMatrix b` reaches column `j` without recording a
singular step:

- Non-singular branch: defer to
  `scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular`.
- Singular branch: both sides vanish — the executable scaled coefficient is
  zero by `scaledCoeffs_eq_zero_of_singularStep_lt` (the lifted lower-column
  singular lemma from #4166), and the public Bareiss determinant of the
  Cramer minor is zero by `Matrix.bareiss_eq_det` composed with
  `scaledCoeffMatrix_det_eq_zero_of_singularStep_lt`. The latter Mathlib-free
  helper internally lifts partial-pass singularity to the full
  `bareissNoPivotData` pass and applies the Cramer determinant identity.

This case-split avoids the transitive dependency on the private sorry
`scaledCoeffRows_lower_eq_scaledCoeffMatrix_bareiss` that the older chain
proof carried via `scaledCoeffs_eq_scaledCoeffMatrix_det`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      exact scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular b i j hji h_sing
  | some s =>
      have hsj : s < j.val := by
        have h := noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 :=
        scaledCoeffs_eq_zero_of_singularStep_lt b i j hji s h_sing hsj
      have h_det := scaledCoeffMatrix_det_eq_zero_of_singularStep_lt
        b i j hji s h_sing
      rw [h_lhs, Matrix.bareiss_eq_det, h_det]

end Int
end GramSchmidt
end Hex
