import HexGramSchmidt.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
Mathlib bridge lemmas for `hex-gram-schmidt`.

This module converts dense `Hex.Matrix` rows into the finite-dimensional real
vector space used by Mathlib's `gramSchmidt`, then states the rowwise
correspondence between the executable `Hex.GramSchmidt` basis and Mathlib's
orthogonalization process.
-/

namespace Hex
namespace GramSchmidtMathlib

/-- View a rational dense row as a vector in Mathlib's standard Euclidean
space on `Fin m`. -/
def rowToEuclidean (row : Vector Rat m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => (row[j] : ℝ))

/-- Cast a rational dense matrix into the real matrix space used by the bridge. -/
def castRatMatrix (b : Matrix Rat n m) : Matrix ℝ n m :=
  Vector.map (fun row => Vector.map (fun x : Rat => (x : ℝ)) row) b

/-- Cast an integer dense matrix into the rational matrix space of `HexGramSchmidt`. -/
def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- The row family fed to Mathlib's `gramSchmidt` for a rational matrix. -/
def ratRowFamily (b : Matrix Rat n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun i => rowToEuclidean (b.row i)

/-- The row family fed to Mathlib's `gramSchmidt` for an integer matrix. -/
def intRowFamily (b : Matrix Int n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  ratRowFamily (castIntMatrix b)

/-- The rational Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem rat_basis_row_eq_gramSchmidt (b : Matrix Rat n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) i := by
  sorry

/-- The integer Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem int_basis_row_eq_gramSchmidt (b : Matrix Int n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Int.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (intRowFamily b) i := by
  simpa [intRowFamily, castIntMatrix, Hex.GramSchmidt.Int.basis, Hex.GramSchmidt.Rat.basis]
    using rat_basis_row_eq_gramSchmidt (castIntMatrix b) i

end GramSchmidtMathlib
end Hex
