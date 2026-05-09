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

private theorem cast_foldl_dotProduct_rat
    (xs : List (Fin m)) (a b : Vector Rat m) (acc : Rat) :
    ((xs.foldl (fun acc i => acc + a[i] * b[i]) acc : Rat) : ℝ) =
      (acc : ℝ) + (xs.map fun i => ((a[i] : Rat) : ℝ) * ((b[i] : Rat) : ℝ)).sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc := acc + a[i] * b[i])]
      simp only [Rat.cast_add, Rat.cast_mul]
      ring

/-- Mathlib's real inner product on converted rows agrees with the executable
rational dense dot product after casting to `ℝ`. -/
theorem rowToEuclidean_inner (a b : Vector Rat m) :
    inner ℝ (rowToEuclidean a) (rowToEuclidean b) =
      ((Matrix.dot (u := a) (v := b) : Rat) : ℝ) := by
  rw [PiLp.inner_apply]
  simp [rowToEuclidean, PiLp.toLp_apply, real_inner_eq_re_inner,
    RCLike.inner_apply, mul_comm]
  rw [Matrix.dot, Hex.Vector.dotProduct, cast_foldl_dotProduct_rat]
  simp only [Rat.cast_zero, zero_add]
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  simp [List.toFinset_finRange]

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
