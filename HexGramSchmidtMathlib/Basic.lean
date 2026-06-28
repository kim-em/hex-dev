module

public import HexGramSchmidt.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

public section

/-!
Mathlib-side correspondence lemmas for `hex-gram-schmidt`.

This module converts dense `Hex.Matrix` rows into the finite-dimensional real
vector space used by Mathlib's `gramSchmidt`, then states the rowwise
correspondence between the executable `Hex.GramSchmidt` basis and Mathlib's
orthogonalization process.
-/

namespace Hex
namespace GramSchmidtMathlib

/-- View a rational dense row as a vector in Mathlib's standard Euclidean
space on `Fin m`. -/
@[expose]
def rowToEuclidean (row : Vector Rat m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => (row[j] : ℝ))

/-- Coordinate access commutes with `rowToEuclidean`: the `j`-th component of the
converted vector is the real cast of the `j`-th rational entry. -/
@[simp, grind =]
theorem rowToEuclidean_apply (row : Vector Rat m) (j : Fin m) :
    rowToEuclidean row j = (row[j] : ℝ) := by
  rfl

/-- `rowToEuclidean` sends the zero row to the zero vector. -/
@[simp, grind =]
theorem rowToEuclidean_zero :
    rowToEuclidean (0 : Vector Rat m) = 0 := by
  ext j
  simp [rowToEuclidean]

/-- `rowToEuclidean` is additive: it sends a rowwise sum to the sum of converted
vectors. -/
@[simp, grind =]
theorem rowToEuclidean_add (a b : Vector Rat m) :
    rowToEuclidean (a + b) = rowToEuclidean a + rowToEuclidean b := by
  ext j
  simp [rowToEuclidean]

/-- `rowToEuclidean` commutes with subtraction. -/
@[simp, grind =]
theorem rowToEuclidean_sub (a b : Vector Rat m) :
    rowToEuclidean (a - b) = rowToEuclidean a - rowToEuclidean b := by
  ext j
  simp [rowToEuclidean]

/-- `rowToEuclidean` is rational-linear: it sends a rational scalar multiple to the
corresponding real scalar multiple of the converted vector. -/
@[simp, grind =]
theorem rowToEuclidean_smul (c : Rat) (row : Vector Rat m) :
    rowToEuclidean (c • row) = (c : ℝ) • rowToEuclidean row := by
  ext j
  simp [rowToEuclidean]

/-- Cast an integer dense matrix into the rational matrix space of `HexGramSchmidt`. -/
@[expose]
def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- The row family fed to Mathlib's `gramSchmidt` for a rational matrix. -/
@[expose]
def ratRowFamily (b : Matrix Rat n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun i => rowToEuclidean (b.row i)

/-- The row family fed to Mathlib's `gramSchmidt` for an integer matrix. -/
@[expose]
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

/-- A strictly lower executable coefficient agrees, after casting to `ℝ`, with
Mathlib's projection coefficient for the corresponding converted rows. -/
theorem rat_coeffs_lower_projection_real (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    ((Hex.GramSchmidt.entry (Hex.GramSchmidt.Rat.coeffs b) i j : Rat) : ℝ) =
      inner ℝ (rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j))
          (rowToEuclidean (b.row i)) /
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 := by
  rw [Hex.GramSchmidt.Rat.coeffs_lower_projection_comm (b := b) hji]
  by_cases hnorm :
      Matrix.dot ((Hex.GramSchmidt.Rat.basis b).row j)
          ((Hex.GramSchmidt.Rat.basis b).row j) = 0
  · have hnorm_real :
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      rw [rowToEuclidean_inner]
      exact_mod_cast hnorm
    simp [hnorm, hnorm_real]
  ·
    have hnorm_real :
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 =
          ((Matrix.dot ((Hex.GramSchmidt.Rat.basis b).row j)
            ((Hex.GramSchmidt.Rat.basis b).row j) : Rat) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq]
      rw [rowToEuclidean_inner]
    simp [hnorm, rowToEuclidean_inner, hnorm_real]

private theorem rowToEuclidean_foldl_linear
    {α : Type*} (xs : List α) (c : α → Rat) (v : α → Vector Rat m)
    (acc : Vector Rat m) :
    rowToEuclidean (xs.foldl (fun acc x => acc + c x • v x) acc) =
      rowToEuclidean acc + (xs.map fun x => (c x : ℝ) • rowToEuclidean (v x)).sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc := acc + c x • v x)]
      simp [rowToEuclidean_add, rowToEuclidean_smul, add_assoc]

private theorem sum_fin_eq_sum_Iio {M : Type*} [AddCommMonoid M]
    (i : Fin n) (f : Fin n → M) :
    (∑ x : Fin i.val, f ⟨x.val, Nat.lt_trans x.isLt i.isLt⟩) =
      ∑ x ∈ Finset.Iio i, f x := by
  classical
  refine Finset.sum_bij
    (fun x _ => (⟨x.val, Nat.lt_trans x.isLt i.isLt⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro x _
    rw [Finset.mem_Iio]
    exact x.isLt
  · intro x _ y _ hxy
    apply Fin.ext
    exact congrArg (fun z : Fin n => z.val) hxy
  · intro y hy
    refine ⟨⟨y.val, ?_⟩, by simp, ?_⟩
    · simpa using hy
    · exact Fin.ext rfl
  · intro x _
    rfl

private theorem rowToEuclidean_prefixCombination_eq_Iio_sum
    (b : Matrix Rat n m) (i : Fin n)
    (hprev :
      ∀ j : Fin n, j.val < i.val →
        rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j) :
    rowToEuclidean
        (Hex.GramSchmidt.prefixCombination
          (Hex.GramSchmidt.Rat.coeffs b) (Hex.GramSchmidt.Rat.basis b) i.val i.isLt) =
      ∑ j ∈ Finset.Iio i,
        (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j) (ratRowFamily b i) /
            (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j := by
  classical
  unfold Hex.GramSchmidt.prefixCombination
  rw [rowToEuclidean_foldl_linear]
  simp only [rowToEuclidean_zero, zero_add]
  rw [← List.sum_toFinset _ (List.nodup_finRange i.val)]
  simpa [rat_coeffs_lower_projection_real, hprev, ratRowFamily] using
    sum_fin_eq_sum_Iio (i := i)
      (f := fun j =>
        (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)
            (rowToEuclidean (b.row i)) /
          (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)

/-- The rational Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem rat_basis_row_eq_gramSchmidt (b : Matrix Rat n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) i := by
  classical
  have hstrong :
      ∀ k : Nat, ∀ hk : k < n,
        rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row ⟨k, hk⟩) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let ik : Fin n := ⟨k, hk⟩
        have hprev :
            ∀ j : Fin n, j.val < ik.val →
              rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j) =
                InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j := by
          intro j hj
          exact ih j.val hj j.isLt
        have hdecomp :=
          congrArg rowToEuclidean
            (Hex.GramSchmidt.Rat.basis_decomposition (b := b) k hk)
        rw [rowToEuclidean_add,
          rowToEuclidean_prefixCombination_eq_Iio_sum (b := b) (i := ik) hprev] at hdecomp
        have hmath := InnerProductSpace.gramSchmidt_def'' ℝ (ratRowFamily b) ik
        change rowToEuclidean (b.row ik) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) ik +
            ∑ j ∈ Finset.Iio ik,
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)
                    (ratRowFamily b ik) /
                  (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
                InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j at hmath
        exact add_right_cancel (by rw [← hdecomp, hmath])
  exact hstrong i.val i.isLt

/-- The integer Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem int_basis_row_eq_gramSchmidt (b : Matrix Int n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Int.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (intRowFamily b) i := by
  simpa [intRowFamily, castIntMatrix, Hex.GramSchmidt.Int.basis, Hex.GramSchmidt.Rat.basis]
    using rat_basis_row_eq_gramSchmidt (castIntMatrix b) i

end GramSchmidtMathlib
end Hex
