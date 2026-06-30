/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Basic.Rat
import all HexGramSchmidt.Basic.Rat

public section

/-!
Integer-cast layer of the Gram-Schmidt surface for `hex-gram-schmidt`.

This module defines the rational-valued `basis` and `coeffs` of an integer
input matrix (via `GramSchmidt.castIntMatrix`) and lifts the rational results
of `HexGramSchmidt/Basic/Rat.lean` to the integer setting: the leading-row,
orthogonality, triangular-decomposition, and prefix-span facts (`basis_zero`,
`basis_orthogonal`, `basis_decomposition`, `coeffs_diag`, `coeffs_upper`,
`basis_span`), together with the behaviour of `basis`/`coeffs` under the
integer row operations `Matrix.rowAdd` and adjacent `Matrix.rowSwap` used by
the LLL size-reduction and swap steps.
-/
namespace Hex
namespace GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis for an integer matrix, viewed in
`Rat` after coefficient divisions. -/
@[expose]
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix (GramSchmidt.castIntMatrix b)

/-- The Gram-Schmidt coefficient matrix for an integer input matrix. -/
@[expose]
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix (GramSchmidt.castIntMatrix b) (basis b)

/-- Gram-Schmidt leaves the first row untouched: the leading basis row of an
integer matrix is its leading input row cast into `Rat`. -/
@[simp, grind =]
theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ =
      Vector.map (fun x : Int => (x : Rat)) (b.row ⟨0, hn⟩) := by
  simpa [basis, GramSchmidt.basisMatrix, GramSchmidt.castIntMatrix, Matrix.row,
    Hex.Matrix.getRow, Fin.getElem_fin] using
    GramSchmidt.basisRows_head (b := GramSchmidt.castIntMatrix b) hn

/-- Distinct Gram-Schmidt basis rows of an integer matrix (taken in `Rat`) are
mutually orthogonal. -/
@[grind =]
theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row ⟨i, hi⟩).dotProduct ((basis b).row ⟨j, hj⟩) = 0 := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_orthogonal (b := GramSchmidt.castIntMatrix b) i j hi hj hij

/-- The triangular factorization for an integer matrix: each input row, cast
into `Rat`, equals its orthogonalized basis row plus the coefficient-weighted
combination of the earlier basis rows. -/
theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩) =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs, GramSchmidt.castIntMatrix, GramSchmidt.Rat.basis,
    GramSchmidt.Rat.coeffs, Matrix.row, Hex.Matrix.getRow, Fin.getElem_fin] using
      GramSchmidt.Rat.basis_decomposition (b := GramSchmidt.castIntMatrix b) i hi

/-- The coefficient matrix of an integer input has unit diagonal: each row
enters its own decomposition with weight `1`. -/
@[simp, grind =]
theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

/-- The coefficient matrix of an integer input is lower triangular: entries
strictly above the diagonal vanish. -/
@[grind =]
theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

private theorem getElem_castIntMatrix (b : Matrix Int n m) (r : Fin n) (k : Fin m) :
    (GramSchmidt.castIntMatrix b)[r][k] = (b[r][k] : Rat) := by
  simp [GramSchmidt.castIntMatrix, Hex.Matrix.getRow, Fin.getElem_fin]

private theorem castIntMatrix_rowAdd (b : Matrix Int n m) (src dst : Fin n) (c : Int) :
    GramSchmidt.castIntMatrix (Matrix.rowAdd b src dst c) =
      Matrix.rowAdd (GramSchmidt.castIntMatrix b) src dst (c : Rat) := by
  apply Hex.Matrix.ext_getElem
  intro r k
  rw [getElem_castIntMatrix, Matrix.getElem_rowAdd, Matrix.getElem_rowAdd,
    getElem_castIntMatrix, getElem_castIntMatrix]
  by_cases hdst : r = dst
  · simp only [hdst, if_true]
    push_cast
    rfl
  · simp only [hdst, if_false, getElem_castIntMatrix]

private theorem castIntMatrix_rowSwap (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.castIntMatrix (Matrix.rowSwap b i j) =
      Matrix.rowSwap (GramSchmidt.castIntMatrix b) i j := by
  apply Hex.Matrix.ext_getElem
  intro r k
  rw [getElem_castIntMatrix, Matrix.getElem_rowSwap, Matrix.getElem_rowSwap,
    getElem_castIntMatrix, getElem_castIntMatrix, getElem_castIntMatrix]
  by_cases hrj : r = j
  · simp [hrj]
  · by_cases hri : r = i <;> simp [hrj, hri] <;> split <;> rfl

/-- The integer Gram-Schmidt basis is invariant under adding an integer
multiple of an earlier row to a later row. -/
@[grind =]
theorem basis_rowAdd (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowAdd] using
    GramSchmidt.Rat.basis_rowAdd
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst

/-- Swapping rows `km1` and `k` of an integer matrix leaves every basis row
before the pair unchanged. -/
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_of_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1k hi

/-- After swapping adjacent rows `km1, k` of an integer matrix, the basis row at
the lower index `km1` becomes the old basis row `k` plus its projection
coefficient times the old basis row `km1`. -/
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_adjacent_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1

/-- Swapping the adjacent rows `km1, k` of an integer matrix leaves every basis
row after the pair unchanged. -/
@[grind =]
theorem basis_rowSwap_of_after (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_of_after
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1 hi

/-- After swapping adjacent rows `km1, k` of an integer matrix (assuming the
swapped pivot is nonzero), the basis row at index `k` is the explicit two-term
combination of the old basis rows `km1, k`. -/
theorem basis_rowSwap_adjacent_curr (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Vector.dotProduct
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let mu := GramSchmidt.entry (coeffs b) k km1
    let swappedPrev := curr + mu • prev
    (basis (Matrix.rowSwap b km1 k)).row k =
      (curr.dotProduct curr / swappedPrev.dotProduct swappedPrev) • prev -
        (mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) • curr := by
  have hnormRat :
      Vector.dotProduct
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1)
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1) ≠ 0 := by
    simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs] using hnorm
  simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_adjacent_curr
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1 hnormRat

/-- After an adjacent swap of an integer matrix, the coefficient at the lower
row `km1` against an earlier column `j` equals the old coefficient at row `k`
against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj

/-- Dual of `coeffs_rowSwap_adjacent_lower_prev` for an integer matrix: after an
adjacent swap, the coefficient at row `k` against an earlier column `j` equals
the old coefficient at row `km1` against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_curr
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj

/-- The explicit value of the new pivot coefficient (row `k`, column `km1`)
after an adjacent swap of an integer matrix. -/
theorem coeffs_rowSwap_adjacent_pivot (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Vector.dotProduct
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let mu := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + mu • prev
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k km1 =
      mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev := by
  have hnormRat :
      Vector.dotProduct
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1)
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1) ≠ 0 := by
    simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs] using hnorm
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_pivot
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1 hnormRat

/-- Coefficient entries for a row and column both lying before the swapped pair
are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hji

/-- Coefficient entries for a row after the swapped pair against a column before
it are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_low
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj

/-- Coefficient entries for a row and column both lying after the swapped pair
are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_high
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj hji

/-- Under integer row-add with `src < dst`, lower coefficients in the
destination row update linearly below the pivot source column. -/
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Int n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        (c : Rat) * GramSchmidt.entry (coeffs b) src col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_lower
      (b := GramSchmidt.castIntMatrix b) (col := col) (src := src) (dst := dst)
      hcolsrc hsrcdst (c := (c : Rat))

/-- Under integer row-add with `src < dst`, the pivot coefficient in the
destination row increases by the added integer multiple. -/
@[grind =]
theorem coeffs_rowAdd_pivot (b : Matrix Int n m) (src dst : Fin n)
    (hsrcdst : src.val < dst.val) (c : Int)
    (hnorm : ((basis b).row src).dotProduct ((basis b).row src) ≠ 0) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst src =
      GramSchmidt.entry (coeffs b) dst src + (c : Rat) := by
  have hnormRat :
      ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row src).dotProduct
          ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row src) ≠ 0 := by
    simpa [basis, GramSchmidt.Rat.basis] using hnorm
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_pivot
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) hsrcdst
      (c := (c : Rat)) hnormRat

/-- Under integer row-add with `src < col < dst`, destination-row coefficients
above the pivot source column are preserved. -/
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Int n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_above_pivot
      (b := GramSchmidt.castIntMatrix b) (src := src) (col := col) (dst := dst)
      hsrccol hcoldst (c := (c : Rat))

/-- An integer row-add only changes the destination row of the coefficient
matrix. -/
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_other_row
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst row hrow

/-- Orthogonalization preserves the row space of each prefix for an integer
matrix: the first `i + 1` basis rows span exactly the vectors spanned by the
first `i + 1` input rows cast into `Rat`. -/
theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan (GramSchmidt.castIntMatrix b) i hi v := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_span (b := GramSchmidt.castIntMatrix b) i hi

end GramSchmidt.Int
end Hex
