/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Basic.Linearity
import all HexGramSchmidt.Basic.Linearity

public section

/-!
Rational Gram-Schmidt API for `hex-gram-schmidt`.

This module wraps the executable kernel into the rational-valued `basis` and
`coeffs` of a `Matrix Rat n m` and proves their defining properties: the
leading row is untouched (`basis_zero`), distinct basis rows are orthogonal
(`basis_orthogonal`), the triangular factorization `b = coeffs · basis`
(`basis_decomposition`), and the unit-diagonal / lower-triangular shape of
`coeffs` (`coeffs_diag`, `coeffs_upper`, `coeffs_lower_projection`). It also
tracks how `basis` and `coeffs` transform under `Matrix.rowAdd` and adjacent
`Matrix.rowSwap` (the explicit re-orthogonalization formulas
`basis_rowSwap_adjacent_prev`/`_curr` and the coefficient updates), and proves
that orthogonalization preserves every row-prefix span (`basis_span`). These
are the rational facts the integer-cast layer lifts.
-/
namespace Hex
namespace GramSchmidt.Rat

/-- The Gram-Schmidt orthogonal basis for a rational matrix. -/
@[expose]
noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix b

/-- The Gram-Schmidt coefficient matrix for a rational input matrix. -/
@[expose]
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix b (basis b)

/-- Gram-Schmidt leaves the first row untouched: the leading basis row of a
rational matrix is its leading input row. -/
@[simp, grind =]
theorem basis_zero (b : Matrix Rat n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ = b.row ⟨0, hn⟩ := by
  simpa [basis, GramSchmidt.basisMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := b) hn

/-- The defining guarantee of the construction: distinct rational Gram-Schmidt
basis rows are mutually orthogonal (their dot product is zero). -/
@[grind =]
theorem basis_orthogonal (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row ⟨i, hi⟩).dotProduct ((basis b).row ⟨j, hj⟩) = 0 := by
  rw [basis, GramSchmidt.basisMatrix_row_eq_basisRows_get!,
    GramSchmidt.basisMatrix_row_eq_basisRows_get!]
  exact GramSchmidt.basisRows_get!_dot_eq_zero b i j hi hj hij

/-- The triangular factorization `b = coeffs · basis`, stated row by row: each
rational input row equals its orthogonalized basis row plus the
coefficient-weighted combination of the earlier basis rows. -/
theorem basis_decomposition (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs] using
    GramSchmidt.basisMatrix_reconstruction_invariant (b := b) i hi

/-- The rational coefficient matrix has unit diagonal: each input row enters its
own decomposition with weight `1`. -/
@[simp, grind =]
theorem coeffs_diag (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

/-- The rational coefficient matrix is lower triangular: entries strictly above
the diagonal vanish, since a row only combines basis rows with smaller index. -/
@[grind =]
theorem coeffs_upper (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

/-- Strictly lower-triangular coefficient entries are the rational projection
coefficient of the input row onto the earlier generated basis row. -/
theorem coeffs_lower_projection (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if ((basis b).row j).dotProduct ((basis b).row j) = 0 then 0
       else
        (b.row i).dotProduct ((basis b).row j) /
          ((basis b).row j).dotProduct ((basis b).row j)) := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
    GramSchmidt.projectionCoeff, Matrix.row, hji]

/-- Lower coefficient entries, with the dot product oriented to match
Mathlib's projection coefficient numerator. -/
theorem coeffs_lower_projection_comm (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if ((basis b).row j).dotProduct ((basis b).row j) = 0 then 0
       else
        ((basis b).row j).dotProduct (b.row i) /
          ((basis b).row j).dotProduct ((basis b).row j)) := by
  rw [coeffs_lower_projection (b := b) hji]
  by_cases hnorm : ((basis b).row j).dotProduct ((basis b).row j) = 0
  · simp [hnorm]
  · simp [hnorm, GramSchmidt.dot_comm_rat]

/-- The Gram-Schmidt basis is invariant under adding a scalar multiple of an
earlier row to a later row. This is the rational size-reduction update used by
the integer wrappers. -/
@[grind =]
theorem basis_rowAdd (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis] using
    GramSchmidt.basisMatrix_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst

/-- Swapping rows `km1` and `k` leaves every basis row before the pair
unchanged, since each Gram-Schmidt output row depends only on the input prefix
up to its own index. -/
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis] using
    GramSchmidt.basisMatrix_rowSwap (b := b) (km1 := km1) (k := k)
      (i := i) hkm1k hi

/-- After swapping the adjacent rows `km1, k`, the basis row at the lower index
`km1` becomes the old basis row `k` plus its projection coefficient times the
old basis row `km1`. The explicit re-orthogonalization formula for the first
vector of the swapped pair. -/
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Rat n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  have hraw :=
    GramSchmidt.basisMatrix_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
  have hlt : km1.val < k.val := by omega
  have hcoeff :
      GramSchmidt.projectionCoeff (b.row k) ((GramSchmidt.basisMatrix b).row km1) =
        GramSchmidt.entry (coeffs b) k km1 := by
    simp [coeffs, basis, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
      GramSchmidt.projectionCoeff, Matrix.row, hlt]
  simpa [basis, hcoeff] using hraw

private theorem projectionCoeff_row_later_basis_eq_zero
    (b : Matrix Rat n m) (src col : Fin n) (hsrccol : src.val < col.val) :
    GramSchmidt.projectionCoeff (b.row src) ((basis b).row col) = 0 := by
  have hsrc_toList : b.toList[src.val]! = b.row src := by simp [Matrix.row]
  have hbasis_col :
      (basis b).row col = (GramSchmidt.basisRows b.toList)[col.val]! := by
    simpa [basis] using
      GramSchmidt.basisMatrix_row_eq_basisRows_get! (b := b) col.val col.isLt
  have hreduce :
      GramSchmidt.reduceAgainstBasis
          ((GramSchmidt.basisRows b.toList).take col.val).reverse (b.row src) = 0 := by
    have key :=
      GramSchmidt.reduceAgainstBasis_basisRows_take_source_eq_zero
        (rows := b.toList) (j := src.val) (k := col.val) hsrccol
        (by simp [Vector.length_toList, Nat.le_of_lt col.isLt])
    rw [hsrc_toList] at key
    exact key
  have hproj :=
    GramSchmidt.projectionCoeff_reduceAgainstBasis_eq
      (basisRev := ((GramSchmidt.basisRows b.toList).take col.val).reverse)
      (row := b.row src) (basisRow := (basis b).row col)
      (by
        intro other hother
        rw [List.mem_reverse] at hother
        rw [List.mem_iff_getElem] at hother
        obtain ⟨idx, hidx, hget⟩ := hother
        have htake_len : ((GramSchmidt.basisRows b.toList).take col.val).length = col.val := by
          rw [List.length_take]
          have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
            simp [GramSchmidt.basisRows_length]
          omega
        have hidx_col : idx < col.val := by
          rw [htake_len] at hidx
          exact hidx
        have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
          simp [GramSchmidt.basisRows_length]
        have hidx_basis : idx < (GramSchmidt.basisRows b.toList).length := by
          rw [hbasis_len]
          exact Nat.lt_trans hidx_col col.isLt
        have hother_get :
            other = (GramSchmidt.basisRows b.toList)[idx]! := by
          rw [← hget, List.getElem_take]
          simp [hidx_basis]
        rw [hother_get, hbasis_col]
        exact GramSchmidt.basisRows_get!_dot_eq_zero
          (b := b) idx col.val (Nat.lt_trans hidx_col col.isLt) col.isLt
          (Nat.ne_of_lt hidx_col))
  rw [hreduce] at hproj
  have hzero : GramSchmidt.projectionCoeff (0 : Vector Rat m) ((basis b).row col) = 0 := by
    by_cases hnorm : ((basis b).row col).dotProduct ((basis b).row col) = 0
    · simp [GramSchmidt.projectionCoeff, hnorm]
    · have hdot : (0 : Vector Rat m).dotProduct ((basis b).row col) = 0 := by
        unfold Vector.dotProduct
        induction List.finRange m with
        | nil => rfl
        | cons idx rest ih =>
            simp only [List.foldl_cons]
            have hentry : (0 : Vector Rat m)[idx] = 0 := by
              change (0 : Vector Rat m)[idx.val] = 0
              rw [Vector.getElem_zero]
            rw [hentry, show (0 : Rat) + 0 * ((basis b).row col)[idx] = 0 by grind]
            exact ih
      have hzero_div : (0 : Rat) / ((basis b).row col).dotProduct ((basis b).row col) = 0 := by
        grind
      simp [GramSchmidt.projectionCoeff, hnorm, hdot, hzero_div]
  simpa [hzero] using hproj.symm

private theorem projectionCoeff_row_basis_self_eq_one
    (b : Matrix Rat n m) (src : Fin n)
    (hnorm : ((basis b).row src).dotProduct ((basis b).row src) ≠ 0) :
    GramSchmidt.projectionCoeff (b.row src) ((basis b).row src) = 1 := by
  have hsrc_toList : b.toList[src.val]! = b.row src := by simp [Matrix.row]
  have hbasis_src :
      (basis b).row src = (GramSchmidt.basisRows b.toList)[src.val]! := by
    simpa [basis] using
      GramSchmidt.basisMatrix_row_eq_basisRows_get! (b := b) src.val src.isLt
  have hreduce :
      GramSchmidt.reduceAgainstBasis
          ((GramSchmidt.basisRows b.toList).take src.val).reverse (b.row src) =
        (basis b).row src := by
    have hbasis :=
      GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_take
        (rows := b.toList) (k := src.val) (by
          simp [Vector.length_toList])
    have key := hbasis.symm
    rw [hsrc_toList, ← hbasis_src] at key
    exact key
  have hproj :=
    GramSchmidt.projectionCoeff_reduceAgainstBasis_eq
      (basisRev := ((GramSchmidt.basisRows b.toList).take src.val).reverse)
      (row := b.row src) (basisRow := (basis b).row src)
      (by
        intro other hother
        rw [List.mem_reverse] at hother
        rw [List.mem_iff_getElem] at hother
        obtain ⟨idx, hidx, hget⟩ := hother
        have htake_len : ((GramSchmidt.basisRows b.toList).take src.val).length = src.val := by
          rw [List.length_take]
          have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
            simp [GramSchmidt.basisRows_length]
          omega
        have hidx_src : idx < src.val := by
          rw [htake_len] at hidx
          exact hidx
        have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
          simp [GramSchmidt.basisRows_length]
        have hidx_basis : idx < (GramSchmidt.basisRows b.toList).length := by
          rw [hbasis_len]
          exact Nat.lt_trans hidx_src src.isLt
        have hother_get :
            other = (GramSchmidt.basisRows b.toList)[idx]! := by
          rw [← hget, List.getElem_take]
          simp [hidx_basis]
        rw [hother_get, hbasis_src]
        exact GramSchmidt.basisRows_get!_dot_eq_zero
          (b := b) idx src.val (Nat.lt_trans hidx_src src.isLt) src.isLt
          (Nat.ne_of_lt hidx_src))
  rw [hreduce] at hproj
  have hself :
      GramSchmidt.projectionCoeff ((basis b).row src) ((basis b).row src) = 1 := by
    have hdiv :
        ((basis b).row src).dotProduct ((basis b).row src) /
            ((basis b).row src).dotProduct ((basis b).row src) = 1 := by
      grind
    simp [GramSchmidt.projectionCoeff, hnorm, hdiv]
  simpa [hself] using hproj.symm

/-- After swapping the adjacent rows `km1, k` (assuming the swapped pivot is
nonzero), the basis row at index `k` is the explicit two-term combination of the
old basis rows `km1, k`. The companion of `basis_rowSwap_adjacent_prev` tracking
how a swap rewrites the second vector of the pair. -/
theorem basis_rowSwap_adjacent_curr (b : Matrix Rat n m) (km1 k : Fin n)
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
  let prev := (basis b).row km1
  let curr := (basis b).row k
  let mu := GramSchmidt.entry (coeffs b) k km1
  let swappedPrev := curr + mu • prev
  have hraw :=
    GramSchmidt.basisMatrix_rowSwap_adjacent_curr (b := b) (km1 := km1) (k := k) hkm1
  have hlt : km1.val < k.val := by omega
  have hmu :
      GramSchmidt.projectionCoeff (b.row k) ((basis b).row km1) = mu := by
    simp [mu, coeffs, basis, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
      GramSchmidt.projectionCoeff, Matrix.row, hlt]
  have hmu_raw :
      GramSchmidt.projectionCoeff (b.row k) ((GramSchmidt.basisMatrix b).row km1) = mu := by
    simpa [basis] using hmu
  have hraw' :
      (basis (Matrix.rowSwap b km1 k)).row k =
        prev - GramSchmidt.projectionCoeff (b.row km1) swappedPrev • swappedPrev := by
    simpa [basis, prev, curr, mu, swappedPrev, hmu_raw] using hraw
  have horth_curr_prev : curr.dotProduct prev = 0 := by
    simpa [curr, prev] using
      basis_orthogonal (b := b) k.val km1.val k.isLt km1.isLt (by omega)
  have horth_prev_curr : prev.dotProduct curr = 0 := by
    simpa [prev, curr, GramSchmidt.dot_comm_rat] using horth_curr_prev
  have hrow_curr : (b.row km1).dotProduct curr = 0 := by
    have hpc :=
      projectionCoeff_row_later_basis_eq_zero (b := b) (src := km1) (col := k) hlt
    by_cases hcurr : curr.dotProduct curr = 0
    · exact GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := curr) hcurr
    · have hdiv :
        (b.row km1).dotProduct curr / curr.dotProduct curr = 0 := by
          simpa [curr, GramSchmidt.projectionCoeff, hcurr] using hpc
      grind
  have hrow_prev : (b.row km1).dotProduct prev = prev.dotProduct prev := by
    by_cases hprev : prev.dotProduct prev = 0
    · have hzero := GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := prev) hprev
      simp [hzero, hprev]
    · have hpc := projectionCoeff_row_basis_self_eq_one (b := b) (src := km1) (by
        simpa [prev] using hprev)
      have hdiv :
        (b.row km1).dotProduct prev / prev.dotProduct prev = 1 := by
          simpa [prev, GramSchmidt.projectionCoeff, hprev] using hpc
      grind
  have hrow_swapped :
      (b.row km1).dotProduct swappedPrev = mu * prev.dotProduct prev := by
    rw [GramSchmidt.dot_comm_rat]
    change (curr + mu • prev).dotProduct (b.row km1) = mu * prev.dotProduct prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left]
    have hcurr_row : curr.dotProduct (b.row km1) = 0 := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_curr
    have hprev_row : prev.dotProduct (b.row km1) = prev.dotProduct prev := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_prev
    rw [hcurr_row, hprev_row]
    grind
  have hproj :
      GramSchmidt.projectionCoeff (b.row km1) swappedPrev =
        mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev := by
    have hnorm' : swappedPrev.dotProduct swappedPrev ≠ 0 := by
      simpa [prev, curr, mu, swappedPrev] using hnorm
    simp [GramSchmidt.projectionCoeff, hnorm', hrow_swapped]
  have hcurr_swapped : curr.dotProduct swappedPrev = curr.dotProduct curr := by
    rw [GramSchmidt.dot_comm_rat]
    change (curr + mu • prev).dotProduct curr = curr.dotProduct curr
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, horth_prev_curr]
    grind
  have hprev_swapped : prev.dotProduct swappedPrev = mu * prev.dotProduct prev := by
    rw [GramSchmidt.dot_comm_rat]
    change (curr + mu • prev).dotProduct prev = mu * prev.dotProduct prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, horth_curr_prev]
    grind
  have hdenom :
      swappedPrev.dotProduct swappedPrev =
        curr.dotProduct curr + mu * mu * prev.dotProduct prev := by
    change (curr + mu • prev).dotProduct swappedPrev =
      curr.dotProduct curr + mu * mu * prev.dotProduct prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, hcurr_swapped, hprev_swapped]
    grind
  rw [hraw', hproj]
  change
    prev - (mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) • swappedPrev =
      (curr.dotProduct curr / swappedPrev.dotProduct swappedPrev) • prev -
        (mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) • curr
  apply Vector.ext
  intro idx hidx
  simp only [Vector.getElem_sub, Vector.getElem_smul]
  have hswapped_idx : swappedPrev[idx] = curr[idx] + mu * prev[idx] := by
    simp only [swappedPrev, Vector.getElem_add, Vector.getElem_smul]
    change curr[idx] + mu * prev[idx] = curr[idx] + mu * prev[idx]
    rfl
  rw [hswapped_idx]
  change
    prev[idx] -
        (mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) *
          (curr[idx] + mu * prev[idx]) =
      (curr.dotProduct curr / swappedPrev.dotProduct swappedPrev) * prev[idx] -
        (mu * prev.dotProduct prev / swappedPrev.dotProduct swappedPrev) * curr[idx]
  have hdenom_ne : swappedPrev.dotProduct swappedPrev ≠ 0 := by
    simpa [prev, curr, mu, swappedPrev] using hnorm
  rw [hdenom]
  grind

private theorem rowSwap_row_left (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row i = b.row j := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[i][c] = b[j][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := i) (k := c)]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

private theorem rowSwap_row_right (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row j = b.row i := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[j][c] = b[i][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := j) (k := c)]
  simp

private theorem rowSwap_row_eq (b : Matrix Rat n m) (i j r : Fin n)
    (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j).row r = b.row r := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := r) (k := c)]
  simp [hri, hrj]

/-- After an adjacent swap, the coefficient at the lower row `km1` against an
earlier column `j` equals the old coefficient at row `k` against `j`: the
swapped rows carry their lower coefficients with them. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row km1 = b.row k :=
    rowSwap_row_left b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := km1) (j := j) hj,
    coeffs_lower_projection (b := b) (i := k) (j := j) (Nat.lt_trans hj hkm1k), hrow, hbasis]

/-- Dual of `coeffs_rowSwap_adjacent_lower_prev`: after an adjacent swap, the
coefficient at row `k` against an earlier column `j` equals the old coefficient
at row `km1` against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row k = b.row km1 :=
    rowSwap_row_right b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := k) (j := j)
    (by omega)]
  rw [coeffs_lower_projection (b := b) (i := km1) (j := j) hj, hrow, hbasis]

/-- The explicit value of the new pivot coefficient (row `k`, column `km1`)
after an adjacent swap, in terms of the old projection coefficient and basis-row
norms. -/
theorem coeffs_rowSwap_adjacent_pivot (b : Matrix Rat n m) (km1 k : Fin n)
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
  let mu := GramSchmidt.entry (coeffs b) k km1
  let prev := (basis b).row km1
  let curr := (basis b).row k
  let swappedPrev := curr + mu • prev
  have hkm1k : km1.val < k.val := by omega
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := k) (j := km1) hkm1k]
  have hrow : (Matrix.rowSwap b km1 k).row k = b.row km1 :=
    rowSwap_row_right b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row km1 = swappedPrev := by
    simpa [swappedPrev, curr, prev, mu] using
      basis_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
  rw [hrow, hbasis]
  have horth_curr_prev : curr.dotProduct prev = 0 := by
    simpa [curr, prev] using
      basis_orthogonal (b := b) k.val km1.val k.isLt km1.isLt (by omega)
  have hrow_curr : (b.row km1).dotProduct curr = 0 := by
    have hpc :=
      projectionCoeff_row_later_basis_eq_zero (b := b) (src := km1) (col := k) hkm1k
    by_cases hcurr : curr.dotProduct curr = 0
    · exact GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := curr) hcurr
    · have hdiv :
        (b.row km1).dotProduct curr / curr.dotProduct curr = 0 := by
          simpa [curr, GramSchmidt.projectionCoeff, hcurr] using hpc
      grind
  have hrow_prev : (b.row km1).dotProduct prev = prev.dotProduct prev := by
    by_cases hprev : prev.dotProduct prev = 0
    · have hzero := GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := prev) hprev
      simp [hzero, hprev]
    · have hpc := projectionCoeff_row_basis_self_eq_one (b := b) (src := km1) (by
        simpa [prev] using hprev)
      have hdiv :
        (b.row km1).dotProduct prev / prev.dotProduct prev = 1 := by
          simpa [prev, GramSchmidt.projectionCoeff, hprev] using hpc
      grind
  have hrow_swapped :
      (b.row km1).dotProduct swappedPrev = mu * prev.dotProduct prev := by
    rw [GramSchmidt.dot_comm_rat]
    change (curr + mu • prev).dotProduct (b.row km1) = mu * prev.dotProduct prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left]
    have hcurr_row : curr.dotProduct (b.row km1) = 0 := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_curr
    have hprev_row : prev.dotProduct (b.row km1) = prev.dotProduct prev := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_prev
    rw [hcurr_row, hprev_row]
    grind
  have hnorm' : swappedPrev.dotProduct swappedPrev ≠ 0 := by
    simpa [swappedPrev, curr, prev, mu] using hnorm
  simp [hnorm', hrow_swapped, swappedPrev, curr, prev, mu]

/-- Under `rowAdd b src dst c` with `src < dst`, lower coefficients in the
destination row update linearly below the pivot source column. -/
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Rat n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        c * GramSchmidt.entry (coeffs b) src col := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
    hcolsrc, Nat.lt_trans hcolsrc hsrcdst]
  rw [hbasis]
  rw [Matrix.rowAdd_eq_set]
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec, GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left]

/-- Under `rowAdd b src dst c` with `src < dst`, the pivot coefficient in the
destination row increases by `c` when the source basis row has nonzero norm. -/
@[grind =]
theorem coeffs_rowAdd_pivot (b : Matrix Rat n m) (src dst : Fin n)
    (hsrcdst : src.val < dst.val) (c : Rat)
    (hnorm : ((basis b).row src).dotProduct ((basis b).row src) ≠ 0) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst src =
      GramSchmidt.entry (coeffs b) dst src + c := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hself :
      GramSchmidt.projectionCoeff (b.row src) ((basis b).row src) = 1 := by
    exact projectionCoeff_row_basis_self_eq_one (b := b) (src := src) hnorm
  have hself_get :
      GramSchmidt.projectionCoeff b[src.val] (basis b)[src.val] = 1 := by
    simpa [Matrix.row] using hself
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hsrcdst]
  rw [hbasis]
  rw [Matrix.rowAdd_eq_set]
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec]
  rw [GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left,
    hself_get]
  grind

/-- Under `rowAdd b src dst c` with `src < col < dst`, destination-row
coefficients above the pivot source column are preserved. -/
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Rat n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  have hsrcdst : src.val < dst.val := Nat.lt_trans hsrccol hcoldst
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hzero := projectionCoeff_row_later_basis_eq_zero (b := b) (src := src) (col := col)
    hsrccol
  have hzero_get :
      GramSchmidt.projectionCoeff b[src.val] (basis b)[col.val] = 0 := by
    simpa [Matrix.row] using hzero
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hcoldst]
  rw [hbasis]
  rw [Matrix.rowAdd_eq_set]
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec]
  rw [GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left,
    hzero_get]
  grind

/-- A row add only changes the destination row of the coefficient matrix. -/
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  apply Vector.ext
  intro col hcol
  let colFin : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) row colFin =
    GramSchmidt.entry (coeffs b) row colFin
  by_cases hlt : colFin.val < row.val
  · simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hlt]
    rw [hbasis]
    rw [Matrix.rowAdd_eq_set]
    have hval : dst.val ≠ row.val := by
      intro h
      exact hrow (Fin.ext h.symm)
    change
      GramSchmidt.projectionCoeff
          ((Vector.set b dst.val (Vector.ofFn fun k => b[dst][k] + c * b[src][k])
            dst.isLt)[row.val])
          (basis b)[colFin.val] =
        GramSchmidt.projectionCoeff b[row.val] (basis b)[colFin.val]
    rw [Vector.getElem_set_ne dst.isLt row.isLt hval]
  · simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hlt]

/-- Orthogonalization preserves the row space of each prefix: the first `i + 1`
rational basis rows span exactly the vectors spanned by the first `i + 1` input
rows. -/
theorem basis_span (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan b i hi v := by
  have hmembersAll :
      ∀ (i : Nat) (hi : i < n),
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan b i hi ((GramSchmidt.prefixRows (basis b) i hi).row j)) ∧
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan (basis b) i hi ((GramSchmidt.prefixRows b i hi).row j)) := by
    intro i
    induction i with
    | zero =>
        intro hi
        constructor
        · intro j
          have hrow :
              (GramSchmidt.prefixRows (basis b) 0 hi).row j =
                (GramSchmidt.prefixRows b 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0
          rw [hrow]
          exact GramSchmidt.prefixSpan_row b 0 hi j
        · intro j
          have hrow :
              (GramSchmidt.prefixRows b 0 hi).row j =
                (GramSchmidt.prefixRows (basis b) 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0.symm
          rw [hrow]
          exact GramSchmidt.prefixSpan_row (basis b) 0 hi j
    | succ k ih =>
        intro hi
        have hk : k < n := Nat.lt_of_succ_lt hi
        have ihk := ih hk
        constructor
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.1 jp
            have hmono := GramSchmidt.prefixSpan_mono_succ b k hi hprev
            have hrow :
                (GramSchmidt.prefixRows (basis b) (k + 1) hi).row j =
                  (GramSchmidt.prefixRows (basis b) k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan b (k + 1) hi pc := by
              have hraw :=
                GramSchmidt.prefixSpan_strictRowCombination
                  (A := basis b) (B := b) (i := k + 1) (hi := hi)
                  (c := GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
                  (by
                    intro row
                    let jp : Fin (k + 1) := row
                    have hprev := ihk.1 jp
                    have hmono := GramSchmidt.prefixSpan_mono_succ b k hi hprev
                    have hrow :
                        (GramSchmidt.strictPrefixRows (basis b) (k + 1)
                            (Nat.le_of_lt hi)).row row =
                          (GramSchmidt.prefixRows (basis b) k hk).row jp := by
                      apply Vector.ext
                      intro col hcol
                      simp [GramSchmidt.strictPrefixRows, GramSchmidt.prefixRows,
                        Matrix.row, jp]
                    rwa [hrow])
              simpa [pc, basis, coeffs,
                GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbrow : GramSchmidt.prefixSpan b (k + 1) hi (b.row last) := by
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using
                GramSchmidt.prefixSpan_row b (k + 1) hi j
            have hbasis_eq :
                ((GramSchmidt.prefixRows (basis b) (k + 1) hi).row j) =
                  b.row last + (-1 : Rat) • pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simp [Vector.getElem_add, Vector.getElem_smul, pc, last, hjlast,
                GramSchmidt.prefixRows, Matrix.row] at hdec_col ⊢
              change (basis b)[k + 1][col] =
                b[k + 1][col] +
                  (-1 : Rat) * (prefixCombination (coeffs b) (basis b) (k + 1) hi)[col]
              rw [hdec_col]
              grind
            rw [hbasis_eq]
            exact GramSchmidt.prefixSpan_add b (k + 1) hi hbrow
              (GramSchmidt.prefixSpan_smul b (k + 1) hi (-1) hpc)
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.2 jp
            have hmono := GramSchmidt.prefixSpan_mono_succ (basis b) k hi hprev
            have hrow :
                (GramSchmidt.prefixRows b (k + 1) hi).row j =
                  (GramSchmidt.prefixRows b k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan (basis b) (k + 1) hi pc := by
              have hraw :=
                GramSchmidt.prefixSpan_strictPrefix_rowCombination
                  (M := basis b) (i := k + 1) (hi := hi)
                  (c := GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
              simpa [pc, basis, coeffs,
                GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbasisrow :
                GramSchmidt.prefixSpan (basis b) (k + 1) hi ((basis b).row last) := by
              have hself := GramSchmidt.prefixSpan_row (basis b) (k + 1) hi j
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using hself
            have hb_eq :
                ((GramSchmidt.prefixRows b (k + 1) hi).row j) =
                  (basis b).row last + pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simpa [pc, last, hjlast, GramSchmidt.prefixRows, Matrix.row] using hdec_col
            rw [hb_eq]
            exact GramSchmidt.prefixSpan_add (basis b) (k + 1) hi hbasisrow hpc
  intro v
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      GramSchmidt.prefixSpan_rowCombination (A := basis b) (B := b)
        (i := i) (hi := hi) c (hmembersAll i hi).1
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      GramSchmidt.prefixSpan_rowCombination (A := b) (B := basis b)
        (i := i) (hi := hi) c (hmembersAll i hi).2
    rwa [hc] at hspan

private theorem basis_row_sub_basis_row_prefixSpan_pred
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    GramSchmidt.prefixSpan (basis b) p hp
      (b.row ⟨i, hi⟩ - (basis b).row ⟨i, hi⟩) := by
  subst i
  refine ⟨GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
      (p + 1) (Nat.le_of_lt hi), ?_⟩
  change
    Matrix.rowCombination (GramSchmidt.prefixRows (basis b) p hp)
        (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
          (p + 1) (Nat.le_of_lt hi)) =
      b.row ⟨p + 1, hi⟩ - (basis b).row ⟨p + 1, hi⟩
  rw [← GramSchmidt.strictPrefixRows_succ_eq_prefixRows
    (M := basis b) (i := p) (hi := hi)]
  have hpc :
      GramSchmidt.prefixCombination (coeffs b) (basis b) (p + 1) hi =
        Matrix.rowCombination (GramSchmidt.strictPrefixRows (basis b) (p + 1)
            (Nat.le_of_lt hi))
          (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
            (p + 1) (Nat.le_of_lt hi)) := by
    simpa [basis, coeffs] using
      GramSchmidt.prefixCombination_eq_strictPrefixRowCombination
        (b := b) (i := p + 1) (hi := hi)
  rw [← hpc]
  have hdec := basis_decomposition b (p + 1) hi
  apply Vector.ext
  intro col hcol
  have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
  rw [Vector.getElem_sub]
  simp only [Vector.getElem_add] at hdec_col
  grind

private theorem basis_row_orthogonal_prefix_pred
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    ∀ j : Fin (p + 1),
      ((basis b).row ⟨i, hi⟩).dotProduct
        ((GramSchmidt.prefixRows (basis b) p hp).row j) = 0 := by
  subst i
  intro j
  have hjn : j.val < n := Nat.lt_trans j.isLt hi
  have hrow :
      (GramSchmidt.prefixRows (basis b) p hp).row j =
        (basis b).row ⟨j.val, hjn⟩ := by
    apply Vector.ext
    intro col hcol
    simp [GramSchmidt.prefixRows, Matrix.row]
  rw [hrow]
  exact basis_orthogonal b (p + 1) j.val hi hjn (by omega)

private theorem basis_rowSwap_of_after_private (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  let p := i.val - 1
  have hp : p < n := by
    dsimp [p]
    exact Nat.lt_of_le_of_lt (Nat.pred_le i.val) i.isLt
  have hsucc : p + 1 = i.val := by
    dsimp [p]
    omega
  have hkp : k.val ≤ p := by
    dsimp [p]
    omega
  have hsource :
      (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply Vector.ext
    intro col hcol
    let c : Fin m := ⟨col, hcol⟩
    change (Matrix.rowSwap b km1 k)[i][c] = b[i][c]
    rw [Matrix.getElem_rowSwap]
    have hik : i ≠ k := by
      intro h
      exact Nat.ne_of_gt hi (congrArg Fin.val h)
    have hikm1 : i ≠ km1 := by
      intro h
      have hval := congrArg Fin.val h
      omega
    simp [hik, hikm1]
  have horig_span :
      GramSchmidt.prefixSpan (basis b) p hp
        (b.row i - (basis b).row i) :=
    basis_row_sub_basis_row_prefixSpan_pred (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_span :
      GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
        (b.row i - (basis (Matrix.rowSwap b km1 k)).row i) := by
    have hraw :=
      basis_row_sub_basis_row_prefixSpan_pred (b := Matrix.rowSwap b km1 k)
        (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
    simpa [hsource] using hraw
  have hswap_to_orig :
      ∀ v : Vector Rat m,
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp v →
          GramSchmidt.prefixSpan (basis b) p hp v := by
    intro v hv
    have hswap_input := (basis_span (Matrix.rowSwap b km1 k) p hp v).1 hv
    have hinput :=
      (GramSchmidt.prefixSpan_rowSwap_adjacent_at_or_after
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp v).1 hswap_input
    exact (basis_span b p hp v).2 hinput
  have horig_rows_to_swap :
      ∀ j : Fin (p + 1),
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) := by
    intro j
    have horig_basis :
        GramSchmidt.prefixSpan (basis b) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) :=
      GramSchmidt.prefixSpan_row (basis b) p hp j
    have horig_input :=
      (basis_span b p hp ((GramSchmidt.prefixRows (basis b) p hp).row j)).1 horig_basis
    have hswap_input :=
      (GramSchmidt.prefixSpan_rowSwap_adjacent_at_or_after
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 horig_input
    exact
      (basis_span (Matrix.rowSwap b km1 k) p hp
        ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 hswap_input
  have horig_orth :=
    basis_row_orthogonal_prefix_pred (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_orth :=
    basis_row_orthogonal_prefix_pred (b := Matrix.rowSwap b km1 k)
      (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
  have hres :=
    GramSchmidt.residual_eq_of_equiv_prefixSpan
      (A := basis b) (B := basis (Matrix.rowSwap b km1 k)) (i := p) (hi := hp)
      (row := b.row i) (r := (basis b).row i)
      (s := (basis (Matrix.rowSwap b km1 k)).row i)
      horig_span hswap_span hswap_to_orig horig_rows_to_swap horig_orth hswap_orth
  exact hres.symm

/-- Swapping the adjacent rows `km1, k` leaves every basis row after the pair
unchanged: the orthogonalized prefix beyond index `k` is recomputed from the
same set of input rows. -/
@[grind =]
theorem basis_rowSwap_of_after (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i :=
  basis_rowSwap_of_after_private b km1 k i hkm1 hi

/-- Coefficient entries for a row and column both lying before the swapped pair
are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k
      (Nat.lt_trans hji hi)
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji,
    coeffs_lower_projection (b := b) (i := i) (j := j) hji, hrow, hbasis]

/-- Coefficient entries for a row after the swapped pair against a column before
it are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hji : j.val < i.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji,
    coeffs_lower_projection (b := b) (i := i) (j := j) hji, hrow, hbasis]

/-- Coefficient entries for a row and column both lying after the swapped pair
are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_after (b := b) (km1 := km1) (k := k) (i := j) hkm1 hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji,
    coeffs_lower_projection (b := b) (i := i) (j := j) hji, hrow, hbasis]

end GramSchmidt.Rat
end Hex
