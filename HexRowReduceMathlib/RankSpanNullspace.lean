/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Vector
public import HexRowReduce
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

/-!
Rank, row-span, and nullspace correspondence theorems for `hex-matrix-mathlib`.

This module converts the executable `Hex.Matrix` row-reduction data into
Mathlib's function-based matrix model, then states theorems relating
computed rank, span membership, and nullspace bases to Mathlib's
noncomputable linear-algebra definitions.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- The executable row combination `Hex.Matrix.vecMul c M` (the linear
combination of the rows of `M` with coefficients `c`) transports under
`vectorEquiv` to Mathlib's `Fintype.linearCombination` over the rows of
`matrixEquiv M`. This identifies the computed row span with Mathlib's span. -/
theorem vectorEquiv_vecMul [CommRing R] (M : Hex.Matrix R n m) (c : Vector R n) :
    vectorEquiv (Hex.Matrix.vecMul c M) =
      Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  funext j
  simp only [vectorEquiv_apply]
  unfold Hex.Matrix.vecMul
  change (Hex.Matrix.mulVec (Hex.Matrix.transpose M) c)[j.val] =
    (Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c)) j
  unfold Hex.Matrix.mulVec Hex.Matrix.row Vector.dotProduct Hex.Matrix.transpose
    Hex.Matrix.col
  rw [Vector.getElem_ofFn j.isLt, foldl_finRange_eq_sum, Fintype.linearCombination_apply,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [vectorEquiv_apply, matrixEquiv_apply, _root_.Matrix.row_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_comm]
  congr 1
  simp [Vector.getElem_ofFn]

/-- Bridge invariant: applying the executable nullspace matrix to a coefficient
vector `c` expands, under `vectorEquiv`, as the `c`-weighted sum of the computed
nullspace basis vectors. Used to express an arbitrary kernel element as a span
of the basis. -/
private theorem vectorEquiv_nullspaceMatrix_mulVec [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (c : Vector R (m - D.rank)) :
    vectorEquiv (E.nullspaceMatrix * c) =
      ∑ k : Fin (m - D.rank), c[k] • vectorEquiv (E.nullspace.get k) := by
  funext j
  simp only [vectorEquiv_apply, Pi.smul_apply, Finset.sum_apply]
  change (Hex.Matrix.mulVec E.nullspaceMatrix c)[j.val] =
    ∑ k : Fin (m - D.rank), c[k] * (E.nullspace.get k)[j]
  unfold Hex.Matrix.mulVec Hex.Matrix.row Vector.dotProduct
  rw [Vector.getElem_ofFn j.isLt, foldl_finRange_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold Hex.Matrix.IsRowReduced.nullspace Hex.Matrix.col
  simp [mul_comm, Vector.get, Vector.toArray_ofFn]

/-- Soundness of the executable `spanCoeffs`: when echelon-form data certifies
`v` as a row combination with coefficients `c`, the Mathlib image of `v` is the
corresponding `linearCombination` of the rows of `M`. Witnesses span membership
with explicit coefficients. -/
theorem spanCoeffs_eq_linearCombination [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c →
      vectorEquiv v =
        Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  intro h
  unfold Hex.Matrix.IsEchelonForm.spanCoeffs at h
  dsimp only at h
  split at h
  · rename_i hrow
    injection h with hc
    subst c
    exact (congrArg vectorEquiv hrow.symm).trans (vectorEquiv_vecMul M _)
  · contradiction

/-- The executable span-membership test `spanContains` is correct: it returns
`true` exactly when the Mathlib image of `v` lies in the `R`-span of the rows of
`M`. The decision procedure agrees with Mathlib's `Submodule.span`. -/
theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      vectorEquiv v ∈ Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M))) := by
  rw [← Fintype.range_linearCombination]
  constructor
  · intro h
    rcases (E.spanContains_iff v).mp h with ⟨c, hc⟩
    exact ⟨vectorEquiv c, by
      rw [← vectorEquiv_vecMul M c, hc]⟩
  · rintro ⟨c, hc⟩
    apply (E.spanContains_iff v).mpr
    refine ⟨vectorEquiv.symm c, ?_⟩
    apply Equiv.injective vectorEquiv
    rw [vectorEquiv_vecMul M (vectorEquiv.symm c)]
    simpa using hc

/-- Every row of the computed echelon form lies in the row span of the original
matrix `M`: row reduction does not enlarge the span. One inclusion of the
"echelon rows span the same subspace as `M`" equivalence. -/
theorem rowReduce_echelon_row_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (i : Fin n) :
    vectorEquiv (Hex.Matrix.row D.echelon i) ∈
      Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M))) := by
  rw [← Fintype.range_linearCombination]
  let e : Vector R n := Vector.ofFn fun p : Fin n => if i = p then (1 : R) else 0
  refine ⟨vectorEquiv (Hex.Matrix.transpose D.transform * e), ?_⟩
  rw [← vectorEquiv_vecMul M (Hex.Matrix.transpose D.transform * e)]
  have htransport := E.toIsEchelonForm.vecMul_transform_transpose (e := e)
  have hsingle : Hex.Matrix.vecMul e D.echelon = Hex.Matrix.row D.echelon i := by
    simpa [e] using Hex.Matrix.IsRowReduced.vecMul_single (M := D.echelon) i
  rw [htransport, hsingle]

/-- Converse direction: any vector in the row span of `M` is realised as an
executable row combination of the echelon rows. Together with
`rowReduce_echelon_row_mem_span` this shows row reduction preserves the row span. -/
theorem rowReduce_mem_span_echelon_of_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) {v : Fin m → R} :
    v ∈ Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M))) →
      ∃ c : Vector R n, Hex.Matrix.vecMul c D.echelon = vectorEquiv.symm v := by
  intro hv
  have hcontains :
      E.toIsEchelonForm.spanContains (vectorEquiv.symm v) = true := by
    rw [spanContains_iff_mem_span E]
    simpa using hv
  exact E.toIsEchelonForm.exists_vecMul_echelon_of_M
    ((E.spanContains_iff (vectorEquiv.symm v)).mp hcontains)

/-- Each computed nullspace basis vector lies in the kernel of `M` (viewed as
Mathlib's linear map `mulVecLin`): the executable nullspace really annihilates
`M`. -/
theorem nullspace_mem_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (k : Fin (m - D.rank)) :
    vectorEquiv (E.nullspace.get k) ∈
      LinearMap.ker ((_root_.Matrix.mulVecLin (matrixEquiv M))) := by
  rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply]
  have hsound := Hex.Matrix.IsRowReduced.nullspace_sound E k
  have hbridge := vectorEquiv_mulVec (M := M) (v := E.nullspace.get k)
  rw [hsound] at hbridge
  have hzero : vectorEquiv (0 : Vector R n) = 0 := by
    ext i
    simp
  rw [hzero] at hbridge
  exact hbridge.symm

/-- The computed nullspace basis spans exactly the kernel of `M`: the span of
the executable basis vectors equals Mathlib's `LinearMap.ker (mulVecLin M)`.
This is the completeness counterpart to `nullspace_mem_ker`. -/
theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    Submodule.span R (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact nullspace_mem_ker E k
  · intro x hx
    rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply] at hx
    let v : Vector R m := vectorEquiv.symm x
    have hMv : M * v = 0 := by
      have hbridge := vectorEquiv_mulVec (M := M) (v := v)
      have hxv : vectorEquiv v = x := by
        simp [v]
      rw [hxv] at hbridge
      have hzero : (matrixEquiv M).mulVec x = 0 := hx
      rw [hzero] at hbridge
      have hzeroVec : vectorEquiv (M * v) = vectorEquiv (0 : Vector R n) := by
        apply funext
        intro i
        have hi := congrFun hbridge i
        simpa [vectorEquiv] using hi
      exact Equiv.injective vectorEquiv hzeroVec
    rcases Hex.Matrix.IsRowReduced.nullspace_complete E v hMv with ⟨c, hc⟩
    have hxsum :
        x = ∑ k : Fin (m - D.rank), c[k] • vectorEquiv (E.nullspace.get k) := by
      have hlin := vectorEquiv_nullspaceMatrix_mulVec E c
      rw [hc] at hlin
      have hxv : vectorEquiv v = x := by
        simp [v]
      rw [hxv] at hlin
      exact hlin
    rw [hxsum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ c[k] (Submodule.subset_span ⟨k, rfl⟩)

/-- Invariant pinning the free-column entries of the nullspace basis: basis
vector `k` reads `1` at its own free column and `0` at the others. This Kronecker
pattern is what makes the basis linearly independent. -/
private theorem nullspace_get_free_entry [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (k l : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] =
      if k = l then (1 : R) else 0 := by
  by_cases hkl : k = l
  · subst k
    simpa using Hex.Matrix.IsRowReduced.nullspace_get_free E l
  · simpa [hkl] using Hex.Matrix.IsRowReduced.nullspace_get_free_ne E hkl

/-- The computed nullspace basis is linearly independent, read off from the
Kronecker pattern of `nullspace_get_free_entry`. Supplies the dimension count in
`rank_eq`. -/
private theorem nullspace_linearIndependent [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    LinearIndependent R (fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum l
  have hcoord := congrFun hsum (E.toIsEchelonForm.freeCols.get l)
  rw [Finset.sum_apply] at hcoord
  have hcoord' :
      (∑ k : Fin (m - D.rank),
          g k * (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l]) = 0 := by
    simpa [Pi.smul_apply, vectorEquiv_apply] using hcoord
  have hsingle :
      (∑ k : Fin (m - D.rank),
          g k * (if k = l then (1 : R) else 0)) = 0 := by
    simpa [nullspace_get_free_entry E] using hcoord'
  rw [Finset.sum_eq_single l] at hsingle
  · simpa using hsingle
  · intro k _ hkl
    simp [hkl]
  · intro hmem
    exact (hmem (Finset.mem_univ l)).elim

/-- The rank computed by row reduction agrees with Mathlib's `Matrix.rank`.
Proven by rank-nullity: the `m - D.rank` independent nullspace basis vectors pin
the kernel dimension, and the complement is the matrix rank. -/
theorem rank_eq [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M) := by
  classical
  have hker :
      Module.finrank R (LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M))) = m - D.rank := by
    rw [← nullspace_span_eq_ker E]
    simpa using finrank_span_eq_card (nullspace_linearIndependent E)
  have hrank_nullity :
      _root_.Matrix.rank (matrixEquiv M) +
          Module.finrank R (LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M))) = m := by
    rw [_root_.Matrix.rank]
    simpa using
      (LinearMap.finrank_range_add_finrank_ker
        (_root_.Matrix.mulVecLin (matrixEquiv M)))
  have hrank_add : _root_.Matrix.rank (matrixEquiv M) + (m - D.rank) = m := by
    simpa [hker] using hrank_nullity
  have hDadd : D.rank + (m - D.rank) = m := Nat.add_sub_of_le E.toIsEchelonForm.rank_le_m
  exact Nat.add_right_cancel (hDadd.trans hrank_add.symm)

end HexMatrixMathlib
