/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Loop
import all HexRowReduce.Loop

public section

/-!
Row-span API over the echelon contracts.

The `IsEchelonForm` section transports row combinations across the echelon
transform and builds the decidable row-span tests `spanCoeffs`/`spanContains`
with their soundness lemmas. The `IsRowReduced` section adds the helper theory
(pivot-column structure, single-row combinations) and proves the tests complete
(`spanCoeffs_complete`, `spanContains_iff`).
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

namespace IsEchelonForm

/-- Row combinations transport forward along the echelon transform. -/
theorem vecMul_transform_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) (e : Vector R n) :
    vecMul (Matrix.transpose D.transform * e) M =
      vecMul e D.echelon := by
  unfold vecMul
  calc
    Matrix.transpose M * (Matrix.transpose D.transform * e) =
        (Matrix.transpose M * Matrix.transpose D.transform) * e := by
          exact (Matrix.mul_assoc_vec (A := Matrix.transpose M)
            (B := Matrix.transpose D.transform) (v := e)).symm
    _ = Matrix.transpose (D.transform * M) * e := by
          rw [← Matrix.transpose_mul_of_mul_comm]
    _ = Matrix.transpose D.echelon * e := by
          rw [E.transform_mul]

/-- Converse row-combination transport: an `M`-row-combination witness `c`
yields a `D.echelon`-row-combination witness `Matrix.transpose Tinv * c`,
where `Tinv` is any left inverse of `D.transform`. The proof reuses the
forward transport at the candidate witness. -/
theorem vecMul_transformInv_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {Tinv : Matrix R n n}
    (hTinv : Tinv * D.transform = (Matrix.identity (R := R) n)) (c : Vector R n) :
    vecMul (Matrix.transpose Tinv * c) D.echelon = vecMul c M := by
  have hcompose :
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) = c := by
    calc
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) =
          (Matrix.transpose D.transform * Matrix.transpose Tinv) * c := by
            exact (Matrix.mul_assoc_vec (A := Matrix.transpose D.transform)
              (B := Matrix.transpose Tinv) (v := c)).symm
      _ = Matrix.transpose (Tinv * D.transform) * c := by
            rw [← Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (Matrix.identity (R := R) n) * c := by
            rw [hTinv]
      _ = (Matrix.identity (R := R) n) * c := by
            rw [Matrix.transpose_identity]
      _ = c := Matrix.identity_mulVec c
  have hforward := E.vecMul_transform_transpose (e := Matrix.transpose Tinv * c)
  rw [hcompose] at hforward
  exact hforward.symm

/-- Existential converse transport: any `v` in the row span of `M` is also in
the row span of `D.echelon`, with an explicit witness produced from a left
inverse of `D.transform`. -/
theorem exists_vecMul_echelon_of_M [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {v : Vector R m}
    (h : ∃ c : Vector R n, vecMul c M = v) :
    ∃ d : Vector R n, vecMul d D.echelon = v := by
  rcases h with ⟨c, hc⟩
  rcases E.transform_inv with ⟨Tinv, hTinv⟩
  refine ⟨Matrix.transpose Tinv * c, ?_⟩
  rw [E.vecMul_transformInv_transpose hTinv c, hc]

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- The echelon-side coefficients selected by pivot coordinates. -/
@[expose]
def echelonCoeffs [Lean.Grind.Field R] (E : IsEchelonForm M D)
    (v : Vector R m) : Vector R n :=
  Vector.ofFn fun i =>
    if h : i.val < D.rank then
      let pi : Fin D.rank := ⟨i.val, h⟩
      v[D.pivotCols.get pi] /
        D.echelon[(IsEchelonForm.pivotRow E pi, D.pivotCols.get pi)]
    else
      0

/-- Coefficients for expressing `v` in the row span, if the echelon rows solve it. -/
@[expose]
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n) :=
  let coeffs := Matrix.transpose D.transform * E.echelonCoeffs v
  if vecMul coeffs M = v then
    some coeffs
  else
    none

/-- Decidable row-span membership test derived from `spanCoeffs`. -/
@[expose]
def spanContains [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Bool :=
  (E.spanCoeffs v).isSome

/-- `spanContains` is the Boolean `isSome` view of `spanCoeffs`. -/
@[simp, grind =] theorem spanContains_eq_isSome [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = (E.spanCoeffs v).isSome := rfl

/-- `spanCoeffs` returns coefficients whose row combination equals `v`. -/
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c → vecMul c M = v := by
  intro h
  unfold spanCoeffs at h
  dsimp only at h
  split at h
  · rename_i hspan
    injection h with hc
    subst c
    exact hspan
  · contradiction

/-- If `spanContains` succeeds, the vector is in the row span. -/
theorem spanContains_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = true → ∃ c : Vector R n, vecMul c M = v := by
  intro h
  unfold spanContains at h
  cases hCoeffs : E.spanCoeffs v with
  | none =>
      simp [hCoeffs] at h
  | some c =>
      exact ⟨c, E.spanCoeffs_sound v c hCoeffs⟩

end IsEchelonForm

namespace IsRowReduced

/-- RREF data has nonzero pivots because every pivot is normalized to one. -/
theorem hasNonzeroPivots [Lean.Grind.Field R]
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRowReduced M D) :
    E.toIsEchelonForm.HasNonzeroPivots := by
  intro i
  have hpivot :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  intro hzero
  exact (show (0 : R) ≠ 1 from Lean.Grind.Field.zero_ne_one) (hzero.symm.trans hpivot)

variable {M : Matrix R n m} {D : RowEchelonData R n m}

private theorem foldl_indicator_mul_unique {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl, List.foldl_add_eq_self xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : R) = acc := by grind
        rw [hacc, ih hitail (List.nodup_cons.mp hnodup).2 acc]

/-- A row-combination vector with a single coefficient `1` at row `i`
and zero elsewhere selects exactly row `i` of the matrix. This packages
the singleton-row case used by span and RREF arguments. -/
theorem vecMul_single {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} (M : Matrix R n m) (i : Fin n) :
    vecMul (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) M =
      row M i := by
  ext j hj
  let jf : Fin m := ⟨j, hj⟩
  change
    (vecMul (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) M)[jf] =
      (row M i)[jf]
  unfold vecMul
  change (Matrix.mulVec (Matrix.transpose M)
      (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0))[jf] =
    (row M i)[jf]
  unfold Matrix.mulVec Matrix.row Vector.dotProduct Matrix.transpose
    Matrix.col
  change (Vector.ofFn fun j : Fin m =>
      (List.finRange n).foldl
        (fun acc l => acc + (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[j][l] *
          (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0)[jf.1] =
    M[i][jf]
  rw [Vector.getElem_ofFn]
  change
    (List.finRange n).foldl
        (fun acc l => acc +
          (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[jf][l] *
          (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0 =
      M[i][jf]
  have hbody :
      (List.finRange n).foldl
          (fun acc l => acc +
            (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[jf][l] *
            (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if i = l then (1 : R) else 0) * M[l][jf]) 0 := by
    apply List.foldl_add_congr
    intro l _hl
    by_cases hil : i = l
    · simp [hil, Lean.Grind.CommSemiring.mul_comm]
    · rw [if_neg hil]
      grind
  rw [hbody]
  have hpick := foldl_indicator_mul_unique (R := R) (List.finRange n) i
    (fun l : Fin n => M[l][jf]) (List.mem_finRange i) (List.nodup_finRange n) 0
  have hzero : (0 : R) + M[i][jf] = M[i][jf] := by grind
  exact hpick.trans hzero

/-- In an RREF, a pivot column is a standard basis vector: its entry in row `i`
is `1` when `i` is the pivot row of `p` and `0` otherwise. -/
private theorem pivot_column_entry [Lean.Grind.Field R] (E : IsRowReduced M D)
    (p : Fin D.rank) (i : Fin n) :
    D.echelon[i][D.pivotCols.get p] =
      if E.toIsEchelonForm.pivotRow p = i then 1 else 0 := by
  by_cases hi : i.val < D.rank
  · let q : Fin D.rank := ⟨i.val, hi⟩
    by_cases hpq : p = q
    · subst q
      have hip : E.toIsEchelonForm.pivotRow p = i := by
        apply Fin.ext
        simpa [IsEchelonForm.pivotRow] using congrArg Fin.val hpq
      rw [if_pos hip]
      subst p
      simpa [IsEchelonForm.pivotRow] using E.pivot_one ⟨i.val, hi⟩
    · have hrow_ne : E.toIsEchelonForm.pivotRow p ≠ i := by
        intro hrow
        apply hpq
        apply Fin.ext
        simpa [IsEchelonForm.pivotRow] using congrArg Fin.val hrow
      rw [if_neg hrow_ne]
      have hne : i.val ≠ p.val := by
        intro hval
        apply hpq
        apply Fin.ext
        exact hval.symm
      cases Nat.lt_or_gt_of_ne hne with
      | inl hip =>
          exact E.above_pivot_zero p i hip
      | inr hpi =>
          exact E.toIsEchelonForm.below_pivot_zero p i hpi
  · have hrow_ne : E.toIsEchelonForm.pivotRow p ≠ i := by
      intro hrow
      apply hi
      rw [← Fin.ext_iff.mp hrow]
      exact p.isLt
    rw [if_neg hrow_ne]
    have hzero := E.toIsEchelonForm.zero_row i (by omega)
    simpa using congrArg (fun row => row[D.pivotCols.get p]) hzero

/-- Reading a row combination of the echelon rows off at pivot column `p` recovers
exactly the coefficient applied to the pivot row of `p`, since that column is a
standard basis vector. -/
private theorem vecMul_pivotCoeff [Lean.Grind.Field R] (E : IsRowReduced M D)
    (c : Vector R n) (p : Fin D.rank) :
    (vecMul c D.echelon)[D.pivotCols.get p] =
      c[E.toIsEchelonForm.pivotRow p] := by
  unfold vecMul
  simp [HMul.hMul, Matrix.mulVec, Matrix.row, Vector.dotProduct,
    Matrix.transpose, Matrix.col]
  change (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][D.pivotCols.get p] * c[i]) 0 =
    c[E.toIsEchelonForm.pivotRow p]
  calc
    (List.finRange n).foldl
        (fun acc i => acc + D.echelon[i][D.pivotCols.get p] * c[i]) 0 =
        (List.finRange n).foldl
          (fun acc i =>
            acc + (if E.toIsEchelonForm.pivotRow p = i then (1 : R) else 0) * c[i]) 0 := by
          apply List.foldl_add_congr
          intro i _hi
          rw [pivot_column_entry E p i]
    _ = c[E.toIsEchelonForm.pivotRow p] := by
          have h :=
            foldl_indicator_mul_unique (List.finRange n) (E.toIsEchelonForm.pivotRow p)
              (fun i => c[i]) (List.mem_finRange _) (List.nodup_finRange n) 0
          have hzero : (0 : R) + c[E.toIsEchelonForm.pivotRow p] =
              c[E.toIsEchelonForm.pivotRow p] := by
            grind
          exact h.trans hzero

/-- Two coefficient vectors that agree on every pivot row yield the same row
combination of the echelon rows, because the non-pivot rows are zero rows and
contribute nothing. -/
private theorem vecMul_eq_of_coeffs_eq_on_rank [Lean.Grind.Field R]
    (E : IsRowReduced M D) {c d : Vector R n}
    (hcoeff : ∀ i : Fin D.rank,
      c[E.toIsEchelonForm.pivotRow i] = d[E.toIsEchelonForm.pivotRow i]) :
    vecMul c D.echelon = vecMul d D.echelon := by
  ext j hj
  let jj : Fin m := ⟨j, hj⟩
  unfold vecMul
  simp [HMul.hMul, Matrix.mulVec, Matrix.row, Vector.dotProduct,
    Matrix.transpose, Matrix.col]
  change (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * c[i]) 0 =
    (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * d[i]) 0
  apply List.foldl_add_congr
  intro i _hi
  by_cases hirank : i.val < D.rank
  · let r : Fin D.rank := ⟨i.val, hirank⟩
    have hirow : E.toIsEchelonForm.pivotRow r = i := by
      apply Fin.ext
      rfl
    have hci : c[i] = d[i] := by
      simpa [hirow] using hcoeff r
    rw [hci]
  · have hrow := E.toIsEchelonForm.zero_row i (by omega)
    have hentry : D.echelon[i][jj] = 0 := by
      simpa using congrArg (fun row => row[jj]) hrow
    rw [hentry]
    have hleft : (0 : R) * c[i] = 0 := by grind
    have hright : (0 : R) * d[i] = 0 := by grind
    rw [hleft, hright]

/-- For any vector in the row span of the echelon matrix, the coefficients recovered
by `echelonCoeffs` reproduce it, so `echelonCoeffs` is a right inverse to row
combination on the span. -/
private theorem vecMul_echelonCoeffs_of_vecMul [Lean.Grind.Field R]
    (E : IsRowReduced M D) {v : Vector R m}
    (h : ∃ c : Vector R n, vecMul c D.echelon = v) :
    vecMul (E.toIsEchelonForm.echelonCoeffs v) D.echelon = v := by
  rcases h with ⟨c, hc⟩
  rw [← hc]
  apply vecMul_eq_of_coeffs_eq_on_rank E
  intro i
  have hi : (E.toIsEchelonForm.pivotRow i).val < D.rank := i.isLt
  have hpi : (⟨(E.toIsEchelonForm.pivotRow i).val, hi⟩ : Fin D.rank) = i := by
    apply Fin.ext
    simp [IsEchelonForm.pivotRow]
  simp [IsEchelonForm.echelonCoeffs, hi, hpi]
  change (vecMul c D.echelon)[D.pivotCols.get i] /
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] =
    c[E.toIsEchelonForm.pivotRow i]
  have hpivot := vecMul_pivotCoeff E c i
  rw [hpivot]
  have hpivotOne :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  rw [hpivotOne]
  grind

/-- Any vector in the row span produces coefficients via the RREF-backed
`spanCoeffs` API. -/
theorem spanCoeffs_complete [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRowReduced M D) (v : Vector R m) :
    (∃ c : Vector R n, vecMul c M = v) →
      (E.toIsEchelonForm.spanCoeffs v).isSome := by
  intro h
  unfold IsEchelonForm.spanCoeffs
  dsimp only
  have hechelon :
      ∃ d : Vector R n, vecMul d D.echelon = v :=
    E.toIsEchelonForm.exists_vecMul_echelon_of_M h
  have hreconstruct :
      vecMul (E.toIsEchelonForm.echelonCoeffs v) D.echelon = v :=
    vecMul_echelonCoeffs_of_vecMul E hechelon
  have htransport :
      vecMul (Matrix.transpose D.transform * E.toIsEchelonForm.echelonCoeffs v) M = v := by
    rw [E.toIsEchelonForm.vecMul_transform_transpose]
    exact hreconstruct
  simp [htransport]

/-- For RREF data, `spanContains` is exactly row-span membership. -/
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRowReduced M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      ∃ c : Vector R n, vecMul c M = v := by
  constructor
  · exact E.toIsEchelonForm.spanContains_sound v
  · intro h
    unfold IsEchelonForm.spanContains
    simpa using E.spanCoeffs_complete v h

end IsRowReduced

end Matrix
end Hex
