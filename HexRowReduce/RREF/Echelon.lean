/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RREF.Loop
import all HexRowReduce.RREF.Loop

public section

/-!
Echelon/RREF span and nullspace APIs for `hex-matrix`.

This module hangs the row-span and nullspace correctness theory off the
`IsEchelonForm` and `IsRREF` contracts. The `IsEchelonForm` section transports
row combinations across the echelon transform and builds the decidable
row-span tests `spanCoeffs`/`spanContains` with their soundness lemmas. The
`IsRREF` section proves these tests complete (`spanContains_iff`), constructs
the nullspace basis (`nullspaceMatrix`, `nullspace`) from the free columns,
and shows it is both sound (`nullspace_sound`) and complete
(`nullspace_complete`). The file closes with the public `rref`-backed wrappers
`spanCoeffs`, `spanContains`, `nullspaceBasisMatrix`, and `nullspace`.
-/

namespace Hex
universe u
namespace Matrix
variable {R : Type u} {n m : Nat}

namespace IsEchelonForm

/-- Row combinations transport forward along the echelon transform. -/
theorem rowCombination_transform_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) (e : Vector R n) :
    rowCombination M (Matrix.transpose D.transform * e) =
      rowCombination D.echelon e := by
  unfold rowCombination
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
theorem rowCombination_transformInv_transpose [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {Tinv : Matrix R n n}
    (hTinv : Tinv * D.transform = 1) (c : Vector R n) :
    rowCombination D.echelon (Matrix.transpose Tinv * c) = rowCombination M c := by
  have hcompose :
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) = c := by
    calc
      Matrix.transpose D.transform * (Matrix.transpose Tinv * c) =
          (Matrix.transpose D.transform * Matrix.transpose Tinv) * c := by
            exact (Matrix.mul_assoc_vec (A := Matrix.transpose D.transform)
              (B := Matrix.transpose Tinv) (v := c)).symm
      _ = Matrix.transpose (Tinv * D.transform) * c := by
            rw [← Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (1 : Matrix R n n) * c := by
            rw [hTinv]
      _ = (1 : Matrix R n n) * c := by
            rw [Matrix.transpose_one]
      _ = c := Matrix.one_mulVec c
  have hforward := E.rowCombination_transform_transpose (e := Matrix.transpose Tinv * c)
  rw [hcompose] at hforward
  exact hforward.symm

/-- Existential converse transport: any `v` in the row span of `M` is also in
the row span of `D.echelon`, with an explicit witness produced from a left
inverse of `D.transform`. -/
theorem exists_rowCombination_echelon_of_M [Lean.Grind.CommRing R]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) {v : Vector R m}
    (h : ∃ c : Vector R n, rowCombination M c = v) :
    ∃ d : Vector R n, rowCombination D.echelon d = v := by
  rcases h with ⟨c, hc⟩
  rcases E.transform_inv with ⟨Tinv, hTinv⟩
  refine ⟨Matrix.transpose Tinv * c, ?_⟩
  rw [E.rowCombination_transformInv_transpose hTinv c, hc]

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
        D.echelon[(IsEchelonForm.pivotRow E pi)][D.pivotCols.get pi]
    else
      0

/-- Coefficients for expressing `v` in the row span, if the echelon rows solve it. -/
@[expose]
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n) :=
  let coeffs := Matrix.transpose D.transform * E.echelonCoeffs v
  if rowCombination M coeffs = v then
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
    E.spanCoeffs v = some c → rowCombination M c = v := by
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
    E.spanContains v = true → ∃ c : Vector R n, rowCombination M c = v := by
  intro h
  unfold spanContains at h
  cases hCoeffs : E.spanCoeffs v with
  | none =>
      simp [hCoeffs] at h
  | some c =>
      exact ⟨c, E.spanCoeffs_sound v c hCoeffs⟩

end IsEchelonForm

namespace IsRREF

/-- RREF data has nonzero pivots because every pivot is normalized to one. -/
theorem hasNonzeroPivots [Lean.Grind.Field R]
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D) :
    E.toIsEchelonForm.HasNonzeroPivots := by
  intro i
  have hpivot :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  intro hzero
  exact (show (0 : R) ≠ 1 from Lean.Grind.Field.zero_ne_one) (hzero.symm.trans hpivot)

variable {M : Matrix R n m} {D : RowEchelonData R n m}

private theorem foldl_add_eq_acc_ring {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

private theorem foldl_sum_congr {R : Type u} [Add R]
    {α : Type v} (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

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
        rw [if_pos rfl]
        rw [foldl_add_eq_acc_ring xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : R) = acc := by grind
        rw [hacc]
        rw [ih hitail (List.nodup_cons.mp hnodup).2 acc]

/-- A row-combination vector with a single coefficient `1` at row `i`
and zero elsewhere selects exactly row `i` of the matrix. This packages
the singleton-row case used by span and RREF arguments. -/
theorem rowCombination_single {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} (M : Matrix R n m) (i : Fin n) :
    rowCombination M (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) =
      row M i := by
  ext j hj
  let jf : Fin m := ⟨j, hj⟩
  change
    (rowCombination M (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0))[jf] =
      (row M i)[jf]
  unfold rowCombination
  change (Matrix.mulVec (Matrix.transpose M)
      (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0))[jf] =
    (row M i)[jf]
  unfold Matrix.mulVec Matrix.row Hex.Vector.dotProduct Matrix.transpose
    Matrix.col
  change (Vector.ofFn fun j : Fin m =>
      (List.finRange n).foldl
        (fun acc l => acc + (Vector.ofFn fun j : Fin m => Vector.ofFn fun i : Fin n => M[i][j])[j][l] *
          (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0).get jf =
    M[i][jf]
  rw [Vector.get_ofFn]
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
    apply foldl_sum_congr
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
private theorem pivot_column_entry [Lean.Grind.Field R] (E : IsRREF M D)
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
private theorem rowCombination_pivotCoeff [Lean.Grind.Field R] (E : IsRREF M D)
    (c : Vector R n) (p : Fin D.rank) :
    (rowCombination D.echelon c)[D.pivotCols.get p] =
      c[E.toIsEchelonForm.pivotRow p] := by
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.row, Hex.Vector.dotProduct,
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
          apply foldl_sum_congr
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
private theorem rowCombination_eq_of_coeffs_eq_on_rank [Lean.Grind.Field R]
    (E : IsRREF M D) {c d : Vector R n}
    (hcoeff : ∀ i : Fin D.rank,
      c[E.toIsEchelonForm.pivotRow i] = d[E.toIsEchelonForm.pivotRow i]) :
    rowCombination D.echelon c = rowCombination D.echelon d := by
  ext j hj
  let jj : Fin m := ⟨j, hj⟩
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.row, Hex.Vector.dotProduct,
    Matrix.transpose, Matrix.col]
  change (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * c[i]) 0 =
    (List.finRange n).foldl
      (fun acc i => acc + D.echelon[i][jj] * d[i]) 0
  apply foldl_sum_congr
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
private theorem rowCombination_echelonCoeffs_of_rowCombination [Lean.Grind.Field R]
    (E : IsRREF M D) {v : Vector R m}
    (h : ∃ c : Vector R n, rowCombination D.echelon c = v) :
    rowCombination D.echelon (E.toIsEchelonForm.echelonCoeffs v) = v := by
  rcases h with ⟨c, hc⟩
  rw [← hc]
  apply rowCombination_eq_of_coeffs_eq_on_rank E
  intro i
  have hi : (E.toIsEchelonForm.pivotRow i).val < D.rank := i.isLt
  have hpi : (⟨(E.toIsEchelonForm.pivotRow i).val, hi⟩ : Fin D.rank) = i := by
    apply Fin.ext
    simp [IsEchelonForm.pivotRow]
  simp [IsEchelonForm.echelonCoeffs, hi, hpi]
  change (rowCombination D.echelon c)[D.pivotCols.get i] /
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] =
    c[E.toIsEchelonForm.pivotRow i]
  have hpivot := rowCombination_pivotCoeff E c i
  rw [hpivot]
  have hpivotOne :
      D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i] = 1 := by
    simpa [IsEchelonForm.pivotRow] using E.pivot_one i
  rw [hpivotOne]
  grind

/-- Any vector in the row span produces coefficients via the RREF-backed
`spanCoeffs` API. -/
theorem spanCoeffs_complete [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRREF M D) (v : Vector R m) :
    (∃ c : Vector R n, rowCombination M c = v) →
      (E.toIsEchelonForm.spanCoeffs v).isSome := by
  intro h
  unfold IsEchelonForm.spanCoeffs
  dsimp only
  have hechelon :
      ∃ d : Vector R n, rowCombination D.echelon d = v :=
    E.toIsEchelonForm.exists_rowCombination_echelon_of_M h
  have hreconstruct :
      rowCombination D.echelon (E.toIsEchelonForm.echelonCoeffs v) = v :=
    rowCombination_echelonCoeffs_of_rowCombination E hechelon
  have htransport :
      rowCombination M
          (Matrix.transpose D.transform * E.toIsEchelonForm.echelonCoeffs v) = v := by
    rw [E.toIsEchelonForm.rowCombination_transform_transpose]
    exact hreconstruct
  simp [htransport]

/-- For RREF data, `spanContains` is exactly row-span membership. -/
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (E : IsRREF M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      ∃ c : Vector R n, rowCombination M c = v := by
  constructor
  · exact E.toIsEchelonForm.spanContains_sound v
  · intro h
    unfold IsEchelonForm.spanContains
    simpa using E.spanCoeffs_complete v h

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
private def pivotIndexAux (D : RowEchelonData R n m) (j : Fin m) (start fuel : Nat) :
    Option (Fin D.rank) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < D.rank then
        let i : Fin D.rank := ⟨start, h⟩
        if D.pivotCols.get i = j then
          some i
        else
          pivotIndexAux D j (start + 1) fuel
      else
        none

/-- Find the pivot-row index for column `j`, if `j` is a pivot column. -/
def pivotIndex? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
  pivotIndexAux D j 0 D.rank

private theorem pivotIndexAux_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    ∀ start fuel,
      start ≤ i.val →
      i.val < start + fuel →
      pivotIndexAux D (D.pivotCols.get i) start fuel = some i := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _ hlt
      omega
  | succ fuel ih =>
      intro hstart hlt
      unfold pivotIndexAux
      have hstartRank : start < D.rank := by omega
      simp [hstartRank]
      let s : Fin D.rank := ⟨start, hstartRank⟩
      by_cases hsi : s = i
      · have hcols : D.pivotCols.get s = D.pivotCols.get i := by rw [hsi]
        rw [if_pos hcols]
        change some s = some i
        exact congrArg some hsi
      · have hcols : D.pivotCols.get s ≠ D.pivotCols.get i := by
          intro hcols
          exact hsi (E.pivotCols_injective hcols)
        rw [if_neg hcols]
        apply ih (start := start + 1)
        · have hslt : start < i.val := by
            have hsne : start ≠ i.val := by
              intro hval
              exact hsi (Fin.ext hval)
            omega
          omega
        · omega

private theorem pivotIndex?_pivot (E : IsEchelonForm M D) (i : Fin D.rank) :
    pivotIndex? D (D.pivotCols.get i) = some i := by
  unfold pivotIndex?
  apply pivotIndexAux_pivot E i
  · omega
  · omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotIndexAux_none_of_not_pivot {j : Fin m}
    (hnot : ∀ i : Fin D.rank, D.pivotCols.get i ≠ j) :
    ∀ start fuel, pivotIndexAux D j start fuel = none := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold pivotIndexAux
      by_cases hstart : start < D.rank
      · simp [hstart, hnot ⟨start, hstart⟩]
        exact ih (start + 1)
      · simp [hstart]

private theorem pivotIndex?_free_none (E : IsEchelonForm M D) (k : Fin (m - D.rank)) :
    pivotIndex? D (E.freeCols.get k) = none := by
  unfold pivotIndex?
  apply pivotIndexAux_none_of_not_pivot
  intro i
  exact E.pivotCols_disjoint_freeCols i k

/-- Nullspace basis vectors assembled as columns indexed by the free variables. -/
@[expose]
def nullspaceMatrix [Lean.Grind.Ring R] (E : IsRREF M D) :
    Matrix R m (m - D.rank) :=
  let freeCols := E.toIsEchelonForm.freeCols
  Matrix.ofFn fun j k =>
    if hFree : j = freeCols.get k then
      1
    else
      match pivotIndex? D j with
      | some i =>
          -D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][freeCols.get k]
      | none => 0

/-- In the `k`th nullspace-matrix column, the row for its own free column is `1`. -/
@[grind =] theorem nullspaceMatrix_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get k][k] = 1 := by
  unfold nullspaceMatrix Matrix.ofFn
  simp

/-- In the `k`th nullspace-matrix column, every other free-column row is `0`. -/
@[grind =] theorem nullspaceMatrix_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] = 0 := by
  unfold nullspaceMatrix Matrix.ofFn
  have hne : E.toIsEchelonForm.freeCols.get l ≠ E.toIsEchelonForm.freeCols.get k := by
    intro h
    exact hkl ((E.toIsEchelonForm.freeCols_injective h).symm)
  simp [hne, pivotIndex?_free_none E.toIsEchelonForm l]

/-- In a pivot-column row, a nullspace-matrix entry is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspaceMatrix_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[D.pivotCols.get i][k] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  unfold nullspaceMatrix Matrix.ofFn
  simp [E.toIsEchelonForm.pivotCols_disjoint_freeCols i k,
    pivotIndex?_pivot E.toIsEchelonForm i]

/-- The individual nullspace basis vectors. -/
@[expose]
def nullspace [Lean.Grind.Ring R] (E : IsRREF M D) :
    Vector (Vector R m) (m - D.rank) :=
  Vector.ofFn fun k => Matrix.col (E.nullspaceMatrix) k

private theorem nullspace_get [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspace.get k = Matrix.col E.nullspaceMatrix k := by
  unfold nullspace
  rw [Vector.get_ofFn]

/-- On its own free column, a nullspace basis vector has entry `1`. -/
@[grind =] theorem nullspace_get_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get k] = 1 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free E k

/-- On every other free column, a nullspace basis vector has entry `0`. -/
@[grind =] theorem nullspace_get_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] = 0 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free_ne E hkl

/-- On a pivot column, a nullspace basis vector is the negative RREF entry in
the matching pivot row and free column. -/
@[grind =] theorem nullspace_get_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[D.pivotCols.get i] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_pivot E i k

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_add_eq_acc_ring_echelon {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_sum_start {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      rw [ih (acc := (0 : R) + f x)]
      grind

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_one_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a : α) (f : α → R) (x : R)
    (haMem : a ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hz : ∀ z ∈ xs, z ≠ a → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hzero : ∀ y ∈ zs, f y = 0 := by
          intro y hy
          have hya : y ≠ a := by
            intro h
            subst y
            exact (List.nodup_cons.mp hnodup).1 hy
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have h0x : (0 : R) + x = x := by grind
        rw [h0x]
        rw [foldl_add_eq_acc_ring_echelon zs f x hzero]
      · have hz0 : f z = 0 := hz z (by simp) hza
        rw [hz0]
        have haTail : a ∈ zs := by
          rcases List.mem_cons.mp haMem with hhead | htail
          · exact False.elim (hza hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hzTail : ∀ y ∈ zs, y ≠ a → f y = 0 := by
          intro y hy hya
          exact hz y (List.mem_cons_of_mem _ hy) hya
        have hzeroAdd : (0 : R) + 0 = 0 := by grind
        rw [hzeroAdd]
        exact ih haTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem foldl_two_nonzero {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} [DecidableEq α] (xs : List α) (a b : α) (f : α → R) (x y : R)
    (hab : a ≠ b) (haMem : a ∈ xs) (hbMem : b ∈ xs) (hnodup : xs.Nodup)
    (ha : f a = x) (hb : f b = y)
    (hz : ∀ z ∈ xs, z ≠ a → z ≠ b → f z = 0) :
    xs.foldl (fun acc z => acc + f z) 0 = x + y := by
  induction xs with
  | nil =>
      cases haMem
  | cons z zs ih =>
      simp only [List.foldl_cons]
      by_cases hza : z = a
      · subst z
        rw [ha]
        have hbTail : b ∈ zs := by
          rcases List.mem_cons.mp hbMem with hhead | htail
          · exact False.elim (hab hhead.symm)
          · exact htail
        have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
        have hbOnly : ∀ t ∈ zs, t ≠ b → f t = 0 := by
          intro t ht htb
          have hta : t ≠ a := by
            intro h
            subst t
            exact (List.nodup_cons.mp hnodup).1 ht
          exact hz t (List.mem_cons_of_mem _ ht) hta htb
        have h0x : (0 : R) + x = x := by grind
        rw [h0x]
        rw [foldl_sum_start zs f x]
        rw [foldl_one_nonzero zs b f y hbTail hnodupTail hb hbOnly]
      · by_cases hzb : z = b
        · subst z
          rw [hb]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have haOnly : ∀ t ∈ zs, t ≠ a → f t = 0 := by
            intro t ht hta
            have htb : t ≠ b := by
              intro h
              subst t
              exact (List.nodup_cons.mp hnodup).1 ht
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have h0y : (0 : R) + y = y := by grind
          rw [h0y]
          rw [foldl_sum_start zs f y]
          rw [foldl_one_nonzero zs a f x haTail hnodupTail ha haOnly]
          grind
        · have hz0 : f z = 0 := hz z (by simp) hza hzb
          rw [hz0]
          have haTail : a ∈ zs := by
            rcases List.mem_cons.mp haMem with hhead | htail
            · exact False.elim (hza hhead.symm)
            · exact htail
          have hbTail : b ∈ zs := by
            rcases List.mem_cons.mp hbMem with hhead | htail
            · exact False.elim (hzb hhead.symm)
            · exact htail
          have hnodupTail : zs.Nodup := (List.nodup_cons.mp hnodup).2
          have hzTail : ∀ t ∈ zs, t ≠ a → t ≠ b → f t = 0 := by
            intro t ht hta htb
            exact hz t (List.mem_cons_of_mem _ ht) hta htb
          have hzeroAdd : (0 : R) + 0 = 0 := by grind
          rw [hzeroAdd]
          exact ih haTail hbTail hnodupTail hzTail

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem nullspace_echelon_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    D.echelon * E.nullspace.get k = 0 := by
  ext r hr
  let row : Fin n := ⟨r, hr⟩
  by_cases hrow : r < D.rank
  · let ri : Fin D.rank := ⟨r, hrow⟩
    let free := E.toIsEchelonForm.freeCols.get k
    let pivot := D.pivotCols.get ri
    let coeff := D.echelon[row][free]
    have hrowEq : row = E.toIsEchelonForm.pivotRow ri := by
      apply Fin.ext
      rfl
    have hpivotFree : pivot ≠ free := by
      exact E.toIsEchelonForm.pivotCols_disjoint_freeCols ri k
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn hr]
    rw [Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hpivotTerm :
        D.echelon[row][pivot] * (E.nullspace.get k)[pivot] = -coeff := by
      have hpone : D.echelon[row][pivot] = 1 := by
        simpa [row, ri, pivot, IsEchelonForm.pivotRow] using E.pivot_one ri
      have hnp := nullspace_get_pivot E ri k
      rw [hpone, hnp]
      have hcoeff :
          D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free] = coeff := by
        simp [free, coeff, row, ri, IsEchelonForm.pivotRow]
      change (1 : R) *
          (-D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm ri)][free]) = -coeff
      rw [hcoeff]
      grind
    have hfreeTerm :
        D.echelon[row][free] * (E.nullspace.get k)[free] = coeff := by
      have hnf := nullspace_get_free E k
      rw [hnf]
      grind
    have hzero :
        ∀ j ∈ List.finRange m, j ≠ pivot → j ≠ free →
          D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _ hjp hjf
      rcases E.toIsEchelonForm.colPartition j with ⟨i, hi⟩ | ⟨l, hl⟩
      · have hij : i ≠ ri := by
          intro hir
          subst i
          exact hjp hi.symm
        have hpivotZero : D.echelon[row][D.pivotCols.get i] = 0 := by
          have hval : i.val ≠ ri.val := by
            intro h
            exact hij (Fin.ext h)
          cases Nat.lt_or_gt_of_ne hval with
          | inl hlt =>
              have hbelow := E.toIsEchelonForm.below_pivot_zero i row (by
                change i.val < r
                simpa [ri] using hlt)
              simpa using hbelow
          | inr hgt =>
              have habove := E.above_pivot_zero i row (by
                change r < i.val
                simpa [ri] using hgt)
              simpa using habove
        rw [← hi, hpivotZero]
        grind
      · have hlk : k ≠ l := by
          intro hkl
          subst l
          exact hjf hl.symm
        have hfreeZero := nullspace_get_free_ne E hlk
        rw [← hl, hfreeZero]
        grind
    have hsum := foldl_two_nonzero (R := R) (xs := List.finRange m) pivot free
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) (-coeff) coeff
      hpivotFree (List.mem_finRange pivot) (List.mem_finRange free)
      (List.nodup_finRange m) hpivotTerm hfreeTerm hzero
    calc
      (List.finRange m).foldl
          (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 =
          -coeff + coeff := by
            simpa only using hsum
      _ = 0 := by grind
  · have hzeroRow := E.toIsEchelonForm.zero_row row (by
      exact Nat.le_of_not_gt hrow)
    change (Matrix.mulVec D.echelon (E.nullspace.get k))[r] = (0 : Vector R n)[r]
    unfold Matrix.mulVec Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn hr]
    rw [Vector.getElem_zero r hr]
    change (List.finRange m).foldl
        (fun acc j => acc + D.echelon[row][j] * (E.nullspace.get k)[j]) 0 = 0
    have hzero :
        ∀ j ∈ List.finRange m, D.echelon[row][j] * (E.nullspace.get k)[j] = 0 := by
      intro j _
      have hentry : D.echelon[row][j] = 0 := by
        have hrowGet := congrArg (fun v => v[j]) hzeroRow
        simpa using hrowGet
      rw [hentry]
      grind
    simpa only using foldl_add_eq_acc_ring_echelon (List.finRange m)
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) 0 hzero

/-- Every basis vector returned by `nullspace` lies in the nullspace of `M`. -/
theorem nullspace_sound {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace.get k = 0 := by
  let b := E.nullspace.get k
  have hbEchelon : D.echelon * b = 0 := by
    exact nullspace_echelon_sound (M := M) (D := D) E k
  have hbTransform : D.transform * (M * b) = 0 := by
    calc
      D.transform * (M * b) = (D.transform * M) * b := by
        exact (Matrix.mul_assoc_vec D.transform M b).symm
      _ = D.echelon * b := by
        rw [E.toIsEchelonForm.transform_mul]
      _ = 0 := hbEchelon
  rcases E.toIsEchelonForm.transform_inv with ⟨Tinv, hTinv⟩
  calc
    M * b = (1 : Matrix R n n) * (M * b) := by
      rw [Matrix.one_mulVec]
    _ = (Tinv * D.transform) * (M * b) := by
      rw [hTinv]
    _ = Tinv * (D.transform * (M * b)) := by
      exact Matrix.mul_assoc_vec Tinv D.transform (M * b)
    _ = Tinv * (0 : Vector R n) := by
      rw [hbTransform]
    _ = 0 := by
      rw [Matrix.mulVec_zero]

private theorem vector_toList_eq_finRange_map_get {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k _ _
    simp

private theorem foldl_sum_mul_left_local {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    c * xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + c * f x) (c * acc) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      have hdist : c * (acc + f x) = c * acc + c * f x := by grind
      rw [hdist]

private theorem foldl_sum_perm_local {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (f : β → R) {xs ys : List β} (hperm : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z =
      ys.foldl (fun acc x => acc + f x) z := by
  induction hperm generalizing z with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldl_cons]
      exact ih (z + _)
  | swap x y xs =>
      simp only [List.foldl_cons]
      congr 1
      grind
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ z).trans (ih₂ z)

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem pivotCols_toList_nodup
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    D.pivotCols.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
  have hj' : j < D.rank := by simpa [Vector.length_toList] using hj
  have h := E.pivotCols_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  intro heq
  have heqGet :
      D.pivotCols.toList[i]'hi = D.pivotCols.toList[j]'hj := heq
  rw [Vector.getElem_toList, Vector.getElem_toList] at heqGet
  have : D.pivotCols.get ⟨i, hi'⟩ = D.pivotCols.get ⟨j, hj'⟩ := heqGet
  rw [this] at h
  omega

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
private theorem finRange_perm_pivot_free
    [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsEchelonForm M D) :
    (List.finRange m).Perm
      (D.pivotCols.toList ++ E.freeColsList) := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hpivot_pair : List.Pairwise (fun a b : Fin m => a < b)
      ((List.finRange m).filter p) :=
    List.Pairwise.filter p (List.pairwise_lt_finRange m)
  have hpivot_nodup : ((List.finRange m).filter p).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hpivot_pair.imp (fun hlt heq => by subst heq; omega)
  have hpivot_perm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
    rw [List.perm_ext_iff_of_nodup (pivotCols_toList_nodup E) hpivot_nodup]
    intro a
    constructor
    · intro ha
      rw [List.mem_filter]
      refine ⟨List.mem_finRange a, ?_⟩
      exact decide_eq_true ha
    · intro ha
      rw [List.mem_filter] at ha
      exact of_decide_eq_true ha.2
  have hfree_eq :
      E.freeColsList = (List.finRange m).filter (fun j => !p j) := by
    unfold IsEchelonForm.freeColsList
    apply List.filter_congr
    intro j _hj
    show decide (j ∉ D.pivotCols.toList) = !decide (j ∈ D.pivotCols.toList)
    by_cases hjp : j ∈ D.pivotCols.toList
    · simp [hjp]
    · simp [hjp]
  have hgoal : (D.pivotCols.toList ++ E.freeColsList).Perm (List.finRange m) := by
    rw [hfree_eq]
    exact (hpivot_perm.append_right _).trans
      (List.filter_append_perm p (List.finRange m))
  exact hgoal.symm

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The pivot-column entry in row `pivotRow i` is `1` exactly when the pivot
indices match. This is the indicator characterization used to extract
`v[D.pivotCols.get i]` from the row sum. -/
private theorem pivot_column_entry_pivotRow {R : Type u} [Lean.Grind.Field R]
    {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m} (E : IsRREF M D)
    (i i' : Fin D.rank) :
    D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] =
      if i' = i then (1 : R) else 0 := by
  have h := pivot_column_entry E i' (E.toIsEchelonForm.pivotRow i)
  by_cases hii : i' = i
  · subst i'
    rw [if_pos rfl]
    rw [h]
    rw [if_pos rfl]
  · rw [if_neg hii]
    rw [h]
    have hrow_ne : E.toIsEchelonForm.pivotRow i' ≠ E.toIsEchelonForm.pivotRow i := by
      intro heq
      apply hii
      apply Fin.ext
      simpa [IsEchelonForm.pivotRow] using congrArg Fin.val heq
    rw [if_neg hrow_ne]

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- The row of `D.echelon * v` at `pivotRow i`, expanded as a foldl, is the
sum of the pivot-column contribution `v[D.pivotCols.get i]` plus the
free-column contributions. When `D.echelon * v = 0`, this gives a relation
between `v[D.pivotCols.get i]` and the free-column entries. -/
private theorem freeSum_eq_neg_pivot {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRREF M D) {v : Vector R m}
    (hEchelon : D.echelon * v = 0) (i : Fin D.rank) :
    v[D.pivotCols.get i] +
      (List.finRange (m - D.rank)).foldl
        (fun acc k =>
          acc +
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k]) 0 = 0 := by
  -- Expand `(D.echelon * v)[pivotRow i] = 0` into a foldl over `Fin m`.
  have hZero : (List.finRange m).foldl
      (fun acc l =>
        acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 = 0 := by
    have hentry := congrArg (fun w => w[(E.toIsEchelonForm.pivotRow i).val]'
      (E.toIsEchelonForm.pivotRow i).isLt) hEchelon
    -- `hentry : (D.echelon * v)[pivotRow i] = (0 : Vector R n)[pivotRow i]`
    change
      (Matrix.mulVec D.echelon v)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt =
      (0 : Vector R n)[(E.toIsEchelonForm.pivotRow i).val]'
        (E.toIsEchelonForm.pivotRow i).isLt at hentry
    unfold Matrix.mulVec Matrix.row Hex.Vector.dotProduct at hentry
    rw [Vector.getElem_ofFn (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    rw [Vector.getElem_zero (E.toIsEchelonForm.pivotRow i).val
      (E.toIsEchelonForm.pivotRow i).isLt] at hentry
    exact hentry
  -- Split the foldl using the perm `finRange m ~ pivotCols.toList ++ freeColsList`.
  have hperm := finRange_perm_pivot_free (M := M) (D := D) E.toIsEchelonForm
  have hSplit :
      (List.finRange m).foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        D.pivotCols.toList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 +
        E.toIsEchelonForm.freeColsList.foldl
            (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 := by
    rw [foldl_sum_perm_local
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) hperm]
    rw [List.foldl_append]
    rw [foldl_sum_start (R := R)
      (xs := E.toIsEchelonForm.freeColsList)
      (f := fun l => D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l])
      (acc := D.pivotCols.toList.foldl
        (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0)]
  -- Pivot half: convert to fold over Fin D.rank, use indicator structure.
  have hPivotPart :
      D.pivotCols.toList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        v[D.pivotCols.get i] := by
    have hList : D.pivotCols.toList =
        (List.finRange D.rank).map fun i' => D.pivotCols.get i' := by
      have h := vector_toList_eq_finRange_map_get D.pivotCols
      simpa [Vector.get] using h
    rw [hList, List.foldl_map]
    have hrewrite :
        (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + D.echelon[E.toIsEchelonForm.pivotRow i][D.pivotCols.get i'] *
                v[D.pivotCols.get i']) 0 =
          (List.finRange D.rank).foldl
            (fun acc i' =>
              acc + (if i = i' then (1 : R) else 0) * v[D.pivotCols.get i']) 0 := by
      apply foldl_sum_congr
      intro i' _hi'
      have h := pivot_column_entry_pivotRow E i i'
      rw [h]
      by_cases hii : i' = i
      · subst i'
        rfl
      · have hii' : i ≠ i' := fun h => hii h.symm
        rw [if_neg hii, if_neg hii']
    rw [hrewrite]
    rw [foldl_indicator_mul_unique (List.finRange D.rank) i
      (fun i' => v[D.pivotCols.get i'])
      (List.mem_finRange i) (List.nodup_finRange D.rank) 0]
    grind
  -- Free half: convert to fold over Fin (m - D.rank).
  have hFreePart :
      E.toIsEchelonForm.freeColsList.foldl
          (fun acc l => acc + D.echelon[E.toIsEchelonForm.pivotRow i][l] * v[l]) 0 =
        (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc +
              D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
                v[E.toIsEchelonForm.freeCols.get k]) 0 := by
    have hList : E.toIsEchelonForm.freeColsList =
        (List.finRange (m - D.rank)).map fun k => E.toIsEchelonForm.freeCols.get k := by
      apply List.ext_getElem
      · simp [E.toIsEchelonForm.freeColsList_length]
      · intro k hk₁ _
        have hk : k < m - D.rank := by
          rw [E.toIsEchelonForm.freeColsList_length] at hk₁
          exact hk₁
        rw [List.getElem_map, List.getElem_finRange]
        change E.toIsEchelonForm.freeColsList[k]'_ = E.toIsEchelonForm.freeCols.get ⟨k, hk⟩
        unfold IsEchelonForm.freeCols
        simp [Vector.get, List.getElem_toArray]
    rw [hList, List.foldl_map]
  rw [hSplit, hPivotPart, hFreePart] at hZero
  exact hZero

omit [Mul R] [Add R] [OfNat R 0] [OfNat R 1] in
/-- Every nullspace vector is generated by the computed nullspace basis. -/
theorem nullspace_complete {R : Type u} [Lean.Grind.Field R] {n m : Nat}
    {M : Matrix R n m} {D : RowEchelonData R n m}
    (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  intro hMv
  have hEchelon : D.echelon * v = 0 := by
    calc
      D.echelon * v = (D.transform * M) * v := by rw [E.toIsEchelonForm.transform_mul]
      _ = D.transform * (M * v) := Matrix.mul_assoc_vec _ _ _
      _ = D.transform * (0 : Vector R n) := by rw [hMv]
      _ = 0 := Matrix.mulVec_zero _
  refine ⟨Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]), ?_⟩
  -- Prove the entry-wise equality for an arbitrary `Fin m` index, then convert
  -- to the `Vector.ext` form. Working with `Fin` lets us use `subst` on the
  -- `colPartition` hypothesis without dependent-type rewriting issues.
  have hcEntry : ∀ k : Fin (m - D.rank),
      (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank))[k] =
        v[E.toIsEchelonForm.freeCols.get k] := by
    intro k
    simp [Vector.getElem_ofFn]
  have key : ∀ jj : Fin m,
      (E.nullspaceMatrix *
          (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
            Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt := by
    intro jj
    -- Expand the matrix-vector product to a foldl.
    change
      (Matrix.mulVec E.nullspaceMatrix
        (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
          Vector R (m - D.rank)))[jj.val]'jj.isLt = v[jj.val]'jj.isLt
    unfold Matrix.mulVec Matrix.row Hex.Vector.dotProduct
    rw [Vector.getElem_ofFn jj.isLt]
    change
      (List.finRange (m - D.rank)).foldl
          (fun acc k =>
            acc + E.nullspaceMatrix[jj][k] *
              (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                Vector R (m - D.rank))[k]) 0 = v[jj]
    rcases E.toIsEchelonForm.colPartition jj with ⟨i, hi⟩ | ⟨l, hl⟩
    · -- Pivot case: substitute jj := D.pivotCols.get i
      subst hi
      -- Replace v[D.pivotCols.get i] using the freeSum identity.
      have hRowEq :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[D.pivotCols.get i][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 := by
        apply foldl_sum_congr
        intro k _hk
        rw [nullspaceMatrix_pivot E i k, hcEntry k]
        grind
      rw [hRowEq]
      have hFree := freeSum_eq_neg_pivot E hEchelon i
      have hNeg :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  -(D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k])) 0 =
            -((List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    D.echelon[E.toIsEchelonForm.pivotRow i][
                      E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k]) 0) := by
        have hmul := foldl_sum_mul_left_local
          (xs := List.finRange (m - D.rank))
          (f := fun k =>
            D.echelon[E.toIsEchelonForm.pivotRow i][E.toIsEchelonForm.freeCols.get k] *
              v[E.toIsEchelonForm.freeCols.get k])
          (c := (-1 : R)) (acc := 0)
        have hzero : ((-1 : R)) * 0 = 0 := by grind
        rw [hzero] at hmul
        have h1 :
            (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    -(D.echelon[E.toIsEchelonForm.pivotRow i][
                        E.toIsEchelonForm.freeCols.get k] *
                      v[E.toIsEchelonForm.freeCols.get k])) 0 =
              (List.finRange (m - D.rank)).foldl
                (fun acc k =>
                  acc +
                    ((-1 : R) *
                      (D.echelon[E.toIsEchelonForm.pivotRow i][
                          E.toIsEchelonForm.freeCols.get k] *
                        v[E.toIsEchelonForm.freeCols.get k]))) 0 := by
          apply foldl_sum_congr
          intro k _hk
          grind
        rw [h1, ← hmul]
        grind
      rw [hNeg]
      have hsum :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc +
                  D.echelon[E.toIsEchelonForm.pivotRow i][
                    E.toIsEchelonForm.freeCols.get k] *
                    v[E.toIsEchelonForm.freeCols.get k]) 0 =
            -v[D.pivotCols.get i] := by
        have h := hFree
        grind
      rw [hsum]
      grind
    · -- Free case: substitute jj := freeCols.get l
      subst hl
      have hcongr :
          (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] *
                  (Vector.ofFn (fun k => v[E.toIsEchelonForm.freeCols.get k]) :
                    Vector R (m - D.rank))[k]) 0 =
            (List.finRange (m - D.rank)).foldl
              (fun acc k =>
                acc + (if l = k then (1 : R) else 0) *
                  v[E.toIsEchelonForm.freeCols.get k]) 0 := by
        apply foldl_sum_congr
        intro k _hk
        rw [hcEntry k]
        by_cases hkl : k = l
        · subst k
          rw [nullspaceMatrix_free E l, if_pos rfl]
        · have hlk : l ≠ k := fun heq => hkl heq.symm
          rw [nullspaceMatrix_free_ne E (k := k) (l := l) hkl, if_neg hlk]
      rw [hcongr]
      rw [foldl_indicator_mul_unique (List.finRange (m - D.rank)) l
        (fun k => v[E.toIsEchelonForm.freeCols.get k])
        (List.mem_finRange l) (List.nodup_finRange (m - D.rank)) 0]
      grind
  ext j hj
  exact key ⟨j, hj⟩

end IsRREF

/-- Convenience wrapper: compute row-span coefficients using `rref` internally. -/
@[expose]
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n) :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanCoeffs v

/-- Wrapper-layer soundness contract for `Matrix.spanCoeffs`. -/
@[grind =>]
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) (c : Vector R n) :
    spanCoeffs M v = some c → rowCombination M c = v := by
  intro h
  exact (rref_isRREF M).toIsEchelonForm.spanCoeffs_sound v c h

/-- Convenience wrapper: decide row-span membership using `rref` internally. -/
@[expose]
def spanContains [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Bool :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanContains v

/-- The public `spanContains` wrapper is the Boolean `isSome` view of
`spanCoeffs`. -/
@[simp, grind =] theorem spanContains_eq_isSome [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = (spanCoeffs M v).isSome := by
  rfl

/-- The public `spanContains` wrapper is exactly row-span membership. -/
@[grind =]
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = true ↔ ∃ c : Vector R n, rowCombination M c = v := by
  unfold spanContains
  simpa using (rref_isRREF M).spanContains_iff v

/-- The rank returned by `rref`. -/
@[expose]
def rref_rank [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) : Nat :=
  (rref M).rank

/-- The public nullspace basis assembled as a matrix of basis columns. -/
@[expose]
def nullspaceBasisMatrix [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Matrix R m (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspaceMatrix

/-- Convenience wrapper: compute the nullspace basis using `rref` internally. -/
@[expose]
def nullspace [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspace

/-- Public column bridge between the matrix and vector nullspace wrappers:
the `k`-th column of `nullspaceBasisMatrix M` is the `k`-th vector in
`nullspace M`. -/
@[grind =>]
theorem nullspaceBasisMatrix_col [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (k : Fin (m - rref_rank M)) :
    Matrix.col (nullspaceBasisMatrix M) k = (nullspace M).get k := by
  unfold nullspaceBasisMatrix nullspace
  exact ((rref_isRREF M).nullspace_get k).symm

/-- Every vector returned by the public `nullspace` wrapper is annihilated by `M`. -/
@[grind =>]
theorem nullspace_sound [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (k : Fin (m - rref_rank M)) :
    M * (nullspace M).get k = 0 := by
  unfold nullspace rref_rank
  exact (rref_isRREF M).nullspace_sound k

/-- Every vector annihilated by `M` is generated by the public nullspace basis matrix. -/
@[grind =>]
theorem nullspace_complete [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - rref_rank M), nullspaceBasisMatrix M * c = v := by
  intro hv
  unfold nullspaceBasisMatrix rref_rank
  exact (rref_isRREF M).nullspace_complete v hv


end Matrix
end Hex
