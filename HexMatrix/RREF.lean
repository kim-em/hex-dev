import Std
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Executable RREF, row-span, and nullspace routines for `hex-matrix`.

This module implements a simple Gaussian-elimination-based `rref` routine over
decidable fields, then exposes the row-span and nullspace APIs layered on top of
the resulting echelon data. It also states the theorem surface connecting the
computed data to the `IsRREF` contract and the derived span/nullspace
characterizations.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

/-- A linear combination of the rows of `M`, using coefficients `c`. -/
def rowCombination [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (c : Vector R n) :
    Vector R m :=
  Matrix.transpose M * c

private structure RrefState (R : Type u) (n m : Nat) where
  row : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivots : List (Fin m)

section FieldAlgorithms

variable [Lean.Grind.Field R] [DecidableEq R]

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivotAux (M : Matrix R n m) (col : Fin m) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search for a nonzero pivot in `col`, starting at row `start`. -/
private def findPivot? (M : Matrix R n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Eliminate every non-pivot entry in a pivot column. -/
private def eliminateColumn (M : Matrix R n m) (T : Matrix R n n)
    (pivotRow : Fin n) (col : Fin m) : Matrix R n m × Matrix R n n :=
  (List.finRange n).foldl
    (fun (state : Matrix R n m × Matrix R n n) j =>
      if h : j = pivotRow then
        state
      else
        let coeff := -state.1[j][col]
        if coeff = 0 then
          state
        else
          (rowAdd state.1 pivotRow j coeff, rowAdd state.2 pivotRow j coeff))
    (M, T)

/-- Process columns left-to-right, performing Gauss-Jordan elimination. -/
private def rrefLoop (col fuel : Nat) (state : RrefState R n m) : RrefState R n m :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hRow : state.row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match findPivot? state.echelon colFin state.row with
          | none =>
              rrefLoop (col + 1) fuel state
          | some pivot =>
              let target : Fin n := ⟨state.row, hRow⟩
              let swappedEchelon := rowSwap state.echelon target pivot
              let swappedTransform := rowSwap state.transform target pivot
              let pivotVal := swappedEchelon[target][colFin]
              let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
              let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
              let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
              let nextState : RrefState R n m :=
                { row := state.row + 1
                  echelon := eliminated.1
                  transform := eliminated.2
                  pivots := state.pivots.concat colFin }
              rrefLoop (col + 1) fuel nextState
        else
          state
      else
        state

/-- Reduced row echelon form data computed by Gauss-Jordan elimination. -/
def rref (M : Matrix R n m) : RowEchelonData R n m :=
  let final := rrefLoop 0 m
    { row := 0
      echelon := M
      transform := 1
      pivots := [] }
  { rank := final.pivots.length
    echelon := final.echelon
    transform := final.transform
    pivotCols := ⟨final.pivots.toArray, by simp⟩ }

/-- The computed `rref` data satisfies the `IsRREF` contract. -/
theorem rref_isRREF (M : Matrix R n m) : IsRREF M (rref M) := by
  sorry

end FieldAlgorithms

namespace IsEchelonForm

private theorem rowCombination_transform_transpose [Lean.Grind.CommRing R]
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
          rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
    _ = Matrix.transpose D.echelon * e := by
          rw [E.transform_mul]

/-- Converse row-combination transport: an `M`-row-combination witness `c`
yields a `D.echelon`-row-combination witness `Matrix.transpose Tinv * c`,
where `Tinv` is any left inverse of `D.transform`. The proof reuses the
forward transport at the candidate witness. -/
private theorem rowCombination_transformInv_transpose [Lean.Grind.CommRing R]
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
            rw [← Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
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
private theorem exists_rowCombination_echelon_of_M [Lean.Grind.CommRing R]
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
private def echelonCoeffs [Lean.Grind.Field R] (E : IsEchelonForm M D)
    (v : Vector R m) : Vector R n :=
  Vector.ofFn fun i =>
    if h : i.val < D.rank then
      let pi : Fin D.rank := ⟨i.val, h⟩
      v[D.pivotCols.get pi] /
        D.echelon[(IsEchelonForm.pivotRow E pi)][D.pivotCols.get pi]
    else
      0

/-- Coefficients for expressing `v` in the row span, if the echelon rows solve it. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Option (Vector R n) :=
  let coeffs := Matrix.transpose D.transform * E.echelonCoeffs v
  if rowCombination M coeffs = v then
    some coeffs
  else
    none

/-- Decidable row-span membership test derived from `spanCoeffs`. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (E : IsEchelonForm M D)
    (v : Vector R m) : Bool :=
  (E.spanCoeffs v).isSome

/-- `spanCoeffs` returns coefficients whose row combination equals `v`. -/
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (E : IsEchelonForm M D) (_hpiv : E.HasNonzeroPivots) (v : Vector R m)
    (c : Vector R n) :
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
    (E : IsEchelonForm M D) (hpiv : E.HasNonzeroPivots) (v : Vector R m) :
    E.spanContains v = true → ∃ c : Vector R n, rowCombination M c = v := by
  intro h
  unfold spanContains at h
  cases hCoeffs : E.spanCoeffs v with
  | none =>
      simp [hCoeffs] at h
  | some c =>
      exact ⟨c, E.spanCoeffs_sound hpiv v c hCoeffs⟩

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

private theorem rowCombination_pivotCoeff [Lean.Grind.Field R] (E : IsRREF M D)
    (c : Vector R n) (p : Fin D.rank) :
    (rowCombination D.echelon c)[D.pivotCols.get p] =
      c[E.toIsEchelonForm.pivotRow p] := by
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.dot, Matrix.row, Hex.Vector.dotProduct,
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

private theorem rowCombination_eq_of_coeffs_eq_on_rank [Lean.Grind.Field R]
    (E : IsRREF M D) {c d : Vector R n}
    (hcoeff : ∀ i : Fin D.rank,
      c[E.toIsEchelonForm.pivotRow i] = d[E.toIsEchelonForm.pivotRow i]) :
    rowCombination D.echelon c = rowCombination D.echelon d := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  unfold rowCombination
  simp [HMul.hMul, Matrix.mulVec, Matrix.dot, Matrix.row, Hex.Vector.dotProduct,
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
  · exact E.toIsEchelonForm.spanContains_sound E.hasNonzeroPivots v
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
private def pivotIndex? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
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

private theorem nullspaceMatrix_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get k][k] = 1 := by
  unfold nullspaceMatrix Matrix.ofFn
  simp

private theorem nullspaceMatrix_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    E.nullspaceMatrix[E.toIsEchelonForm.freeCols.get l][k] = 0 := by
  unfold nullspaceMatrix Matrix.ofFn
  have hne : E.toIsEchelonForm.freeCols.get l ≠ E.toIsEchelonForm.freeCols.get k := by
    intro h
    exact hkl ((E.toIsEchelonForm.freeCols_injective h).symm)
  simp [hne, pivotIndex?_free_none E.toIsEchelonForm l]

private theorem nullspaceMatrix_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    E.nullspaceMatrix[D.pivotCols.get i][k] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  unfold nullspaceMatrix Matrix.ofFn
  simp [E.toIsEchelonForm.pivotCols_disjoint_freeCols i k,
    pivotIndex?_pivot E.toIsEchelonForm i]

/-- The individual nullspace basis vectors. -/
def nullspace [Lean.Grind.Ring R] (E : IsRREF M D) :
    Vector (Vector R m) (m - D.rank) :=
  Vector.ofFn fun k => Matrix.col (E.nullspaceMatrix) k

private theorem nullspace_get [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    E.nullspace.get k = Matrix.col E.nullspaceMatrix k := by
  unfold nullspace
  rw [Vector.get_ofFn]

private theorem nullspace_get_free [Lean.Grind.Ring R] (E : IsRREF M D)
    (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get k] = 1 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free E k

private theorem nullspace_get_free_ne [Lean.Grind.Ring R] (E : IsRREF M D)
    {k l : Fin (m - D.rank)} (hkl : k ≠ l) :
    (E.nullspace.get k)[E.toIsEchelonForm.freeCols.get l] = 0 := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_free_ne E hkl

private theorem nullspace_get_pivot [Lean.Grind.Ring R] (E : IsRREF M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    (E.nullspace.get k)[D.pivotCols.get i] =
      -(D.echelon[(IsEchelonForm.pivotRow E.toIsEchelonForm i)][E.toIsEchelonForm.freeCols.get k]) := by
  rw [nullspace_get]
  simpa [Matrix.col] using nullspaceMatrix_pivot E i k

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
        rw [foldl_add_eq_acc_ring zs f x hzero]
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
  apply Vector.ext
  intro r hr
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
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct
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
    unfold Matrix.mulVec Matrix.dot Matrix.row Hex.Vector.dotProduct
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
    simpa only using foldl_add_eq_acc_ring (List.finRange m)
      (fun j => D.echelon[row][j] * (E.nullspace.get k)[j]) 0 hzero

/-- Every basis vector returned by `nullspace` lies in the nullspace of `M`. -/
theorem nullspace_sound [Lean.Grind.Ring R] (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace.get k = 0 := by
  sorry

/-- Every nullspace vector is generated by the computed nullspace basis. -/
theorem nullspace_complete [Lean.Grind.Field R] (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  sorry

end IsRREF

/-- Convenience wrapper: compute row-span coefficients using `rref` internally. -/
def spanCoeffs [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Option (Vector R n) :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanCoeffs v

/-- Convenience wrapper: decide row-span membership using `rref` internally. -/
def spanContains [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
    Bool :=
  let E := (rref_isRREF M).toIsEchelonForm
  E.spanContains v

/-- The public `spanContains` wrapper is exactly row-span membership. -/
theorem spanContains_iff [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) :
    spanContains M v = true ↔ ∃ c : Vector R n, rowCombination M c = v := by
  unfold spanContains
  simpa using (rref_isRREF M).spanContains_iff v

/-- The rank returned by `rref`. -/
def rref_rank [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) : Nat :=
  (rref M).rank

/-- Convenience wrapper: compute the nullspace basis using `rref` internally. -/
def nullspace [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m) :
    Vector (Vector R m) (m - rref_rank M) :=
  let E := rref_isRREF M
  E.nullspace

end Matrix
end Hex
