/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Unique
public import HexDeterminant.Triangular

public section

/-! Executable row-lattice, kernel, pivot, and index APIs derived from HNF. -/

namespace Hex.Matrix

private theorem strictMono_fin_id_le (f : Fin n → Fin n)
    (hf : ∀ i j, i < j → f i < f j) (i : Fin n) : i.val ≤ (f i).val := by
  have aux : ∀ k (hk : k < n), k ≤ (f ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hstep : (f (⟨k, hk'⟩ : Fin n)).val <
          (f (⟨k + 1, hk⟩ : Fin n)).val :=
        hf (⟨k, hk'⟩ : Fin n) (⟨k + 1, hk⟩ : Fin n)
          (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
      have hprev := ih hk'
      change k ≤ (f (⟨k, hk'⟩ : Fin n)).val at hprev
      change k + 1 ≤ (f (⟨k + 1, hk⟩ : Fin n)).val
      omega
  exact aux i.val i.isLt

private theorem strictMono_fin_eq (f : Fin n → Fin n)
    (hf : ∀ i j, i < j → f i < f j) (i : Fin n) : f i = i := by
  let rev : Fin n → Fin n := fun x => ⟨n - 1 - x.val, by omega⟩
  let g : Fin n → Fin n := fun x => rev (f (rev x))
  have hrev (x : Fin n) : rev (rev x) = x := by
    apply Fin.ext
    simp only [rev]
    omega
  have hg : ∀ x y, x < y → g x < g y := by
    intro x y hxy
    have hryx : rev y < rev x := by
      simp only [rev, Fin.mk_lt_mk]
      omega
    have hfyx := hf (rev y) (rev x) hryx
    simp only [g, rev, Fin.mk_lt_mk] at hfyx ⊢
    omega
  have hlower := strictMono_fin_id_le f hf i
  have hupper := strictMono_fin_id_le g hg (rev i)
  simp only [g, hrev, rev] at hupper
  apply Fin.ext
  omega

private theorem foldl_natAbs_mul (xs : List Int) (a : Int) :
    (xs.foldl (fun x y => x * y) a).natAbs =
      (xs.map Int.natAbs).foldl (fun x y => x * y) a.natAbs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, Int.natAbs_mul]

private theorem vector_foldl_toList (v : Vector R n) (f : α → R → α) (a : α) :
    v.foldl f a = v.toList.foldl f a := by
  exact (Array.foldl_toList f).symm

private theorem List.get_of_eq {xs ys : List α} (h : xs = ys)
    (i : Fin xs.length) :
    xs.get i = ys.get (Fin.cast (congrArg List.length h) i) := by
  subst ys
  rfl

private theorem det_eq_zero_of_zero_row (M : Matrix Int n n) (i : Fin n)
    (hi : M[i] = 0) : det M = 0 := by
  have hscale : Matrix.rowScale M i 0 = M := by
    apply Matrix.ext_getElem
    intro r c
    rw [Matrix.getElem_rowScale]
    by_cases hri : r = i
    · subst r
      rw [if_pos rfl]
      have hentry := congrArg (fun row : Vector Int n => row[c.val]'c.isLt) hi
      have hzero : M[i][c] = 0 := by
        change M[i][c.val]'c.isLt = 0
        simpa only [Vector.getElem_zero] using hentry
      rw [hzero]
      omega
    · rw [if_neg hri]
  have hdet := det_rowScale M i 0
  rw [hscale] at hdet
  simpa using hdet

namespace Hermite

@[expose]
def solveStep (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (state : Vector Int m × Vector Int n) (row : Fin n) :
    Option (Vector Int m × Vector Int n) :=
  if hr : row.val < r then
    let i : Fin r := ⟨row.val, hr⟩
    let col := piv.get i
    let p : Int := H[(row, col)]
    if p = 0 then
      none
    else
      let value := state.1.get col
      if value % p = 0 then
        let q := value / p
        let residual := Vector.ofFn fun j => state.1.get j - q * H[(row, j)]
        some (residual, state.2 + q • Vector.unit Int row)
      else
        none
  else
    some state

@[expose]
def solveLoop (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (row : Nat) (hrow : row ≤ n) (state : Vector Int m × Vector Int n) :
    Option (Vector Int m × Vector Int n) :=
  if hend : row = n then
    some state
  else
    have hlt : row < n := by omega
    match solveStep H r piv state ⟨row, hlt⟩ with
    | none => none
    | some next => solveLoop H r piv (row + 1) (by omega) next
termination_by n - row
decreasing_by all_goals exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self row)

/-- Solve against the nonzero HNF rows by forward pivot substitution. -/
@[expose]
def solve (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (v : Vector Int m) : Option (Vector Int n) :=
  let initial : Vector Int m × Vector Int n := (v, 0)
  let result := solveLoop H r piv 0 (Nat.zero_le n) initial
  match result with
  | none => none
  | some (residual, coeffs) =>
      if residual = 0 then some coeffs else none

/-- The forward solver keeps a lattice residual, clears pivots in order, and
records exactly the row combination removed from the input. -/
def SolveInvariant (D : RowEchelonData Int n m) (v : Vector Int m)
    (row : Nat) (state : Vector Int m × Vector Int n) : Prop :=
  D.echelon.memLattice state.1 ∧
  (∀ q : Fin D.rank, q.val < row →
    state.1[D.pivotCols.get q] = 0) ∧
  vecMul state.2 D.echelon + state.1 = v

private theorem solveStep_complete {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D)
    (v : Vector Int m) (state : Vector Int m × Vector Int n) (row : Fin n)
    (hinv : SolveInvariant D v row.val state) :
    ∃ next, solveStep D.echelon D.rank D.pivotCols state row = some next ∧
      SolveInvariant D v (row.val + 1) next := by
  by_cases hr : row.val < D.rank
  · let q : Fin D.rank := ⟨row.val, hr⟩
    let col := D.pivotCols.get q
    let p : Int := D.echelon[row][col]
    have hrow : h.toIsEchelonForm.pivotRow q = row := Fin.ext rfl
    have hp : 0 < p := by
      have := h.pivot_pos q
      change 0 < D.echelon[h.toIsEchelonForm.pivotRow q][D.pivotCols.get q] at this
      rw [hrow] at this
      exact this
    have hpne : p ≠ 0 := Int.ne_of_gt hp
    rcases h.pivot_factor hinv.1 q (by
      intro i hi
      exact hinv.2.1 i hi) with ⟨a, ha⟩
    have hvalue : state.1[col] = a * p := by
      simpa only [col, p, hrow] using ha
    have hmod : state.1[col] % p = 0 := by
      rw [hvalue]
      exact Int.mul_emod_left a p
    have hdiv : state.1[col] / p = a := by
      rw [hvalue]
      exact Int.mul_ediv_cancel a hpne
    let residual : Vector Int m :=
      Vector.ofFn fun j => state.1.get j - a * D.echelon[row][j]
    let coeffs : Vector Int n := state.2 + a • Vector.unit Int row
    have hresidual_get (j : Fin m) : residual.get j =
        state.1.get j - a * D.echelon[row][j] := by
      change residual[j.val]'j.isLt = _
      simp only [residual, Vector.getElem_ofFn]
    have hresidual : residual = state.1 - a • D.echelon[row] := by
      apply Vector.ext
      intro j hj
      let jj : Fin m := ⟨j, hj⟩
      simp only [residual, Vector.getElem_ofFn]
      change state.1[jj] - a * D.echelon[row][jj] =
        (state.1 - a • D.echelon[row])[j]
      rw [Vector.getElem_sub, Vector.getElem_smul]
      rfl
    have hmem : D.echelon.memLattice residual := by
      rw [hresidual]
      exact memLattice_sub hinv.1
        (memLattice_smul a (row_memLattice D.echelon row))
    have hpivots : ∀ i : Fin D.rank, i.val < row.val + 1 →
        residual[D.pivotCols.get i] = 0 := by
      intro i hi
      by_cases hir : i.val < row.val
      · have hzero := hinv.2.1 i hir
        have hcolLt : D.pivotCols.get i < col :=
          h.toIsEchelonForm.pivotCols_sorted i q (Fin.mk_lt_mk.mpr hir)
        have hlead := h.pivot_leading q (D.pivotCols.get i) hcolLt
        change D.echelon[row][D.pivotCols.get i] = 0 at hlead
        have hget : residual[D.pivotCols.get i] =
            state.1[D.pivotCols.get i] -
              a * D.echelon[row][D.pivotCols.get i] := by
          change residual.get (D.pivotCols.get i) = _
          exact hresidual_get _
        rw [hget]
        change state.1[D.pivotCols.get i] -
          a * D.echelon[row][D.pivotCols.get i] = 0
        rw [hzero, hlead]
        omega
      · have hiq : i = q := Fin.ext (by
          change i.val = row.val
          omega)
        subst i
        have hget : residual[col] =
            state.1[col] - a * D.echelon[row][col] := by
          change residual.get col = _
          exact hresidual_get _
        rw [hget]
        change state.1[col] - a * D.echelon[row][col] = 0
        rw [hvalue]
        change a * p - a * p = 0
        omega
    have hrecord : vecMul coeffs D.echelon + residual = v := by
      simp only [coeffs]
      rw [vecMul_add, vecMul_smul, vecMul_unit, hresidual]
      apply Vector.ext
      intro j hj
      have hold := congrArg (fun w : Vector Int m => w[j]) hinv.2.2
      simp only [Vector.getElem_add, Vector.getElem_sub,
        Vector.getElem_smul] at hold ⊢
      omega
    refine ⟨(residual, coeffs), ?_, hmem, hpivots, hrecord⟩
    unfold solveStep
    rw [dif_pos hr]
    simp only [Matrix.getElem_pair_eq_nested]
    change (if p = 0 then none else
      if state.1[col] % p = 0 then
        some
          (Vector.ofFn fun j => state.1.get j - state.1[col] / p * D.echelon[row][j],
            state.2 + (state.1[col] / p) • Vector.unit Int row)
      else none) = some (residual, coeffs)
    rw [if_neg hpne, if_pos hmod]
    congr 2
    · apply Vector.ext
      intro j hj
      simp only [Vector.getElem_ofFn, residual, hdiv]
    · exact congrArg (fun b => state.2 + b • Vector.unit Int row) hdiv
  · refine ⟨state, ?_, hinv.1, ?_, hinv.2.2⟩
    · unfold solveStep
      rw [dif_neg hr]
    · intro q hq
      exact hinv.2.1 q (by omega)

private theorem solveLoop_complete {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D)
    (v : Vector Int m) (row : Nat) (hrow : row ≤ n)
    (state : Vector Int m × Vector Int n)
    (hinv : SolveInvariant D v row state) :
    ∃ coeffs, solveLoop D.echelon D.rank D.pivotCols row hrow state =
        some (0, coeffs) ∧ vecMul coeffs D.echelon = v := by
  unfold solveLoop
  by_cases hend : row = n
  · rw [dif_pos hend]
    subst row
    have hzero : state.1 = 0 := h.eq_zero_of_pivots hinv.1 (by
      intro q
      exact hinv.2.1 q (Nat.lt_of_lt_of_le q.isLt
        h.toIsEchelonForm.rank_le_n))
    refine ⟨state.2, ?_, ?_⟩
    · apply congrArg some
      apply Prod.ext
      · exact hzero
      · rfl
    · have hrecord := hinv.2.2
      rw [hzero] at hrecord
      apply Vector.ext
      intro j hj
      have hentry := congrArg (fun w : Vector Int m => w[j]) hrecord
      simp only [Vector.getElem_add, Vector.getElem_zero] at hentry
      omega
  · rw [dif_neg hend]
    have hlt : row < n := by omega
    rcases solveStep_complete h v state ⟨row, hlt⟩ hinv with
      ⟨next, hstep, hnext⟩
    simp only [hstep]
    exact solveLoop_complete h v (row + 1) (by omega) next hnext
termination_by n - row
decreasing_by exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self row)

/-- Forward pivot substitution succeeds on every vector in an HNF row
lattice and returns coefficients for it. -/
theorem solve_complete {A : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF A D) {v : Vector Int m} (hv : D.echelon.memLattice v) :
    ∃ coeffs, solve D.echelon D.rank D.pivotCols v = some coeffs ∧
      vecMul coeffs D.echelon = v := by
  let initial : Vector Int m × Vector Int n := (v, 0)
  have hinitial : SolveInvariant D v 0 initial := by
    refine ⟨hv, ?_, ?_⟩
    · intro q hq
      omega
    · dsimp only [initial]
      have hzero : vecMul (0 : Vector Int n) D.echelon = 0 :=
        Matrix.mulVec_zero (Matrix.transpose D.echelon)
      rw [hzero]
      apply Vector.ext
      intro j hj
      simp only [Vector.getElem_add, Vector.getElem_zero]
      omega
  rcases solveLoop_complete h v 0 (Nat.zero_le n) initial hinitial with
    ⟨coeffs, hloop, hcoeffs⟩
  refine ⟨coeffs, ?_, hcoeffs⟩
  unfold solve
  dsimp only
  rw [hloop]
  simp

end Hermite

/-- Integer coefficients expressing `v` as a combination of the rows of
`A`, or `none` when the forward HNF solve does not verify. -/
@[expose]
def latticeCoeffs (A : Matrix Int n m) (v : Vector Int m) : Option (Vector Int n) :=
  let D := hnfData A
  match Hermite.solve D.echelon D.rank D.pivotCols v with
  | none => none
  | some d =>
      let c := Matrix.transpose D.transform * d
      if vecMul c A = v then some c else none

/-- Decide membership in the integer row lattice of `A`. -/
@[expose]
def latticeContains (A : Matrix Int n m) (v : Vector Int m) : Bool :=
  (latticeCoeffs A v).isSome

/-- The rows of the transform corresponding to zero HNF rows. -/
@[expose]
def kernelBasis (A : Matrix Int n m) : Matrix Int (n - hnfRank A) n :=
  let hr := Hermite.run_rank_le (Hermite.formAccumulator n) A
  Matrix.ofFn fun i j =>
    let row : Fin n := ⟨hnfRank A + i.val, by omega⟩
    (hnfData A).transform[(row, j)]

/-- Positive HNF pivot values in pivot-column order. -/
@[expose]
def pivots (A : Matrix Int n m) : Vector Nat (hnfRank A) :=
  let result := Hermite.run (Hermite.formAccumulator n) A
  have hr := Hermite.run_rank_le (Hermite.formAccumulator n) A
  Vector.ofFn fun i =>
    let row : Fin n := Fin.castLE hr i
    (result.matrix[(row, result.pivotVector.get i)]).natAbs

/-- Index of the row lattice in `Int^m`, with `0` denoting infinite index. -/
@[expose]
def latticeIndex (A : Matrix Int n m) : Nat :=
  if hnfRank A = m then
    (pivots A).foldl (· * ·) 1
  else
    0

set_option maxHeartbeats 400000 in
private theorem recover_of_inverse {A : Matrix Int n m} {H : Matrix Int n m}
    {U W : Matrix Int n n} (hUA : U * A = H)
    (hWU : W * U = Matrix.identity (R := Int) n) : W * H = A := by
  calc
    W * H = W * (U * A) := by rw [hUA]
    _ = (W * U) * A := (Matrix.mul_assoc W U A).symm
    _ = Matrix.identity (R := Int) n * A := by rw [hWU]
    _ = A := Matrix.identity_mul A

set_option maxHeartbeats 400000 in
/-- Hermite reduction preserves the integer row lattice. -/
theorem hnf_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    A.memLattice v ↔ (hnf A).memLattice v := by
  let D := hnfWithInv A
  have hforward : D.rowData.transform * A = D.rowData.echelon :=
    hnfWithInv_transform_mul A
  have hback : D.inverse * D.rowData.echelon = A :=
    recover_of_inverse hforward (hnfWithInv_inv_mul A)
  have hform : hnf A = D.rowData.echelon := by
    rw [hnf_eq_hnfData_echelon, ← hnfWithInv_data A]
  rw [hform]
  exact memLattice_iff_of_mul_eq hforward hback v

/-- A row of a matrix product is the corresponding executable row-vector
product. -/
theorem row_mul_eq_vecMul (M : Matrix Int n' n) (N : Matrix Int n m)
    (i : Fin n') : Matrix.row (M * N) i = vecMul (Matrix.row M i) N := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (M * N)[i][jj] = (Matrix.row M i * N)[jj]
  rw [Matrix.getElem_mul, Matrix.getElem_vecMul]
  exact Vector.dotProduct_comm _ _

private theorem basis_mul_form (A : Matrix Int n m) :
    let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
      if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
        then 1 else 0
    P * hnf A = hnfBasis A := by
  dsimp only
  let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
      then 1 else 0
  apply Matrix.ext_getElem
  intro i j
  have hrow : Matrix.row P i = Vector.ofFn fun k : Fin n =>
      if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = k
        then 1 else 0 := by
    apply Vector.ext
    intro k hk
    let kk : Fin n := ⟨k, hk⟩
    have hp : (Matrix.row P i)[kk] =
        (if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = kk
          then 1 else 0) := by
      rw [Matrix.getElem_row]
      simp only [P, Matrix.getElem_ofFn]
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hp
  have hmul := row_mul_eq_vecMul P (hnf A) i
  rw [hrow, IsRowReduced.vecMul_single] at hmul
  have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
  calc
    (P * hnf A)[i][j] =
        (hnf A)[Fin.castLE
          (Hermite.run_rank_le (Hermite.formAccumulator n) A) i][j] := hentry
    _ = (hnfBasis A)[i][j] := by
      simp only [hnfBasis, Matrix.getElem_ofFn,
        Matrix.getElem_pair_eq_nested]

private theorem form_mul_basis (A : Matrix Int n m) :
    let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
      if i.val = j.val then 1 else 0
    Q * hnfBasis A = hnf A := by
  dsimp only
  let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  have hform := hnfData_isHNF A
  have hrank := hnfRank_eq A
  apply Matrix.ext_getElem
  intro i j
  by_cases hir : i.val < hnfRank A
  · let ii : Fin (hnfRank A) := ⟨i.val, hir⟩
    have hrow : Matrix.row Q i = Vector.ofFn fun k : Fin (hnfRank A) =>
        if ii = k then 1 else 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (hnfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] =
          (if ii = kk then 1 else 0) := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        congr 1
        exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hq
    have hmul := row_mul_eq_vecMul Q (hnfBasis A) i
    rw [hrow, IsRowReduced.vecMul_single] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    calc
      (Q * hnfBasis A)[i][j] = (hnfBasis A)[ii][j] := hentry
      _ = (hnf A)[i][j] := by
        simp only [hnfBasis, Matrix.getElem_ofFn,
          Matrix.getElem_pair_eq_nested]
        congr 2
  · have hrow : Matrix.row Q i = 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (hnfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] = 0 := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        rw [if_neg]
        omega
      have hz : (0 : Vector Int (hnfRank A))[kk.val] = 0 :=
        Vector.getElem_zero kk.val kk.isLt
      calc
        (Matrix.row Q i)[k] = 0 := by
          simpa only [Fin.getElem_fin] using hq
        _ = (0 : Vector Int (hnfRank A))[k] := hz.symm
    have hmul := row_mul_eq_vecMul Q (hnfBasis A) i
    have hzero : vecMul (0 : Vector Int (hnfRank A)) (hnfBasis A) = 0 :=
      Matrix.mulVec_zero (Matrix.transpose (hnfBasis A))
    rw [hrow, hzero] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    have hiD : (hnfData A).rank ≤ i.val := by omega
    have hz := hform.toIsEchelonForm.zero_row i hiD
    have hzentry := congrArg (fun row : Vector Int m => row.get j) hz
    rw [← hnf_eq_hnfData_echelon A] at hzentry
    calc
      (Q * hnfBasis A)[i][j] = (0 : Vector Int m)[j] := hentry
      _ = (hnf A)[i][j] := hzentry.symm

/-- Discarding the trailing zero rows of HNF does not change its integer row
lattice. -/
theorem hnfBasis_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    (hnfBasis A).memLattice v ↔ A.memLattice v := by
  let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
      then 1 else 0
  let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  have hP : P * hnf A = hnfBasis A := basis_mul_form A
  have hQ : Q * hnfBasis A = hnf A := form_mul_basis A
  constructor
  · intro hv
    exact (hnf_memLattice_iff A v).2 (memLattice_of_mul_eq hP hv)
  · intro hv
    exact memLattice_of_mul_eq hQ ((hnf_memLattice_iff A v).1 hv)

/-- Every returned lattice coefficient vector satisfies its advertised
row-combination equation. -/
theorem latticeCoeffs_sound {A : Matrix Int n m} {v : Vector Int m}
    {c : Vector Int n} :
    latticeCoeffs A v = some c → vecMul c A = v := by
  intro h
  unfold latticeCoeffs at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · rename_i d hverify
      injection h with hc
      subst c
      exact hverify
    · contradiction

/-- Every vector in the integer row lattice receives a coefficient
certificate. -/
theorem latticeCoeffs_complete {A : Matrix Int n m} {v : Vector Int m} :
    (∃ c, vecMul c A = v) → (latticeCoeffs A v).isSome := by
  intro hv
  let D := hnfData A
  have hvH : D.echelon.memLattice v :=
    ((hnfData_isHNF A).memLattice_iff v).1 hv
  rcases Hermite.solve_complete (hnfData_isHNF A) hvH with
    ⟨d, hsolve, hd⟩
  let c : Vector Int n := Matrix.transpose D.transform * d
  have hc : vecMul c A = v := by
    change vecMul (Matrix.transpose D.transform * d) A = v
    rw [vecMul_transpose_mul, (hnfData_isHNF A).transform_mul, hd]
  unfold latticeCoeffs
  dsimp only
  rw [hsolve]
  dsimp only
  rw [if_pos hc]
  rfl

/-- The executable lattice predicate is equivalent to integer row-lattice
membership. -/
theorem latticeContains_iff {A : Matrix Int n m} {v : Vector Int m} :
    latticeContains A v = true ↔ ∃ c, vecMul c A = v := by
  constructor
  · intro hv
    unfold latticeContains at hv
    generalize hcoeffs : latticeCoeffs A v = result at hv
    cases result with
    | none => contradiction
    | some c => exact ⟨c, latticeCoeffs_sound hcoeffs⟩
  · intro hv
    unfold latticeContains
    exact latticeCoeffs_complete hv

private theorem take_append_drop {R : Type} (v : Vector R n) (r : Nat)
    (hr : r ≤ n) :
    (((v.take r).cast (Nat.min_eq_left hr)) ++ v.drop r).cast
      (Nat.add_sub_of_le hr) = v := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_cast]
  by_cases hir : i < r
  · rw [Vector.getElem_append_left hir, Vector.getElem_cast,
      Vector.getElem_take]
  · have hri : r ≤ i := Nat.le_of_not_gt hir
    rw [Vector.getElem_append_right]
    · rw [Vector.getElem_drop]
      congr 1
      omega
    · simpa [Nat.min_eq_left hr] using hri

private theorem dotProduct_cast {R : Type} [Mul R] [Add R] [OfNat R 0]
    (u v : Vector R n) (h : n = n') :
    (u.cast h).dotProduct (v.cast h) = u.dotProduct v := by
  subst n'
  rfl

private theorem dotProduct_drop_of_head_zero {R : Type} [Lean.Grind.Ring R]
    (u v : Vector R n) (r : Nat) (hr : r ≤ n)
    (hz : ∀ i : Fin r, u[Fin.castLE hr i] = 0) :
    (u.drop r).dotProduct (v.drop r) = u.dotProduct v := by
  let hu : Vector R r := (u.take r).cast (Nat.min_eq_left hr)
  let hv : Vector R r := (v.take r).cast (Nat.min_eq_left hr)
  have huz : hu = 0 := by
    apply Vector.ext
    intro i hi
    simp only [hu, Vector.getElem_cast, Vector.getElem_take,
      Vector.getElem_zero]
    exact hz ⟨i, hi⟩
  have husplit := take_append_drop u r hr
  have hvsplit := take_append_drop v r hr
  calc
    (u.drop r).dotProduct (v.drop r) =
        hu.dotProduct hv + (u.drop r).dotProduct (v.drop r) := by
          have hdot : (0 : Vector R r).dotProduct hv = 0 := by
            unfold Vector.dotProduct
            apply List.foldl_add_eq_self
            intro i _hi
            rw [show (0 : Vector R r)[i] = 0 by
              exact Vector.getElem_zero i.val i.isLt]
            grind
          rw [huz, hdot]
          grind
    _ = (hu ++ u.drop r).dotProduct (hv ++ v.drop r) :=
      (Vector.dotProduct_append hu (u.drop r) hv (v.drop r)).symm
    _ = (((hu ++ u.drop r).cast (Nat.add_sub_of_le hr)).dotProduct
        ((hv ++ v.drop r).cast (Nat.add_sub_of_le hr))) := by
          exact (dotProduct_cast (hu ++ u.drop r) (hv ++ v.drop r)
            (Nat.add_sub_of_le hr)).symm
    _ = u.dotProduct v := by rw [husplit, hvsplit]

private theorem vecMul_kernelBasis (A : Matrix Int n m) (d : Vector Int n)
    (hz : ∀ i : Fin (hnfRank A),
      d[Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i] = 0) :
    vecMul (d.drop (hnfRank A)) (kernelBasis A) =
      vecMul d (hnfData A).transform := by
  let r := hnfRank A
  have hr : r ≤ n := Hermite.run_rank_le (Hermite.formAccumulator n) A
  apply Vector.ext
  intro j hj
  let col : Fin n := ⟨j, hj⟩
  change ((d.drop r) * kernelBasis A)[col] =
    (d * (hnfData A).transform)[col]
  rw [getElem_vecMul, getElem_vecMul]
  have hcol : Matrix.col (kernelBasis A) col =
      (Matrix.col (hnfData A).transform col).drop r := by
    apply Vector.ext
    intro i hi
    unfold Matrix.col
    rw [Vector.getElem_ofFn]
    rw [Vector.getElem_drop, Vector.getElem_ofFn]
    simp only [kernelBasis, Matrix.getElem_ofFn,
      Matrix.getElem_pair_eq_nested, r]
  rw [hcol]
  calc
    ((Matrix.col (hnfData A).transform col).drop r).dotProduct (d.drop r) =
        (d.drop r).dotProduct
          ((Matrix.col (hnfData A).transform col).drop r) :=
      Vector.dotProduct_comm _ _
    _ = d.dotProduct (Matrix.col (hnfData A).transform col) :=
      dotProduct_drop_of_head_zero d
        (Matrix.col (hnfData A).transform col) r hr hz
    _ = (Matrix.col (hnfData A).transform col).dotProduct d :=
      Vector.dotProduct_comm _ _

/-- The returned kernel rows are annihilated by the input matrix. -/
theorem kernelBasis_mul (A : Matrix Int n m) : kernelBasis A * A = 0 := by
  let D := hnfData A
  have hform := hnfData_isHNF A
  have hrank : hnfRank A = D.rank := hnfRank_eq A
  apply Matrix.ext_getElem
  intro i j
  let row : Fin n := ⟨hnfRank A + i.val, by
    have hr := hform.toIsEchelonForm.rank_le_n
    omega⟩
  have hrow : D.rank ≤ row.val := by simp only [row]; omega
  have hzero : D.echelon[row] = 0 := hform.toIsEchelonForm.zero_row row hrow
  calc
    (kernelBasis A * A)[i][j] = (D.transform * A)[row][j] := by
      simp only [D, row, Matrix.getElem_mul, kernelBasis, Matrix.getElem_ofFn,
        Matrix.getElem_row, Matrix.getElem_col, Matrix.getElem_pair_eq_nested,
        Vector.dotProduct]
    _ = D.echelon[row][j] := by rw [hnfData_transform_mul A]
    _ = 0 := by rw [hzero]; simp
    _ = (0 : Matrix Int (n - hnfRank A) m)[i][j] :=
      (Matrix.getElem_zero i j).symm

set_option maxHeartbeats 400000 in
/-- Every integer left-kernel vector is an integer combination of the returned
kernel rows. -/
theorem kernelBasis_complete {A : Matrix Int n m} {x : Vector Int n} :
    vecMul x A = 0 → ∃ c, vecMul c (kernelBasis A) = x := by
  intro hx
  let D := hnfData A
  let W := (hnfWithInv A).inverse
  let d : Vector Int n := Matrix.transpose W * x
  have hform : IsHNF A D := hnfData_isHNF A
  have hinv : W * D.transform = Matrix.identity (R := Int) n := by
    simp only [W, D]
    rw [← hnfWithInv_data A]
    exact hnfWithInv_inv_mul A
  have hd : vecMul d D.echelon = 0 := by
    calc
      vecMul d D.echelon = vecMul x A :=
        hform.toIsEchelonForm.vecMul_transformInv_transpose hinv x
      _ = 0 := hx
  have hr : hnfRank A ≤ n :=
    Hermite.run_rank_le (Hermite.formAccumulator n) A
  have hz : ∀ i : Fin (hnfRank A), d[Fin.castLE hr i] = 0 := by
    intro i
    have hi : i.val < D.rank := by
      rw [← hnfRank_eq A]
      exact i.isLt
    let ii : Fin D.rank := ⟨i.val, hi⟩
    have hcoeff := hform.coeff_eq_zero d hd ii
    have hrow : hform.toIsEchelonForm.pivotRow ii = Fin.castLE hr i := Fin.ext rfl
    change d.get (Fin.castLE hr i) = 0
    calc
      d.get (Fin.castLE hr i) =
          d.get (hform.toIsEchelonForm.pivotRow ii) :=
        congrArg d.get hrow.symm
      _ = 0 := hcoeff
  have hrecover : Matrix.transpose D.transform * d = x := by
    calc
      Matrix.transpose D.transform * d =
          Matrix.transpose D.transform * (Matrix.transpose W * x) := rfl
      _ = (Matrix.transpose D.transform * Matrix.transpose W) * x :=
        (Matrix.mul_assoc_vec D.transform.transpose W.transpose x).symm
      _ = Matrix.transpose (W * D.transform) * x := by
        rw [← Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (Matrix.identity (R := Int) n) * x := by rw [hinv]
      _ = Matrix.identity (R := Int) n * x := by rw [Matrix.transpose_identity]
      _ = x := Matrix.identity_mulVec x
  refine ⟨d.drop (hnfRank A), ?_⟩
  calc
    vecMul (d.drop (hnfRank A)) (kernelBasis A) =
        vecMul d D.transform := vecMul_kernelBasis A d hz
    _ = x := hrecover

set_option maxHeartbeats 400000 in
/-- The returned kernel rows are linearly independent over the integers. -/
theorem kernelBasis_independent {A : Matrix Int n m}
    {c : Vector Int (n - hnfRank A)} :
    vecMul c (kernelBasis A) = 0 → c = 0 := by
  intro hc
  let r := hnfRank A
  have hr : r ≤ n := Hermite.run_rank_le (Hermite.formAccumulator n) A
  let d : Vector Int n := Vector.ofFn fun i =>
    if h : i.val < r then 0 else c[i.val - r]'(by omega)
  have hz : ∀ i : Fin r, d[Fin.castLE hr i] = 0 := by
    intro i
    simp [d, i.isLt]
  have hdrop : d.drop r = c := by
    apply Vector.ext
    intro i hi
    simp only [d, Vector.getElem_drop, Vector.getElem_ofFn]
    rw [dite_eq_right (by omega)]
    congr 1
    omega
  have hdU : vecMul d (hnfData A).transform = 0 := by
    rw [← vecMul_kernelBasis A d hz, hdrop, hc]
  let W := (hnfWithInv A).inverse
  have hinv : (hnfData A).transform * W = Matrix.identity (R := Int) n := by
    simp only [W]
    rw [← hnfWithInv_data A]
    exact hnfWithInv_mul_inv A
  have hd : d = 0 := by
    have hrecover : Matrix.transpose W *
        (Matrix.transpose (hnfData A).transform * d) = d := by
      calc
        Matrix.transpose W * (Matrix.transpose (hnfData A).transform * d) =
            (Matrix.transpose W * Matrix.transpose (hnfData A).transform) * d :=
          (Matrix.mul_assoc_vec W.transpose (hnfData A).transform.transpose d).symm
        _ = Matrix.transpose ((hnfData A).transform * W) * d := by
          rw [← Matrix.transpose_mul_of_mul_comm]
        _ = Matrix.transpose (Matrix.identity (R := Int) n) * d := by rw [hinv]
        _ = Matrix.identity (R := Int) n * d := by rw [Matrix.transpose_identity]
        _ = d := Matrix.identity_mulVec d
    have hzero : Matrix.transpose W *
        (Matrix.transpose (hnfData A).transform * d) = 0 := by
      change Matrix.transpose W * vecMul d (hnfData A).transform = 0
      rw [hdU]
      exact Matrix.mulVec_zero _
    exact hrecover.symm.trans hzero
  have hdropzero : (0 : Vector Int n).drop r = 0 := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_drop]
    calc
      (0 : Vector Int n)[r + i] = (0 : Int) :=
        Vector.getElem_zero (α := Int) (n := n) (r + i) (by
          simp only [r] at hi ⊢
          omega)
      _ = (0 : Vector Int (n - r))[i] :=
        (Vector.getElem_zero (α := Int) (n := n - r) i hi).symm
  calc
    c = d.drop r := hdrop.symm
    _ = (0 : Vector Int n).drop r := congrArg (fun v : Vector Int n => v.drop r) hd
    _ = 0 := hdropzero

@[simp] theorem latticeContains_eq_isSome (A : Matrix Int n m) (v : Vector Int m) :
    latticeContains A v = (latticeCoeffs A v).isSome := rfl

/-- The index definition is the pivot product in the full-rank case. -/
theorem latticeIndex_eq_prod_pivots (A : Matrix Int n m) (h : hnfRank A = m) :
    latticeIndex A = (pivots A).foldl (· * ·) 1 := by
  simp [latticeIndex, h]

set_option maxHeartbeats 800000 in
/-- For a square integer matrix, the HNF pivot product is the absolute
determinant. -/
theorem latticeIndex_eq_det (A : Matrix Int n n) :
    latticeIndex A = (det A).natAbs := by
  let D := hnfData A
  have hform : IsHNF A D := hnfData_isHNF A
  have htransform : D.transform * A = D.echelon := hnfData_transform_mul A
  have hdetmul : det D.echelon = det D.transform * det A := by
    rw [← det_mul, htransform]
  have habs : (det D.echelon).natAbs = (det A).natAbs := by
    rcases hform.det_transform with hU | hU
    · rw [hU] at hdetmul
      simpa using congrArg Int.natAbs hdetmul
    · rw [hU] at hdetmul
      have h := congrArg Int.natAbs hdetmul
      simpa [Int.natAbs_mul] using h
  by_cases hfull : hnfRank A = n
  · have hrD : D.rank = n := by
      rw [← hnfRank_eq A]
      exact hfull
    let f : Fin n → Fin n := fun i => D.pivotCols.get (Fin.cast hrD.symm i)
    have hf : ∀ i j, i < j → f i < f j := by
      intro i j hij
      exact hform.toIsEchelonForm.pivotCols_sorted
        (Fin.cast hrD.symm i) (Fin.cast hrD.symm j) hij
    have hfid : ∀ i, f i = i := strictMono_fin_eq f hf
    have hupper : ∀ i j : Fin n, j.val < i.val → D.echelon[i][j] = 0 := by
      intro i j hji
      let q : Fin D.rank := Fin.cast hrD.symm i
      have hlead := hform.pivot_leading q j (by
        have hfi := hfid i
        change j < f i
        rw [hfi]
        exact hji)
      have hrow : hform.toIsEchelonForm.pivotRow q = i := Fin.ext rfl
      rw [← hrow]
      exact hlead
    have hdiag : ∀ i : Fin n, 0 < D.echelon[i][i] := by
      intro i
      let q : Fin D.rank := Fin.cast hrD.symm i
      have hp := hform.pivot_pos q
      have hcol : D.pivotCols.get q = i := hfid i
      let v : Vector Int n := D.echelon[q.val]'(Nat.lt_of_lt_of_le q.isLt
        hform.toIsEchelonForm.rank_le_n)
      change 0 < v.get (D.pivotCols.get q) at hp
      have hentry : v.get (D.pivotCols.get q) = v.get i := congrArg v.get hcol
      rw [hentry] at hp
      change 0 < (D.echelon[i.val]'i.isLt).get i
      simpa only [v, q, Fin.cast, Fin.getElem_fin] using hp
    have hpivList : (pivots A).toList =
        List.ofFn (fun i : Fin n => D.echelon[i][i].natAbs) := by
      apply List.ext_getElem
      · simp [hfull]
      · intro k hkA hkD
        have hk : k < n := by simpa using hkD
        let i : Fin n := ⟨k, hk⟩
        have hcol : D.pivotCols.get (Fin.cast hrD.symm i) = i := hfid i
        rw [Vector.getElem_toList, List.getElem_ofFn]
        unfold pivots
        rw [Vector.getElem_ofFn]
        let rs := Hermite.run (Hermite.formAccumulator n) A
        let rt := Hermite.run (Hermite.transformAccumulator n) A
        have hm : rs.matrix = rt.matrix :=
          Hermite.run_matrix_agree (Hermite.formAccumulator n)
            (Hermite.transformAccumulator n) A
        have hp : rs.pivots = rt.pivots :=
          Hermite.run_pivots_agree (Hermite.formAccumulator n)
            (Hermite.transformAccumulator n) A
        have hkR : k < hnfRank A := by rw [hfull]; exact hk
        let is : Fin rs.pivots.length := ⟨k, by simpa [rs, hnfRank] using hkR⟩
        let it : Fin rt.pivots.length :=
          Fin.cast (congrArg List.length hp) is
        have hrow : Fin.castLE
            (Hermite.run_rank_le (Hermite.formAccumulator n) A)
            (⟨k, hkR⟩ : Fin (hnfRank A)) = i := Fin.ext rfl
        have hit : it = Fin.cast hrD.symm i := Fin.ext rfl
        have hcolS : rs.pivotVector.get is = i := by
          rw [Hermite.Result.pivotVector_get]
          calc
            rs.pivots.get is = rt.pivots.get it := List.get_of_eq hp is
            _ = rt.pivotVector.get it := (Hermite.Result.pivotVector_get rt it).symm
            _ = D.pivotCols.get (Fin.cast hrD.symm i) := by
              rw [hit]
              simp [D, rt, hnfData]
            _ = i := hcol
        change rs.matrix[(Fin.castLE
          (Hermite.run_rank_le (Hermite.formAccumulator n) A)
          (⟨k, hkR⟩ : Fin (hnfRank A)),
          rs.pivotVector.get is)].natAbs = D.echelon[i][i].natAbs
        rw [hrow, hcolS, hm]
        simp [D, rt, hnfData]
    have hdet := det_upperTriangular_eq_foldl_diag D.echelon hupper
    have hdetAbs : (det D.echelon).natAbs =
        (List.finRange n).foldl
          (fun acc i => acc * D.echelon[i][i].natAbs) 1 := by
      rw [hdet]
      have h := foldl_natAbs_mul
        ((List.finRange n).map fun i => D.echelon[i][i]) 1
      simpa [List.foldl_map, Function.comp_def] using h
    have hpivFold : (pivots A).foldl (fun x y => x * y) 1 =
        (List.finRange n).foldl
          (fun acc i => acc * D.echelon[i][i].natAbs) 1 := by
      rw [vector_foldl_toList, hpivList]
      have hlist : (List.ofFn fun i : Fin n => D.echelon[i][i].natAbs) =
          (List.finRange n).map (fun i => D.echelon[i][i].natAbs) := by
        rw [List.finRange, List.map_ofFn]
        rfl
      rw [hlist, List.foldl_map]
    rw [latticeIndex_eq_prod_pivots A hfull, hpivFold, ← hdetAbs, habs]
  · have hrDlt : D.rank < n := by
      have hrDle := hform.toIsEchelonForm.rank_le_n
      have hneD : D.rank ≠ n := by
        intro heq
        apply hfull
        rw [hnfRank_eq A, heq]
      omega
    let row : Fin n := ⟨D.rank, hrDlt⟩
    have hrow : D.echelon[row] = 0 :=
      hform.toIsEchelonForm.zero_row row (Nat.le_refl _)
    have hdetzero : det D.echelon = 0 := det_eq_zero_of_zero_row D.echelon row hrow
    have hdetA : det A = 0 := by
      rcases hform.det_transform with hU | hU
      · rw [hdetzero, hU] at hdetmul
        omega
      · rw [hdetzero, hU] at hdetmul
        omega
    simp [latticeIndex, hfull, hdetA]

end Hex.Matrix
