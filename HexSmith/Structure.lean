/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Unique
import Batteries.Data.Vector.Lemmas

public section

/-! Consumer-facing data derived from the Smith diagonal. -/

namespace Hex.Matrix

/-- The structure of `ℤᵐ / rowlattice A`: free rank and non-unit torsion
invariants, in divisibility-chain order. -/
@[expose]
def abelianStructure (A : Matrix Int n m) : AbelianStructure :=
  let result := Smith.run (Smith.formAccumulator n m) A
  let factors := result.diag.filterMap fun d =>
    if 1 < d then some d.natAbs else none
  { freeRank := m - result.diag.length
    torsionFactors := factors.toArray }

@[simp]
theorem abelianStructure_freeRank (A : Matrix Int n m) :
    (abelianStructure A).freeRank = m - snfRank A := by
  rfl

/-- The independent relation rows obtained by discarding the zero rows of the
Smith-transformed presentation. -/
@[expose]
def smithBasis (A : Matrix Int n m) : Matrix Int (snfRank A) m :=
  let S := snfData A
  Matrix.takeRows (S.left * A) (snfRank A) (snfRank_le_n A)

/-- Cancel the recorded right transform to recover the left-transformed
presentation from the Smith diagonal. -/
theorem snfData_left_mul (A : Matrix Int n m) :
    (snfData A).left * A =
      diagMatrix (snfData A).diag n m * (snfData A).rightInv := by
  let S := snfData A
  have hS := snfData_isSNF A
  calc
    S.left * A = (S.left * A) * Matrix.identity m :=
      (Matrix.mul_identity (S.left * A)).symm
    _ = (S.left * A) * (S.right * S.rightInv) := by rw [hS.right_inv]
    _ = (S.left * A * S.right) * S.rightInv :=
      (Matrix.mul_assoc (S.left * A) S.right S.rightInv).symm
    _ = diagMatrix S.diag n m * S.rightInv := by rw [hS.mul_eq]

private theorem smithBasis_mul_form (A : Matrix Int n m) :
    let P : Matrix Int (snfRank A) n := Matrix.ofFn fun i j =>
      if Fin.castLE (snfRank_le_n A) i = j then 1 else 0
    P * ((snfData A).left * A) = smithBasis A := by
  dsimp only
  let P : Matrix Int (snfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (snfRank_le_n A) i = j then 1 else 0
  apply Matrix.ext_getElem
  intro i j
  have hrow : Matrix.row P i = Vector.ofFn fun k : Fin n =>
      if Fin.castLE (snfRank_le_n A) i = k then 1 else 0 := by
    apply Vector.ext
    intro k hk
    let kk : Fin n := ⟨k, hk⟩
    have hp : (Matrix.row P i)[kk] =
        (if Fin.castLE (snfRank_le_n A) i = kk then 1 else 0) := by
      rw [Matrix.getElem_row]
      simp only [P, Matrix.getElem_ofFn]
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hp
  have hmul := row_mul_eq_vecMul P ((snfData A).left * A) i
  rw [hrow, IsRowReduced.vecMul_single] at hmul
  have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
  calc
    (P * ((snfData A).left * A))[i][j] =
        ((snfData A).left * A)[Fin.castLE (snfRank_le_n A) i][j] := hentry
    _ = (smithBasis A)[i][j] := by
      simp only [smithBasis, Matrix.getElem_takeRows]
      exact congrArg (fun q : Fin n => ((snfData A).left * A)[q][j])
        (Fin.ext rfl)

private theorem form_mul_smithBasis (A : Matrix Int n m) :
    let Q : Matrix Int n (snfRank A) := Matrix.ofFn fun i j =>
      if i.val = j.val then 1 else 0
    Q * smithBasis A = (snfData A).left * A := by
  dsimp only
  let Q : Matrix Int n (snfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  apply Matrix.ext_getElem
  intro i j
  by_cases hir : i.val < snfRank A
  · let ii : Fin (snfRank A) := ⟨i.val, hir⟩
    have hrow : Matrix.row Q i = Vector.ofFn fun k : Fin (snfRank A) =>
        if ii = k then 1 else 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (snfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] = (if ii = kk then 1 else 0) := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        congr 1
        exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hq
    have hmul := row_mul_eq_vecMul Q (smithBasis A) i
    rw [hrow, IsRowReduced.vecMul_single] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    calc
      (Q * smithBasis A)[i][j] = (smithBasis A)[ii][j] := hentry
      _ = ((snfData A).left * A)[i][j] := by
        simp only [smithBasis, Matrix.getElem_takeRows]
        congr 2
  · have hrow : Matrix.row Q i = 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (snfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] = 0 := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        rw [if_neg]
        omega
      have hz : (0 : Vector Int (snfRank A))[kk.val] = 0 :=
        Vector.getElem_zero kk.val kk.isLt
      calc
        (Matrix.row Q i)[k] = 0 := by
          simpa only [Fin.getElem_fin] using hq
        _ = (0 : Vector Int (snfRank A))[k] := hz.symm
    have hmul := row_mul_eq_vecMul Q (smithBasis A) i
    have hzero : vecMul (0 : Vector Int (snfRank A)) (smithBasis A) = 0 :=
      Matrix.mulVec_zero (Matrix.transpose (smithBasis A))
    rw [hrow, hzero] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    have hsource := congrArg (fun M : Matrix Int n m => Matrix.row M i)
      (snfData_left_mul A)
    have hdiag : Matrix.row (diagMatrix (snfData A).diag n m) i = 0 :=
      Matrix.row_diagMatrix_of_ge (snfData A).diag i (by
        rw [← snfRank_eq_data]
        omega)
    have hright : Matrix.row
        (diagMatrix (snfData A).diag n m * (snfData A).rightInv) i = 0 := by
      rw [row_mul_eq_vecMul, hdiag]
      exact Matrix.mulVec_zero (Matrix.transpose (snfData A).rightInv)
    have hsourceZero : Matrix.row ((snfData A).left * A) i = 0 := by
      exact hsource.trans hright
    have hzentry := congrArg (fun row : Vector Int m => row.get j) hsourceZero
    calc
      (Q * smithBasis A)[i][j] = (0 : Vector Int m)[j] := hentry
      _ = ((snfData A).left * A)[i][j] := hzentry.symm

/-- The Smith basis rows generate exactly the original integer row lattice. -/
theorem smithBasis_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    (smithBasis A).memLattice v ↔ A.memLattice v := by
  let P : Matrix Int (snfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (snfRank_le_n A) i = j then 1 else 0
  let Q : Matrix Int n (snfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  have hP : P * ((snfData A).left * A) = smithBasis A := smithBasis_mul_form A
  have hQ : Q * smithBasis A = (snfData A).left * A := form_mul_smithBasis A
  have hleft : (snfData A).leftInv * (snfData A).left = Matrix.identity n :=
    mul_eq_one_comm (snfData_left_inv A)
  have hrecover : (snfData A).leftInv * ((snfData A).left * A) = A := by
    rw [← Matrix.mul_assoc, hleft, Matrix.identity_mul]
  constructor
  · intro hv
    exact memLattice_of_mul_eq
      (show (snfData A).left * A = (snfData A).left * A from rfl)
      (memLattice_of_mul_eq hP hv)
  · intro hv
    exact memLattice_of_mul_eq hQ (memLattice_of_mul_eq hrecover hv)

/-- Solving against Smith data is equivalent to solving the transformed
diagonal system. -/
theorem solvable_iff_diagonal {A : Matrix Int n m} {S : SmithData n m}
    (hS : IsSNF A S) {b : Vector Int m} :
    (∃ x, vecMul x A = b) ↔
      ∃ z, vecMul z (diagMatrix S.diag n m) = vecMul b S.right := by
  constructor
  · rintro ⟨x, hx⟩
    have hleft : S.leftInv * S.left = Matrix.identity n :=
      mul_eq_one_comm hS.left_inv
    refine ⟨vecMul x S.leftInv, ?_⟩
    rw [← hS.mul_eq]
    calc
      vecMul (vecMul x S.leftInv) (S.left * A * S.right) =
          vecMul x (S.leftInv * (S.left * A * S.right)) :=
        vecMul_mul x S.leftInv (S.left * A * S.right)
      _ = vecMul x (A * S.right) := by
        congr 1
        simp only [← Matrix.mul_assoc, hleft, Matrix.identity_mul]
      _ = vecMul (vecMul x A) S.right := (vecMul_mul x A S.right).symm
      _ = vecMul b S.right := by rw [hx]
  · rintro ⟨z, hz⟩
    refine ⟨vecMul z S.left, ?_⟩
    have hz' := congrArg (fun v => vecMul v S.rightInv) hz
    rw [← hS.mul_eq] at hz'
    simpa only [vecMul_mul, Matrix.mul_assoc, hS.right_inv,
      Matrix.mul_identity, vecMul_identity] using hz'

private theorem vecMul_diagMatrix (d : Vector Int r) (z : Vector Int n)
    (hrn : r ≤ n) (j : Fin m) :
    (vecMul z (diagMatrix d n m))[j] =
      if h : j.val < r then
        d[(⟨j.val, h⟩ : Fin r)] * z[(⟨j.val, Nat.lt_of_lt_of_le h hrn⟩ : Fin n)]
      else 0 := by
  change (z * diagMatrix d n m)[j] = _
  rw [getElem_vecMul]
  unfold Vector.dotProduct
  by_cases hj : j.val < r
  · rw [dif_pos hj]
    let target : Fin n := ⟨j.val, Nat.lt_of_lt_of_le hj hrn⟩
    calc
      (List.finRange n).foldl
          (fun acc i => acc + (Matrix.col (diagMatrix d n m) j)[i] * z[i]) 0 =
          (List.finRange n).foldl (fun acc i => acc +
            if i = target then d[(⟨j.val, hj⟩ : Fin r)] * z[target] else 0) 0 := by
        apply List.foldl_add_congr
        intro i _hi
        rw [Matrix.getElem_col, Matrix.getElem_diagMatrix]
        by_cases hit : i = target
        · subst i
          rw [dif_pos ⟨rfl, hj⟩, if_pos rfl]
        · rw [if_neg hit]
          split
          next hentry =>
            exfalso
            apply hit
            apply Fin.ext
            exact hentry.1
          next _ => rw [Int.zero_mul]
      _ = d[(⟨j.val, hj⟩ : Fin r)] * z[target] := by
        rw [List.foldl_add_single (List.finRange n) 0 target
          (fun _ => d[(⟨j.val, hj⟩ : Fin r)] * z[target])
          (List.mem_finRange target) (List.nodup_finRange n)]
        omega
  · rw [dif_neg hj]
    calc
      (List.finRange n).foldl
          (fun acc i => acc + (Matrix.col (diagMatrix d n m) j)[i] * z[i]) 0 =
          (List.finRange n).foldl (fun acc _ => acc + 0) 0 := by
        apply List.foldl_add_congr
        intro i _hi
        rw [Matrix.getElem_col, Matrix.getElem_diagMatrix]
        split
        next hentry => exact False.elim (hj (hentry.1 ▸ hentry.2))
        next _ => rw [Int.zero_mul]
      _ = 0 := List.foldl_add_zero _ _

/-- Smith solvability is coordinatewise divisibility on the nonzero diagonal,
together with vanishing of every trailing transformed coordinate. -/
theorem solvable_iff_dvd {A : Matrix Int n m} {S : SmithData n m}
    (hS : IsSNF A S) (b : Vector Int m) :
    (∃ x, vecMul x A = b) ↔
      (∀ i : Fin S.rank,
          S.diag[i] ∣ (vecMul b S.right)[
            (⟨i.val, Nat.lt_of_lt_of_le i.isLt hS.rank_le_m⟩ : Fin m)]) ∧
      (∀ j : Fin m, S.rank ≤ j.val → (vecMul b S.right)[j] = 0) := by
  rw [solvable_iff_diagonal hS]
  let transformed := vecMul b S.right
  constructor
  · rintro ⟨z, hz⟩
    constructor
    · intro i
      let row : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS.rank_le_n⟩
      let col : Fin m := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS.rank_le_m⟩
      have heq := congrArg (fun v : Vector Int m => v.get col) hz
      change (vecMul z (diagMatrix S.diag n m))[col] = transformed[col] at heq
      rw [vecMul_diagMatrix S.diag z hS.rank_le_n col, dif_pos i.isLt] at heq
      exact ⟨z[row], by simpa [row, col, transformed, Int.mul_comm] using heq.symm⟩
    · intro j hj
      have heq := congrArg (fun v : Vector Int m => v.get j) hz
      change (vecMul z (diagMatrix S.diag n m))[j] = transformed[j] at heq
      rw [vecMul_diagMatrix S.diag z hS.rank_le_n j, dif_neg (by omega)] at heq
      exact heq.symm
  · rintro ⟨hdvd, hzero⟩
    let z : Vector Int n := Vector.ofFn fun row =>
      if hrow : row.val < S.rank then
        let col : Fin m := ⟨row.val, Nat.lt_of_lt_of_le hrow hS.rank_le_m⟩
        HexArith.Int.exactDiv transformed[col]
          S.diag[(⟨row.val, hrow⟩ : Fin S.rank)]
      else 0
    refine ⟨z, ?_⟩
    apply Vector.ext
    intro j hj
    let col : Fin m := ⟨j, hj⟩
    change (vecMul z (diagMatrix S.diag n m))[col] = transformed[col]
    rw [vecMul_diagMatrix S.diag z hS.rank_le_n col]
    split
    next hcol =>
      let i : Fin S.rank := ⟨col.val, hcol⟩
      let row : Fin n := ⟨col.val, Nat.lt_of_lt_of_le hcol hS.rank_le_n⟩
      have hd := hdvd i
      have hquot : HexArith.Int.exactDiv transformed[col] S.diag[i] * S.diag[i] =
          transformed[col] := by
        simpa only [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hd
      change S.diag[i] * z.get row = transformed[col]
      have hzget : z.get row = HexArith.Int.exactDiv transformed[col] S.diag[i] := by
        change z[row.val] = HexArith.Int.exactDiv transformed[col] S.diag[i]
        simp only [z, Vector.getElem_ofFn]
        rw [dif_pos hcol]
      rw [hzget]
      rw [Int.mul_comm]
      exact hquot
    next hcol =>
      simpa only [transformed] using (hzero col (by omega)).symm

private theorem vector_foldl_toList (v : Vector R n) (f : α → R → α) (a : α) :
    v.foldl f a = v.toList.foldl f a := by
  rw [Vector.foldl_toList]

private theorem positive_foldl (v : Vector Int n) (h : ∀ i : Fin n, 0 < v[i]) :
    0 < v.foldl (· * ·) 1 := by
  rw [vector_foldl_toList]
  have hall : ∀ x ∈ v.toList, 0 < x := by
    intro x hx
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx
    have hn : i < n := by simpa using hi
    have hv := h (⟨i, hn⟩ : Fin n)
    rw [Vector.getElem_toList] at hget
    have hget' : v[(⟨i, hn⟩ : Fin n)] = x := by simpa using hget
    rw [hget'] at hv
    exact hv
  have go : ∀ (xs : List Int) (acc : Int), 0 < acc →
      (∀ x ∈ xs, 0 < x) → 0 < xs.foldl (· * ·) acc := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro acc hacc hxs
        rw [List.foldl_cons]
        apply ih (acc * x) (Int.mul_pos hacc (hxs x (by simp)))
        intro y hy
        exact hxs y (List.mem_cons_of_mem x hy)
  exact go v.toList 1 (by omega) hall

private theorem det_natAbs_eq_one (U W : Matrix Int n n)
    (h : U * W = Matrix.identity n) : (det U).natAbs = 1 := by
  have hdet := congrArg det h
  rw [det_mul, det_identity] at hdet
  have habs := congrArg Int.natAbs hdet
  rw [Int.natAbs_mul, Int.natAbs_one] at habs
  exact Nat.dvd_one.mp ⟨(det W).natAbs, habs.symm⟩

/-- For a full-rank square matrix, the product of the invariant factors is
the absolute determinant. -/
theorem prod_invariantFactors (A : Matrix Int n n) (h : snfRank A = n) :
    (invariantFactors A).foldl (· * ·) 1 = Int.ofNat ((det A).natAbs) := by
  let S := snfData A
  have hS : IsSNF A S := snfData_isSNF A
  have hrank : S.rank = n := by rw [← snfRank_eq_data]; exact h
  have hupper : ∀ i j : Fin n, j.val < i.val →
      (diagMatrix S.diag n n)[i][j] = 0 := by
    intro i j hji
    exact diagMatrix_apply_of_ne S.diag i j (by omega)
  have hdetDiag := det_upperTriangular_eq_foldl_diag (diagMatrix S.diag n n) hupper
  have hdiagFold : det (diagMatrix S.diag n n) = S.diag.foldl (· * ·) 1 := by
    rw [hdetDiag, vector_foldl_toList]
    rw [← List.foldl_map]
    apply congrArg (fun xs : List Int => xs.foldl (· * ·) 1)
    apply List.ext_getElem
    · simp [hrank]
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_finRange, Vector.getElem_toList]
      rw [Matrix.getElem_diagMatrix]
      simp [show i < n by simpa using hi, hrank]
  have hdet := congrArg det hS.mul_eq
  rw [det_mul, det_mul, hdiagFold] at hdet
  have hleft := det_natAbs_eq_one S.left S.leftInv hS.left_inv
  have hright := det_natAbs_eq_one S.right S.rightInv hS.right_inv
  have habs := congrArg Int.natAbs hdet
  rw [Int.natAbs_mul, Int.natAbs_mul, hleft, hright,
    Nat.one_mul, Nat.mul_one] at habs
  have hpos : 0 < S.diag.foldl (· * ·) 1 := positive_foldl S.diag hS.diag_pos
  have hvalue : S.diag.foldl (· * ·) 1 = Int.ofNat ((det A).natAbs) := by
    calc
      S.diag.foldl (· * ·) 1 = Int.ofNat (S.diag.foldl (· * ·) 1).natAbs :=
        (Int.ofNat_natAbs_of_nonneg (Int.le_of_lt hpos)).symm
      _ = Int.ofNat (det A).natAbs := congrArg Int.ofNat habs.symm
  have hsame := Smith.run_same (Smith.formAccumulator n n)
    (Smith.transformAccumulator n n) A
  change (Smith.run (Smith.formAccumulator n n) A).diagVector.foldl (· * ·) 1 = _
  rw [vector_foldl_toList]
  change (Smith.run (Smith.formAccumulator n n) A).diag.foldl (· * ·) 1 = _
  rw [hsame.diag]
  simpa [S, snfData, Smith.Result.diagVector, vector_foldl_toList] using hvalue

private def pivotPrefix (D : RowEchelonData Int n m) (k : Nat) (hk : k ≤ D.rank) :
    Vector (Fin m) k :=
  Vector.ofFn fun i => D.pivotCols.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

@[simp] private theorem pivotPrefix_get {D : RowEchelonData Int n m}
    {k : Nat} {hk : k ≤ D.rank} (i : Fin k) :
    (pivotPrefix D k hk).get i =
      D.pivotCols.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  simp only [pivotPrefix, Vector.get_ofFn]

@[simp] private theorem pivotPrefix_getElem {D : RowEchelonData Int n m}
    {k : Nat} {hk : k ≤ D.rank} (i : Nat) (hi : i < k) :
    (pivotPrefix D k hk)[i] =
      D.pivotCols[i]'(Nat.lt_of_lt_of_le hi hk) := by
  change (pivotPrefix D k hk).get ⟨i, hi⟩ =
    D.pivotCols.get ⟨i, Nat.lt_of_lt_of_le hi hk⟩
  exact pivotPrefix_get ⟨i, hi⟩

private theorem pivotPrefix_mem {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D) (k : Nat) (hk : k ≤ D.rank) :
    pivotPrefix D k hk ∈ selectedColumnTuples k m := by
  rw [mem_selectedColumnTuples_iff]
  intro i j hij
  change (pivotPrefix D k hk).get i < (pivotPrefix D k hk).get j
  rw [pivotPrefix_get, pivotPrefix_get]
  exact h.toIsEchelonForm.pivotCols_sorted _ _ hij

private theorem finFoldl_pos (f : Fin k → Int) (h : ∀ i, 0 < f i) :
    0 < Fin.foldl k (fun acc i => acc * f i) 1 := by
  rw [Fin.foldl_eq_finRange_foldl]
  have go : ∀ (xs : List (Fin k)) (acc : Int), 0 < acc →
      0 < xs.foldl (fun total i => total * f i) acc := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
        intro acc hacc
        rw [List.foldl_cons]
        exact ih (acc * f i) (Int.mul_pos hacc (h i))
  exact go (List.finRange k) 1 (by omega)

private theorem IsHNF.detDivisor_ne_zero {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D) (k : Nat) (hk : k ≤ D.rank) :
    detDivisor D.echelon k ≠ 0 := by
  let rows := firstColumns k n (Nat.le_trans hk h.toIsEchelonForm.rank_le_n)
  let cols := pivotPrefix D k hk
  let minor := selectedSubmatrix D.echelon rows cols
  have hupper : ∀ i j : Fin k, j.val < i.val → minor[i][j] = 0 := by
    intro i j hji
    dsimp only [minor]
    rw [getElem_selectedSubmatrix]
    have hrow : rows[i] =
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_trans hk h.toIsEchelonForm.rank_le_n)⟩ := by
      simp only [rows, getElem_firstColumns]
    have hcol : cols[j] =
        D.pivotCols.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ := by
      simp only [cols]
      change (pivotPrefix D k hk).get j = _
      exact pivotPrefix_get j
    rw [← Matrix.getElem_pair_eq_nested, hrow, hcol,
      Matrix.getElem_pair_eq_nested]
    exact h.toIsEchelonForm.below_pivot_zero
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt
        (Nat.le_trans hk h.toIsEchelonForm.rank_le_n)⟩ hji
  have hdiag : ∀ i : Fin k, 0 < minor[i][i] := by
    intro i
    dsimp only [minor]
    rw [getElem_selectedSubmatrix]
    have hrow : rows[i] =
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_trans hk h.toIsEchelonForm.rank_le_n)⟩ := by
      simp only [rows, getElem_firstColumns]
    have hcol : cols[i] =
        D.pivotCols.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
      simp only [cols]
      change (pivotPrefix D k hk).get i = _
      exact pivotPrefix_get i
    rw [← Matrix.getElem_pair_eq_nested, hrow, hcol,
      Matrix.getElem_pair_eq_nested]
    exact h.pivot_pos ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hminor : 0 < det minor := by
    rw [det_upperTriangular_eq_finFoldl_diag minor hupper]
    exact finFoldl_pos (fun i => minor[i][i]) hdiag
  have hdvd := detDivisor_dvd_minor D.echelon k rows cols
    (firstColumns_mem_selectedColumnTuples k n
      (Nat.le_trans hk h.toIsEchelonForm.rank_le_n))
    (pivotPrefix_mem h k hk)
  intro hzero
  rw [hzero] at hdvd
  have habsZero : (det minor).natAbs = 0 := Nat.zero_dvd.mp hdvd
  exact Int.natAbs_ne_zero.mpr (Int.ne_of_gt hminor) habsZero

private theorem IsHNF.detDivisor_succ_eq_zero {A : Matrix Int n m}
    {D : RowEchelonData Int n m} (h : IsHNF A D) :
    detDivisor D.echelon (D.rank + 1) = 0 := by
  apply detDivisor_eq_zero
  intro rows hrows cols _hcols
  let last : Fin (D.rank + 1) := Fin.last D.rank
  have hindex : D.rank ≤ rows[last].val := index_le_of_strictlyIncreasing rows
    ((mem_selectedColumnTuples_iff rows).mp hrows) last
  have hrowZero := h.toIsEchelonForm.zero_row rows[last] hindex
  have hminorRow : (selectedSubmatrix D.echelon rows cols)[last] = 0 := by
    apply Vector.ext
    intro j hj
    let col : Fin (D.rank + 1) := ⟨j, hj⟩
    have hz := congrArg (fun v : Vector Int m => v[cols[col]]) hrowZero
    change (selectedSubmatrix D.echelon rows cols)[last][col] =
      (0 : Vector Int (D.rank + 1))[col]
    rw [getElem_selectedSubmatrix]
    calc
      D.echelon[rows[last]][cols[col]] = (0 : Vector Int m)[cols[col]] := hz
      _ = 0 := Vector.getElem_zero _ _
      _ = (0 : Vector Int (D.rank + 1))[col] := (Vector.getElem_zero _ _).symm
  exact det_eq_zero_of_row_zero (selectedSubmatrix D.echelon rows cols) last hminorRow

private theorem hnf_detDivisor_eq (A : Matrix Int n m) (k : Nat) :
    detDivisor (hnfData A).echelon k = detDivisor A k := by
  have hH := hnfData_isHNF A
  rcases hH.toIsEchelonForm.transform_right_inv with ⟨W, hW⟩
  rw [← hH.toIsEchelonForm.transform_mul]
  exact detDivisor_mul_left_eq (hnfData A).transform W hW A k

/-- Smith rank agrees with the executable Hermite rank. -/
theorem IsSNF.rank_eq_hnfRank {A : Matrix Int n m} {S : SmithData n m}
    (hS : IsSNF A S) : S.rank = hnfRank A := by
  let D := hnfData A
  have hH : IsHNF A D := hnfData_isHNF A
  have hrank : hnfRank A = D.rank := hnfRank_eq A
  rw [hrank]
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hgt
    let k := D.rank + 1
    have hsmith := hS.detDivisor_eq k
    rw [if_pos (by simp [k]; omega)] at hsmith
    have hzero := hH.detDivisor_succ_eq_zero
    rw [hnf_detDivisor_eq A k, hsmith] at hzero
    have hpos : 0 < (S.diag.take k).foldl (· * ·) 1 := by
      rw [foldl_take_eq_finFoldl S.diag k (by simp [k]; omega)]
      apply finFoldl_pos
      intro i
      exact hS.diag_pos ⟨i.val, by simp [k] at i ⊢; omega⟩
    exact Int.natAbs_ne_zero.mpr (Int.ne_of_gt hpos) hzero
  · apply Nat.le_of_not_gt
    intro hgt
    let k := S.rank + 1
    have hsmith := hS.detDivisor_eq k
    rw [if_neg (by simp [k])] at hsmith
    have hnonzero := hH.detDivisor_ne_zero k (by simp [k]; omega)
    rw [hnf_detDivisor_eq A k, hsmith] at hnonzero
    exact hnonzero rfl

/-- The executable Smith and Hermite paths report the same rank. -/
theorem snfRank_eq_hnfRank (A : Matrix Int n m) : snfRank A = hnfRank A := by
  rw [snfRank_eq_data]
  exact (snfData_isSNF A).rank_eq_hnfRank

private theorem strictMonoFin_le (f : Fin n → Fin n)
    (hf : ∀ i j, i < j → f i < f j) (i : Fin n) : i.val ≤ (f i).val := by
  have aux : ∀ k (hk : k < n), k ≤ (f ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hstep := hf (⟨k, hk'⟩ : Fin n) (⟨k + 1, hk⟩ : Fin n)
        (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
      have hprev := ih hk'
      change k ≤ (f ⟨k, hk'⟩).val at hprev
      change k + 1 ≤ (f ⟨k + 1, hk⟩).val
      omega
  exact aux i.val i.isLt

private theorem strictMonoFin_eq (f : Fin n → Fin n)
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
  have hlower := strictMonoFin_le f hf i
  have hupper := strictMonoFin_le g hg (rev i)
  simp only [g, hrev, rev] at hupper
  apply Fin.ext
  omega

private theorem fullSelection_get {v : Vector (Fin n) n}
    (hv : v ∈ selectedColumnTuples n n) (i : Fin n) : v.get i = i := by
  let f : Fin n → Fin n := fun j => v.get j
  exact strictMonoFin_eq f
    ((mem_selectedColumnTuples_iff v).mp hv) i

private theorem foldl_natAbs_mul (xs : List Int) (a : Int) :
    (xs.foldl (· * ·) a).natAbs =
      (xs.map Int.natAbs).foldl (· * ·) a.natAbs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, Int.natAbs_mul]

private theorem latticeIndex_eq_detDivisor (A : Matrix Int n m) :
    latticeIndex A = detDivisor A m := by
  by_cases hfull : hnfRank A = m
  · let D := hnfData A
    have hH : IsHNF A D := hnfData_isHNF A
    have hrank : D.rank = m := by rw [← hnfRank_eq A]; exact hfull
    have hmn : m ≤ n := by rw [← hrank]; exact hH.toIsEchelonForm.rank_le_n
    let rows₀ := firstColumns m n hmn
    let cols₀ := firstColumns m m (Nat.le_refl m)
    let B := selectedSubmatrix D.echelon rows₀ cols₀
    let f : Fin m → Fin m := fun i => D.pivotCols.get (Fin.cast hrank.symm i)
    have hf : ∀ i j, i < j → f i < f j := by
      intro i j hij
      exact hH.toIsEchelonForm.pivotCols_sorted
        (Fin.cast hrank.symm i) (Fin.cast hrank.symm j) hij
    have hfid : ∀ i, f i = i := strictMonoFin_eq f hf
    have hupper : ∀ i j : Fin m, j.val < i.val → B[i][j] = 0 := by
      intro i j hji
      simp only [B, getElem_selectedSubmatrix, rows₀, cols₀,
        getElem_firstColumns]
      let q : Fin D.rank := Fin.cast hrank.symm j
      have hz := hH.toIsEchelonForm.below_pivot_zero q
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩ hji
      have hcol : D.pivotCols.get q = j := hfid j
      rw [← Matrix.getElem_pair_eq_nested] at hz ⊢
      rw [hcol] at hz
      exact hz
    have hdiag : ∀ i : Fin m, 0 < B[i][i] := by
      intro i
      simp only [B, getElem_selectedSubmatrix, rows₀, cols₀,
        getElem_firstColumns]
      let q : Fin D.rank := Fin.cast hrank.symm i
      have hp := hH.pivot_pos q
      have hcol : D.pivotCols.get q = i := hfid i
      let v : Vector Int m := D.echelon[q.val]'(Nat.lt_of_lt_of_le q.isLt
        hH.toIsEchelonForm.rank_le_n)
      change 0 < v.get (D.pivotCols.get q) at hp
      have hentry : v.get (D.pivotCols.get q) = v.get i := congrArg v.get hcol
      rw [hentry] at hp
      change 0 < (D.echelon[i.val]'(Nat.lt_of_lt_of_le i.isLt hmn)).get i
      simpa only [v, q, Fin.cast, Fin.getElem_fin] using hp
    have hdet : det B = Fin.foldl m (fun acc i => acc * B[i][i]) 1 :=
      det_upperTriangular_eq_finFoldl_diag B hupper
    have hdetPos : 0 < det B := by
      rw [hdet]
      exact finFoldl_pos (fun i => B[i][i]) hdiag
    have hdivD : detDivisor D.echelon m = (det B).natAbs := by
      apply Nat.dvd_antisymm
      · exact detDivisor_dvd_minor D.echelon m rows₀ cols₀
          (firstColumns_mem_selectedColumnTuples m n hmn)
          (firstColumns_mem_selectedColumnTuples m m (Nat.le_refl m))
      · apply dvd_detDivisor
        intro rows hrows cols hcols
        have hcols : ∀ i : Fin m, cols[i] = i := by
          intro i
          change cols.get i = i
          exact fullSelection_get hcols i
        by_cases hall : ∀ i : Fin m, (rows.get i).val < m
        · let rowMap : Fin m → Fin m := fun i => ⟨(rows.get i).val, hall i⟩
          have hrowMono : ∀ i j, i < j → rowMap i < rowMap j := by
            intro i j hij
            exact ((mem_selectedColumnTuples_iff rows).mp hrows) i j hij
          have hrows : ∀ i : Fin m, rows[i] =
              (⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩ : Fin n) := by
            intro i
            change rows.get i = _
            apply Fin.ext
            have hi := strictMonoFin_eq rowMap hrowMono i
            simpa only [rowMap] using congrArg Fin.val hi
          have hminor : selectedSubmatrix D.echelon rows cols = B := by
            dsimp only [B]
            apply Matrix.ext_getElem
            intro i j
            rw [getElem_selectedSubmatrix, getElem_selectedSubmatrix]
            rw [← Matrix.getElem_pair_eq_nested, ← Matrix.getElem_pair_eq_nested,
              hrows i, hcols j]
            simp only [rows₀, cols₀, getElem_firstColumns]
          rw [hminor]
          exact Nat.dvd_refl _
        · obtain ⟨i, hi⟩ := Classical.not_forall.mp hall
          have hi : m ≤ (rows.get i).val := by omega
          have hzero := hH.toIsEchelonForm.zero_row (rows.get i) (by
            rw [hrank]
            exact hi)
          have hminorRow : (selectedSubmatrix D.echelon rows cols)[i] = 0 := by
            apply Vector.ext
            intro j hj
            let col : Fin m := ⟨j, hj⟩
            have hz := congrArg (fun v : Vector Int m => v[cols[col]]) hzero
            change (selectedSubmatrix D.echelon rows cols)[i][col] =
              (0 : Vector Int m)[col]
            rw [getElem_selectedSubmatrix]
            calc
              D.echelon[rows[i]][cols[col]] = (0 : Vector Int m)[cols[col]] := hz
              _ = 0 := Vector.getElem_zero _ _
              _ = (0 : Vector Int m)[col] := (Vector.getElem_zero _ _).symm
          rw [det_eq_zero_of_row_zero _ i hminorRow, Int.natAbs_zero]
          exact Nat.dvd_zero _
    have hpivList : (pivots A).toList =
        List.ofFn (fun i : Fin m => B[i][i].natAbs) := by
      apply List.ext_getElem
      · simp [hfull]
      · intro k hkA hkB
        have hk : k < m := by simpa using hkB
        let i : Fin m := ⟨k, hk⟩
        rw [Vector.getElem_toList, List.getElem_ofFn]
        unfold pivots
        rw [Vector.getElem_ofFn]
        let rs := Hermite.checkedRun (Hermite.formAccumulator n) A
        let rt := Hermite.checkedRun (Hermite.transformAccumulator n) A
        have hm : rs.matrix = rt.matrix :=
          Hermite.checkedRun_matrix_agree (Hermite.formAccumulator n)
            (Hermite.transformAccumulator n) A
        have hp : rs.pivots = rt.pivots :=
          Hermite.checkedRun_pivots_agree (Hermite.formAccumulator n)
            (Hermite.transformAccumulator n) A
        have hkR : k < hnfRank A := by rw [hfull]; exact hk
        let is : Fin rs.pivots.length := ⟨k, by simpa [rs, hnfRank] using hkR⟩
        let it : Fin rt.pivots.length :=
          Fin.cast (congrArg List.length hp) is
        have hrow : Fin.castLE
            (Hermite.checkedRun_rank_le (Hermite.formAccumulator n) A)
            (⟨k, hkR⟩ : Fin (hnfRank A)) =
              (⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩ : Fin n) := Fin.ext rfl
        have hit : it = Fin.cast hrank.symm i := Fin.ext rfl
        have hcol : D.pivotCols.get (Fin.cast hrank.symm i) = i := hfid i
        have hcolS : rs.pivotVector.get is = i := by
          rw [Hermite.Result.pivotVector_get]
          calc
            rs.pivots.get is = rt.pivots.get it := List.get_of_eq hp is
            _ = rt.pivotVector.get it := (Hermite.Result.pivotVector_get rt it).symm
            _ = D.pivotCols.get (Fin.cast hrank.symm i) := by
              rw [hit]
              simp [D, rt, hnfData]
            _ = i := hcol
        change rs.matrix[(Fin.castLE
          (Hermite.checkedRun_rank_le (Hermite.formAccumulator n) A)
          (⟨k, hkR⟩ : Fin (hnfRank A)),
          rs.pivotVector.get is)].natAbs = B[i][i].natAbs
        rw [hrow, hcolS, hm]
        simp only [B, getElem_selectedSubmatrix, rows₀, cols₀,
          getElem_firstColumns, Matrix.getElem_pair_eq_nested]
        simp [D, rt, hnfData]
    have hpiv : (pivots A).foldl (· * ·) 1 = (det B).natAbs := by
      rw [vector_foldl_toList, hpivList, hdet]
      rw [Fin.foldl_eq_finRange_foldl]
      have hlist : (List.ofFn fun i : Fin m => B[i][i].natAbs) =
          (List.finRange m).map (fun i => B[i][i].natAbs) := by
        rw [List.finRange, List.map_ofFn]
        rfl
      rw [hlist, List.foldl_map]
      have habs := foldl_natAbs_mul
        ((List.finRange m).map fun i => B[i][i]) 1
      simpa [List.foldl_map, Function.comp_def] using habs.symm
    rw [latticeIndex_eq_prod_pivots A hfull, hpiv, ← hdivD,
      hnf_detDivisor_eq A m]
  · have hrank : snfRank A ≠ m := by
      rw [snfRank_eq_hnfRank]
      exact hfull
    have hS := (snfData_isSNF A).detDivisor_eq m
    have hnotle : ¬ m ≤ (snfData A).rank := by
      rw [← snfRank_eq_data]
      intro hm
      apply hrank
      exact Nat.le_antisymm (snfRank_le_m A) hm
    rw [if_neg hnotle] at hS
    rw [latticeIndex, if_neg hfull, hS]

/-- The lattice index is the product of the Smith invariant factors in full
column rank, and zero otherwise. -/
theorem latticeIndex_eq_invariantFactors (A : Matrix Int n m) :
    latticeIndex A =
      if snfRank A = m then
        (invariantFactors A).foldl (fun acc d => acc * d.natAbs) 1
      else 0 := by
  rw [latticeIndex_eq_detDivisor]
  have hS := (snfData_isSNF A).detDivisor_eq m
  by_cases hfull : snfRank A = m
  · rw [if_pos hfull]
    have hrank : (snfData A).rank = m := by
      rw [← snfRank_eq_data]
      exact hfull
    rw [if_pos (by omega)] at hS
    have htake : ((snfData A).diag.take m).toList =
        (snfData A).diag.toList := by
      simp only [Vector.toList_take]
      apply List.take_of_length_le
      simp [hrank]
    have hdiag : (snfData A).diag.toList =
        (invariantFactors A).toList := by
      have heq := congrArg Vector.toList (invariantFactors_cast_eq_data A)
      simpa only [Vector.toList_cast] using heq.symm
    have hprod : ((snfData A).diag.take m).foldl (· * ·) 1 =
        (invariantFactors A).foldl (· * ·) 1 := by
      rw [vector_foldl_toList, vector_foldl_toList, htake, hdiag]
    rw [hS, hprod]
    have habs := foldl_natAbs_mul (invariantFactors A).toList 1
    rw [vector_foldl_toList (v := invariantFactors A) (f := (· * ·))]
    rw [vector_foldl_toList (v := invariantFactors A)
      (f := fun acc d => acc * d.natAbs)]
    simpa only [List.foldl_map, Int.natAbs_one] using habs
  · rw [if_neg hfull]
    have hnotle : ¬ m ≤ (snfData A).rank := by
      rw [← snfRank_eq_data]
      intro hm
      apply hfull
      exact Nat.le_antisymm (snfRank_le_m A) hm
    rw [if_neg hnotle] at hS
    exact hS

end Hex.Matrix
