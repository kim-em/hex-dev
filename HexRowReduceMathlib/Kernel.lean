/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRowReduce.Kernel
public import HexRowReduceMathlib.InverseSolve
public import HexMatrixMathlib.Rational
public import HexMatrixMathlib.ListProducts

public section

namespace HexMatrixMathlib

attribute [local instance 2000] Field.toGrindField

open Hex.Matrix.Lists

/-- A certified inverse or a certified nonzero right-kernel vector. -/
inductive InverseResult {F : Type u} [Field F] {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) where
  | invertible (value : Matrix (Fin n) (Fin n) F)
      (right_inv : A * value = 1) (left_inv : value * A = 1)
      (inv_eq : A⁻¹ = value)
  | singular (kernel : Fin n → F) (nonzero : kernel ≠ 0)
      (annihilates : A.mulVec kernel = 0) (det_eq : A.det = 0)
      (inv_eq : A⁻¹ = 0)

/-- The complete affine solution space or a certified separating row. -/
inductive SolveResult {F : Type u} [Field F] {n m : Nat}
    (A : Matrix (Fin n) (Fin m) F) (b : Fin n → F) where
  | consistent (value : Fin m → F) (nullity : Nat)
      (basis : Matrix (Fin m) (Fin nullity) F)
      (solution : A.mulVec value = b)
      (complete : ∀ x : Fin m → F, A.mulVec x = b ↔
        ∃! c : Fin nullity → F, x = value + basis.mulVec c)
  | inconsistent (separator : Fin n → F)
      (annihilates : Matrix.vecMul separator A = 0)
      (separates : dotProduct separator b ≠ 0)
      (impossible : ¬ ∃ x : Fin m → F, A.mulVec x = b)

/-- The full mathematical statement certified by either solve outcome. -/
@[expose] def SolveResult.statement {F : Type u} [Field F] {n m : Nat}
    {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} : SolveResult A b → Prop
  | .consistent value _ basis _ _ =>
      ∀ x, A.mulVec x = b ↔ ∃! c, x = value + basis.mulVec c
  | .inconsistent _ _ _ _ => ¬ ∃ x, A.mulVec x = b

/-- Extract completeness or impossibility while retaining the literal result data. -/
theorem SolveResult.spec {F : Type u} [Field F] {n m : Nat}
    {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} (r : SolveResult A b) : r.statement := by
  cases r with
  | consistent _ _ _ _ h => exact h
  | inconsistent _ _ _ h => exact h

namespace FieldCertificate

/-- Decoding belongs to soundness, outside the arithmetic reduction path. -/
@[expose] def matrix (n m : Nat) (a : ScaledRows) : Matrix (Fin n) (Fin m) ℚ :=
  ofLists n m (decodeRows a)

@[expose] def vector (n : Nat) (a : Scaled) : Fin n → ℚ :=
  vecOfList n (decodeList a)

theorem matrix_apply (n m : Nat) (a : ScaledRows) (i : Fin n) (j : Fin m) :
    matrix n m a i j = (get a.nums i j : ℚ) / a.denom := by
  simp only [matrix, ofLists_apply, decodeRows_getD, decodeScalar, Hex.Matrix.Lists.get, entry_eq_getD]

theorem vector_apply (n : Nat) (a : Scaled) (i : Fin n) :
    vector n a i = ((entry 0 a.nums i : Int) : ℚ) / a.denom := by
  simp only [vector, vecOfList_apply, decodeList_getD, decodeScalar, entry_eq_getD]

theorem matrix_valid {n m : Nat} {a : ScaledRows} (h : Hex.Matrix.FieldLists.matrix n m a = true) :
    0 < a.denom ∧ shape n m a.nums = true := by
  simpa [Hex.Matrix.FieldLists.matrix] using h

theorem vector_valid {n : Nat} {a : Scaled} (h : Hex.Matrix.FieldLists.vector n a = true) :
    0 < a.denom ∧ a.nums.length = n := by
  simpa [Hex.Matrix.FieldLists.vector] using h

theorem mul_apply {n k m : Nat} {a b : ScaledRows}
    (ha : shape n k a.nums = true) (i : Fin n) (j : Fin m) :
    (matrix n k a * matrix k m b) i j =
      (dot (entry [] a.nums i) (column j b.nums) : ℚ) /
        ((a.denom : ℚ) * b.denom) := by
  have hd := dot_eq_sum (entry [] a.nums i) (column j b.nums)
  rw [row_length ha i] at hd
  simp only [Matrix.mul_apply, matrix_apply, div_mul_div_comm, ← Finset.sum_div]
  congr 1
  rw [hd]
  simp only [Int.cast_sum, Int.cast_mul, Hex.Matrix.Lists.get, entry_eq_getD, ListProducts.column_getD]

/-- Arbitrary accepted scaled products transport to Mathlib multiplication. -/
theorem product {n k m : Nat} {a b c : ScaledRows}
    (ha : Hex.Matrix.FieldLists.matrix n k a = true) (hb : Hex.Matrix.FieldLists.matrix k m b = true)
    (hc : Hex.Matrix.FieldLists.matrix n m c = true) (h : Hex.Matrix.FieldLists.product n m a b c = true) :
    matrix n k a * matrix k m b = matrix n m c := by
  obtain ⟨ha0, ha⟩ := matrix_valid ha
  obtain ⟨hb0, _⟩ := matrix_valid hb
  obtain ⟨hc0, _⟩ := matrix_valid hc
  have ha' : (a.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha0)
  have hb' : (b.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb0)
  have hc' : (c.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc0)
  ext i j
  rw [mul_apply ha, matrix_apply]
  apply (div_eq_div_iff (mul_ne_zero ha' hb') hc').mpr
  have hh := of_decide_eq_true
    ((all_iff _ m).mp ((all_iff _ n).mp h i i.isLt) j j.isLt)
  exact_mod_cast hh

/-- The scaled identity check supplies the matrix inverse equation. -/
theorem inverse {n : Nat} {a b : ScaledRows}
    (ha : Hex.Matrix.FieldLists.matrix n n a = true) (hb : Hex.Matrix.FieldLists.matrix n n b = true)
    (h : Hex.Matrix.FieldLists.inverse n a b = true) : matrix n n a * matrix n n b = 1 := by
  obtain ⟨ha0, ha⟩ := matrix_valid ha
  obtain ⟨hb0, _⟩ := matrix_valid hb
  have hab : (a.denom : ℚ) * b.denom ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt ha0))
      (by exact_mod_cast (Nat.ne_of_gt hb0))
  ext i j
  rw [mul_apply ha, div_eq_iff hab]
  have hh := of_decide_eq_true
    ((all_iff _ n).mp ((all_iff _ n).mp h i i.isLt) j j.isLt)
  by_cases hij : i = j
  · subst j
    simp [identity] at hh
    simp only [Matrix.one_apply_eq, one_mul]
    exact_mod_cast hh
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [identity, hv] at hh
    simp [Matrix.one_apply_ne hij, hh]

/-- A two-sided inverse determines Mathlib's nonsingular inverse. -/
theorem inv_eq {F : Type u} [Field F] {n : Nat}
    {A B : Matrix (Fin n) (Fin n) F} (hr : A * B = 1) (hl : B * A = 1) : A⁻¹ = B := by
  have hu := Matrix.isUnit_det_of_right_inverse hr
  calc
    A⁻¹ = (B * A) * A⁻¹ := by rw [hl, one_mul]
    _ = B := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]

theorem mulVec_apply {n m : Nat} {a : ScaledRows} {v : Scaled}
    (ha : shape n m a.nums = true) (i : Fin n) :
    (matrix n m a).mulVec (vector m v) i =
      (dot (entry [] a.nums i) v.nums : ℚ) / ((a.denom : ℚ) * v.denom) := by
  have hd := dot_eq_sum (entry [] a.nums i) v.nums
  rw [row_length ha i] at hd
  simp only [Matrix.mulVec, dotProduct, matrix_apply, vector_apply,
    div_mul_div_comm, ← Finset.sum_div]
  congr 1
  rw [hd]
  simp only [Int.cast_sum, Int.cast_mul, Hex.Matrix.Lists.get, entry_eq_getD]

theorem kernel {n m : Nat} {a : ScaledRows} {v : Scaled}
    (ha : Hex.Matrix.FieldLists.matrix n m a = true)
    (h : Hex.Matrix.FieldLists.kernel n a v = true) :
    (matrix n m a).mulVec (vector m v) = 0 := by
  funext i
  rw [mulVec_apply (matrix_valid ha).2]
  have hi := of_decide_eq_true ((all_iff _ n).mp h i i.isLt)
  simp [hi]

theorem nonzero {n k : Nat} {v : Scaled}
    (hv : Hex.Matrix.FieldLists.vector n v = true) (hk : k < n)
    (h : entry 0 v.nums k ≠ 0) : vector n v ≠ 0 := by
  intro hz
  have he := congrFun hz ⟨k, hk⟩
  rw [vector_apply] at he
  have hd : (v.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (vector_valid hv).1)
  have hn : ((entry 0 v.nums k : Int) : ℚ) = 0 := (div_eq_zero_iff).mp he |>.resolve_right hd
  exact h (by exact_mod_cast hn)

/-- A nonzero kernel vector certifies determinant zero, including the empty boundary. -/
theorem singular {F : Type u} [Field F] {n : Nat}
    {A : Matrix (Fin n) (Fin n) F} {v : Fin n → F}
    (hv : v ≠ 0) (ha : A.mulVec v = 0) : A.det = 0 ∧ A⁻¹ = 0 := by
  have hd : A.det = 0 := by
    by_contra h
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr h
    have he := congrArg (Matrix.mulVec A⁻¹) ha
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec, Matrix.mulVec_zero] at he
    exact hv he
  exact ⟨hd, Matrix.nonsing_inv_apply_not_isUnit A (by simp [hd])⟩

theorem column_valid {n : Nat} {v : Scaled}
    (h : Hex.Matrix.FieldLists.vector n v = true) :
    Hex.Matrix.FieldLists.matrix n 1 (Hex.Matrix.FieldLists.columnBlock v) = true := by
  obtain ⟨hd, hn⟩ := vector_valid h
  simp [Hex.Matrix.FieldLists.matrix, Hex.Matrix.FieldLists.columnBlock, shape, hd, hn]

theorem column_apply (n : Nat) (v : Scaled) (i : Fin n) :
    matrix n 1 (Hex.Matrix.FieldLists.columnBlock v) i 0 = vector n v i := by
  simp only [matrix_apply, vector_apply, Hex.Matrix.FieldLists.columnBlock,
    Hex.Matrix.Lists.get, entry_eq_getD]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v.nums[i.val]? <;> simp

/-- A residual identity accepts every solution, regardless of the producer's choice. -/
theorem residual {n m : Nat} {a : ScaledRows} {b x : Scaled}
    (ha : Hex.Matrix.FieldLists.matrix n m a = true)
    (hb : Hex.Matrix.FieldLists.vector n b = true)
    (hx : Hex.Matrix.FieldLists.vector m x = true)
    (h : Hex.Matrix.FieldLists.product n 1 a
      (Hex.Matrix.FieldLists.columnBlock x) (Hex.Matrix.FieldLists.columnBlock b) = true) :
    (matrix n m a).mulVec (vector m x) = vector n b := by
  have hp := product ha (column_valid hx) (column_valid hb) h
  funext i
  have he := congrArg (fun M : Matrix (Fin n) (Fin 1) ℚ => M i 0) hp
  simpa only [Matrix.mul_apply, column_apply, Matrix.mulVec, dotProduct] using he

theorem dot_apply {n : Nat} {a b : Scaled} (ha : a.nums.length = n) :
    dotProduct (vector n a) (vector n b) =
      (dot a.nums b.nums : ℚ) / ((a.denom : ℚ) * b.denom) := by
  have hd := dot_eq_sum a.nums b.nums
  rw [ha] at hd
  simp only [dotProduct, vector_apply, div_mul_div_comm, ← Finset.sum_div]
  congr 1
  rw [hd]
  simp only [Int.cast_sum, Int.cast_mul, entry_eq_getD]

theorem vecMul_apply {n m : Nat} {a : ScaledRows} {y : Scaled}
    (hy : y.nums.length = n) (j : Fin m) :
    Matrix.vecMul (vector n y) (matrix n m a) j =
      (dot y.nums (column j a.nums) : ℚ) / ((y.denom : ℚ) * a.denom) := by
  have hd := dot_eq_sum y.nums (column j a.nums)
  rw [hy] at hd
  simp only [Matrix.vecMul, dotProduct, matrix_apply, vector_apply,
    div_mul_div_comm, ← Finset.sum_div]
  congr 1
  rw [hd]
  simp only [Int.cast_sum, Int.cast_mul, Hex.Matrix.Lists.get, entry_eq_getD,
    ListProducts.column_getD]

/-- A separating row rules out every solution by associativity. -/
theorem impossible {F : Type u} [Field F] {n m : Nat}
    {A : Matrix (Fin n) (Fin m) F} {b y : Fin n → F}
    (hy : Matrix.vecMul y A = 0) (hb : dotProduct y b ≠ 0) :
    ¬ ∃ x, A.mulVec x = b := by
  rintro ⟨x, hx⟩
  apply hb
  rw [← hx, Matrix.dotProduct_mulVec, hy, zero_dotProduct]

/-- Transport the two independently checked separator conditions. -/
theorem separator {n m : Nat} {a : ScaledRows} {b y : Scaled}
    (hb : Hex.Matrix.FieldLists.vector n b = true)
    (hy : Hex.Matrix.FieldLists.vector n y = true)
    (h : Hex.Matrix.FieldLists.separator m a b y = true) :
    Matrix.vecMul (vector n y) (matrix n m a) = 0 ∧
      dotProduct (vector n y) (vector n b) ≠ 0 := by
  simp only [Hex.Matrix.FieldLists.separator, Bool.and_eq_true] at h
  obtain ⟨hz, hd⟩ := h
  constructor
  · funext j
    rw [vecMul_apply (vector_valid hy).2]
    have hj := of_decide_eq_true ((all_iff _ m).mp hz j j.isLt)
    simp [hj]
  · rw [dot_apply (vector_valid hy).2]
    apply div_ne_zero
    · exact_mod_cast of_decide_eq_true hd
    · exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt (vector_valid hy).1))
        (by exact_mod_cast (Nat.ne_of_gt (vector_valid hb).1))

/-- The proof-facing reduced-row-echelon conditions extracted from a list check. -/
structure EchelonChecks (n m : Nat) (d : Hex.Matrix.SolveBasis) : Prop where
  rows : d.rank ≤ n
  cols : d.rank ≤ m
  length : d.pivots.length = d.rank
  bounds : ∀ i : Fin d.rank, entry m d.pivots i < m
  sorted : ∀ i j : Fin d.rank, i < j → entry m d.pivots i < entry m d.pivots j
  pivot : ∀ (i : Fin d.rank) (j : Fin n),
    get d.reduced.nums j (entry m d.pivots i) =
      if i.val = j.val then (d.reduced.denom : Int) else 0
  trailing : ∀ (i : Fin n) (j : Fin m), d.rank ≤ i.val → get d.reduced.nums i j = 0

theorem echelon_spec {n m : Nat} {d : Hex.Matrix.SolveBasis}
    (h : Hex.Matrix.FieldLists.echelon n m d = true) : EchelonChecks n m d := by
  simp only [Hex.Matrix.FieldLists.echelon, Bool.and_eq_true, Nat.ble_eq,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hn, hm⟩, hl⟩, hp⟩, hz⟩ := h
  have hp' (i : Fin d.rank) := (all_iff _ d.rank).mp hp i i.isLt
  simp only [Bool.and_eq_true, Nat.blt_eq] at hp'
  refine ⟨hn, hm, hl, fun i => (hp' i).1.1.1, ?_, ?_, ?_⟩
  · intro i j hij
    exact of_decide_eq_true ((all_iff _ j).mp (hp' j).1.1.2 i hij)
  · intro i j
    have he := of_decide_eq_true ((all_iff _ n).mp (hp' i).1.2 j j.isLt)
    simpa using he
  · intro i j hi
    have he := (all_iff _ n).mp hz i i.isLt
    simp only [Bool.or_eq_true, Nat.blt_eq] at he
    rcases he with hlt | he
    · omega
    · exact of_decide_eq_true ((all_iff _ m).mp he j j.isLt)

/-- Reconstruct executable data only in the soundness layer. -/
noncomputable abbrev echelonData {n m : Nat} (d : Hex.Matrix.SolveBasis)
    (h : EchelonChecks n m d) : Hex.Matrix.RowEchelonData ℚ n m where
  rank := d.rank
  echelon := matrixEquiv.symm (matrix n m d.reduced)
  transform := matrixEquiv.symm (matrix n n d.transform)
  pivotCols := Vector.ofFn fun i => ⟨entry m d.pivots i, h.bounds i⟩

theorem echelonData_pivot {n m : Nat} (d : Hex.Matrix.SolveBasis)
    (h : EchelonChecks n m d) (i : Fin d.rank) :
    ((echelonData d h).pivotCols.get i).val = entry m d.pivots i := by
  simp [echelonData, Vector.get, Fin.cast]

/-- Checked row operations and canonical columns give an arbitrary `IsRowReduced` witness. -/
theorem rowReduced {n m : Nat} {a : ScaledRows} {d : Hex.Matrix.SolveBasis}
    (ha : Hex.Matrix.FieldLists.matrix n m a = true)
    (hr : Hex.Matrix.FieldLists.matrix n m d.reduced = true)
    (hu : Hex.Matrix.FieldLists.matrix n n d.transform = true)
    (hw : Hex.Matrix.FieldLists.matrix n n d.inverse = true)
    (hprod : Hex.Matrix.FieldLists.product n m d.transform a d.reduced = true)
    (hinv : Hex.Matrix.FieldLists.inverse n d.transform d.inverse = true)
    (h : EchelonChecks n m d) :
    Hex.Matrix.IsRowReduced (matrixEquiv.symm (matrix n m a)) (echelonData d h) := by
  have hi := inverse hu hw hinv
  have hl := mul_eq_one_comm.mp hi
  have hi0 : matrixEquiv (Hex.Matrix.identity (R := ℚ) n) = 1 := by
    ext i j
    rw [matrixEquiv_apply, Hex.Matrix.getElem_identity]
    rfl
  have hd : (d.reduced.denom : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (matrix_valid hr).1)
  have hp (i : Fin d.rank) (j : Fin n) :
      (echelonData d h).echelon[j][(echelonData d h).pivotCols.get i] =
        if i.val = j.val then (1 : ℚ) else 0 := by
    change (matrixEquiv.symm (matrix n m d.reduced))[j.val][((echelonData d h).pivotCols.get i).val] = _
    rw [matrixEquiv_symm_apply]
    rw [matrix_apply, echelonData_pivot, h.pivot]
    split <;> simp_all
  refine {
    transform_mul := ?_
    transform_inv := ?_
    transform_right_inv := ?_
    rank_le_n := h.rows
    rank_le_m := h.cols
    pivotCols_sorted := ?_
    below_pivot_zero := ?_
    zero_row := ?_
    pivot_one := ?_
    above_pivot_zero := ?_ }
  · apply matrixEquiv.injective
    simpa only [matrixEquiv_mul, echelonData, Equiv.apply_symm_apply] using product hu ha hr hprod
  · refine ⟨matrixEquiv.symm (matrix n n d.inverse), matrixEquiv.injective ?_⟩
    simpa only [matrixEquiv_mul, echelonData, Equiv.apply_symm_apply, hi0] using hl
  · refine ⟨matrixEquiv.symm (matrix n n d.inverse), matrixEquiv.injective ?_⟩
    simpa only [matrixEquiv_mul, echelonData, Equiv.apply_symm_apply, hi0] using hi
  · intro i j hij
    change ((echelonData d h).pivotCols.get i).val < ((echelonData d h).pivotCols.get j).val
    rw [echelonData_pivot, echelonData_pivot]
    exact h.sorted i j hij
  · intro i j hij
    exact (hp i j).trans (ite_eq_right (by omega))
  · intro i hi
    apply Vector.ext
    intro j hj
    change (matrixEquiv.symm (matrix n m d.reduced))[i.val][j] = (0 : Vector ℚ m)[j]
    rw [matrixEquiv_symm_apply _ i ⟨j, hj⟩, Vector.getElem_zero]
    rw [matrix_apply, h.trailing i ⟨j, hj⟩ hi]
    simp
  · intro i
    exact (hp i ⟨i, Nat.lt_of_lt_of_le i.isLt h.rows⟩).trans (ite_eq_left rfl)
  · intro i j hij
    exact (hp i j).trans (ite_eq_right (by omega))

theorem pivots_list {n m : Nat} {d : Hex.Matrix.SolveBasis} (h : EchelonChecks n m d) :
    (echelonData d h).pivotCols.toList.map Fin.val = d.pivots := by
  apply List.ext_getElem
  · simp [h.length]
  · intro i hi hj
    simp only [List.getElem_map, Vector.getElem_toList]
    have hi' : i < d.rank := by simpa using hi
    simp only [Vector.getElem_ofFn, entry_eq_getD, getD_eq_getElem' _ _ _ hj]

theorem free_list {n m : Nat} {a : ScaledRows} {d : Hex.Matrix.SolveBasis}
    (h : EchelonChecks n m d)
    (E : Hex.Matrix.IsRowReduced (matrixEquiv.symm (matrix n m a)) (echelonData d h)) :
    E.toIsEchelonForm.freeColsList.map Fin.val =
      (List.range m).filter (fun j => !d.pivots.contains j) := by
  have hrange : (List.finRange m).map Fin.val = List.range m := by
    apply List.ext_getElem <;> simp
  rw [← hrange, List.filter_map]
  unfold Hex.Matrix.IsEchelonForm.freeColsList
  congr 1
  apply List.filter_congr
  intro j _
  have hm : j ∈ (echelonData d h).pivotCols.toList ↔ j.val ∈ d.pivots := by
    rw [← pivots_list h, List.mem_map]
    constructor
    · intro hj
      exact ⟨j, hj, rfl⟩
    · rintro ⟨k, hk, he⟩
      exact (Fin.ext he) ▸ hk
  simp [hm]

theorem free_entry {n m : Nat} {a : ScaledRows} {d : Hex.Matrix.SolveBasis}
    (h : EchelonChecks n m d)
    (E : Hex.Matrix.IsRowReduced (matrixEquiv.symm (matrix n m a)) (echelonData d h))
    (hf : d.free = (List.range m).filter (fun j => !d.pivots.contains j))
    (k : Fin (m - d.rank)) :
    (E.toIsEchelonForm.freeCols.get k).val = entry m d.free k := by
  have he : E.toIsEchelonForm.freeColsList.map Fin.val = d.free := (free_list h E).trans hf.symm
  have hk : k.val < E.toIsEchelonForm.freeColsList.length := by
    simp [Hex.Matrix.IsEchelonForm.freeColsList_length]
  have hget := congrArg (fun l : List Nat => l.getD k m) he
  rw [getD_eq_getElem' _ _ _ (by simpa using hk), List.getElem_map] at hget
  rw [entry_eq_getD, ← hget]
  simp [Hex.Matrix.IsEchelonForm.freeCols, Vector.get, List.getElem_toArray, Fin.cast]

/-- The checked basis is exactly the computed free-column basis of the reconstructed RREF. -/
theorem basis_eq {n m : Nat} {a : ScaledRows} {d : Hex.Matrix.SolveBasis}
    (h : EchelonChecks n m d)
    (E : Hex.Matrix.IsRowReduced (matrixEquiv.symm (matrix n m a)) (echelonData d h))
    (hr : Hex.Matrix.FieldLists.matrix n m d.reduced = true)
    (hb : Hex.Matrix.FieldLists.matrix m d.nullity d.basis = true)
    (hf : Hex.Matrix.FieldLists.freeData m d = true) :
    matrix m (m - d.rank) d.basis = matrixEquiv E.nullspaceMatrix := by
  simp only [Hex.Matrix.FieldLists.freeData, Bool.and_eq_true, decide_eq_true_eq,
    Nat.beq_eq] at hf
  obtain ⟨⟨⟨hfree, hnull⟩, _⟩, hdata⟩ := hf
  have hk (k : Fin (m - d.rank)) := (all_iff _ d.nullity).mp hdata k
    (by rw [hnull]; exact k.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  have hr0 : (d.reduced.denom : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (matrix_valid hr).1)
  have hb0 : (d.basis.denom : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (matrix_valid hb).1)
  ext i k
  rcases E.toIsEchelonForm.colPartition i with ⟨j, hj⟩ | ⟨l, hl⟩
  · rw [← hj, matrixEquiv_apply, Hex.Matrix.IsRowReduced.nullspaceMatrix_pivot]
    change matrix m (m - d.rank) d.basis ((echelonData d h).pivotCols.get j) k =
      -(matrixEquiv.symm (matrix n m d.reduced))[(E.toIsEchelonForm.pivotRow j).val][(E.toIsEchelonForm.freeCols.get k).val]
    rw [matrixEquiv_symm_apply, matrix_apply, matrix_apply, echelonData_pivot,
      free_entry h E hfree]
    change (get d.basis.nums (entry m d.pivots j) k : ℚ) / d.basis.denom =
      -((get d.reduced.nums j (entry m d.free k) : ℚ) / d.reduced.denom)
    rw [← neg_div]
    apply (div_eq_div_iff hb0 hr0).mpr
    have he := of_decide_eq_true ((all_iff _ d.rank).mp (hk k).2 j j.isLt)
    have he' : (get d.basis.nums (entry m d.pivots j) k : ℚ) * d.reduced.denom =
        -((get d.reduced.nums j (entry m d.free k) : ℚ) * d.basis.denom) := by
      exact_mod_cast he
    simpa only [neg_mul] using he'
  · rw [← hl, matrix_apply, free_entry h E hfree, matrixEquiv_apply]
    have he := of_decide_eq_true ((all_iff _ d.nullity).mp (hk k).1.2 l
      (by rw [hnull]; exact l.isLt))
    by_cases hkl : k = l
    · subst l
      rw [Hex.Matrix.IsRowReduced.nullspaceMatrix_free]
      have he' : get d.basis.nums (entry m d.free k) k = d.basis.denom := by simpa using he
      rw [he']
      simpa using div_self hb0
    · rw [Hex.Matrix.IsRowReduced.nullspaceMatrix_free_ne E hkl]
      have he' : get d.basis.nums (entry m d.free l) k = 0 := by
        simpa [show k.val ≠ l.val from fun hh => hkl (Fin.ext hh)] using he
      simp [he']

/-- Span completeness and independence give unique affine coordinates. -/
theorem affine {F : Type u} [Field F] {n m : Nat}
    {M : Hex.Matrix F n m} {D : Hex.Matrix.RowEchelonData F n m}
    (E : Hex.Matrix.IsRowReduced M D) {b : Fin n → F} {value : Fin m → F}
    (hvalue : (matrixEquiv M).mulVec value = b) :
    ∀ x, (matrixEquiv M).mulVec x = b ↔
      ∃! c, x = value + (matrixEquiv E.nullspaceMatrix).mulVec c := by
  let B := matrixEquiv E.nullspaceMatrix
  have hcol : B.col = fun k => vectorEquiv (E.nullspace.get k) := by
    funext k i
    simp only [B, Matrix.col_apply, matrixEquiv_apply, vectorEquiv_apply,
      Hex.Matrix.IsRowReduced.nullspace_get, Hex.Matrix.getElem_col]
  have hspan : LinearMap.range B.mulVecLin = LinearMap.ker (matrixEquiv M).mulVecLin := by
    rw [Matrix.range_mulVecLin, hcol, nullspace_span_eq_ker E]
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff.mpr (by rw [hcol]; exact nullspace_linearIndependent E)
  intro x
  constructor
  · intro hx
    have hz : x - value ∈ LinearMap.ker (matrixEquiv M).mulVecLin := by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub,
        hx, hvalue, sub_self]
    rw [← hspan] at hz
    obtain ⟨c, hc⟩ := hz
    change B.mulVec c = x - value at hc
    have he : x = value + B.mulVec c := by rw [hc]; abel
    refine ⟨c, he, ?_⟩
    intro d hd
    exact hinj (add_left_cancel (hd.symm.trans he))
  · rintro ⟨c, hc, _⟩
    have hz : B.mulVec c ∈ LinearMap.ker (matrixEquiv M).mulVecLin := by
      rw [← hspan]
      exact ⟨c, rfl⟩
    change (matrixEquiv M).mulVec (B.mulVec c) = 0 at hz
    rw [hc, Matrix.mulVec_add, hvalue, hz, add_zero]

/-- The complete check transports the quoted particular solution and full affine basis. -/
theorem complete {n m : Nat} {a : ScaledRows} {b : Scaled} {d : Hex.Matrix.SolveBasis}
    (ha : Hex.Matrix.FieldLists.matrix n m a = true)
    (hb : Hex.Matrix.FieldLists.vector n b = true)
    (hr : Hex.Matrix.FieldLists.matrix n m d.reduced = true)
    (hu : Hex.Matrix.FieldLists.matrix n n d.transform = true)
    (hw : Hex.Matrix.FieldLists.matrix n n d.inverse = true)
    (hv : Hex.Matrix.FieldLists.vector m d.value = true)
    (hk : Hex.Matrix.FieldLists.matrix m d.nullity d.basis = true)
    (hprod : Hex.Matrix.FieldLists.product n m d.transform a d.reduced = true)
    (hinv : Hex.Matrix.FieldLists.inverse n d.transform d.inverse = true)
    (he : Hex.Matrix.FieldLists.echelon n m d = true)
    (hsol : Hex.Matrix.FieldLists.product n 1 a (Hex.Matrix.FieldLists.columnBlock d.value)
      (Hex.Matrix.FieldLists.columnBlock b) = true)
    (hfree : Hex.Matrix.FieldLists.freeData m d = true) :
    (matrix n m a).mulVec (vector m d.value) = vector n b ∧
      ∀ x, (matrix n m a).mulVec x = vector n b ↔
        ∃! c : Fin d.nullity → ℚ, x = vector m d.value + (matrix m d.nullity d.basis).mulVec c := by
  have hvalue := residual ha hb hv hsol
  refine ⟨hvalue, ?_⟩
  let checks := echelon_spec he
  let E := rowReduced ha hr hu hw hprod hinv checks
  have hn : d.nullity = m - d.rank := by
    simp only [Hex.Matrix.FieldLists.freeData, Bool.and_eq_true, Nat.beq_eq] at hfree
    exact hfree.1.1.2
  rw [hn, basis_eq checks E hr hk hfree]
  have hs := affine E (by simpa only [Equiv.apply_symm_apply] using hvalue)
  simpa only [Equiv.apply_symm_apply] using hs

end FieldCertificate

/-- All proof fields for one inverse outcome, bundled for a single kernel check. -/
@[expose] def InverseFacts {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    Hex.Matrix.InverseWitness → Prop
  | .invertible _ b => A * FieldCertificate.matrix n n b = 1 ∧
      FieldCertificate.matrix n n b * A = 1 ∧ A⁻¹ = FieldCertificate.matrix n n b
  | .singular _ v _ => FieldCertificate.vector n v ≠ 0 ∧
      A.mulVec (FieldCertificate.vector n v) = 0 ∧ A.det = 0 ∧ A⁻¹ = 0

/-- All proof fields for one solve outcome. -/
@[expose] def SolveFacts {n m : Nat} (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ) :
    Hex.Matrix.SolveWitness → Prop
  | .consistent _ _ d => A.mulVec (FieldCertificate.vector m d.value) = b ∧
      ∀ x, A.mulVec x = b ↔ ∃! c : Fin d.nullity → ℚ,
        x = FieldCertificate.vector m d.value + (FieldCertificate.matrix m d.nullity d.basis).mulVec c
  | .inconsistent _ _ y => Matrix.vecMul (FieldCertificate.vector n y) A = 0 ∧
      dotProduct (FieldCertificate.vector n y) b ≠ 0 ∧ ¬ ∃ x, A.mulVec x = b

/-- Soundness for both inverse certificate alternatives. -/
theorem inverse_facts {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (List Rat))
    (c : Hex.Matrix.InverseWitness) (hA : A = ofLists n n rows)
    (hc : Hex.Matrix.checkInverseList n rows c = true) : InverseFacts A c := by
  cases c with
  | invertible a b =>
    simp only [Hex.Matrix.checkInverseList, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨ha, hs⟩, hb⟩, hr⟩, hl⟩ := hc
    have hrows := scaleRows_sound a.denom rows a.nums (FieldCertificate.matrix_valid ha).1 hs
    have he : A = FieldCertificate.matrix n n a := hA.trans (congrArg (ofLists n n) hrows)
    change A * FieldCertificate.matrix n n b = 1 ∧
      FieldCertificate.matrix n n b * A = 1 ∧ A⁻¹ = FieldCertificate.matrix n n b
    rw [he]
    exact ⟨FieldCertificate.inverse ha hb hr, FieldCertificate.inverse hb ha hl,
      FieldCertificate.inv_eq (FieldCertificate.inverse ha hb hr) (FieldCertificate.inverse hb ha hl)⟩
  | singular a v k =>
    simp only [Hex.Matrix.checkInverseList, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨ha, hs⟩, hv⟩, hk⟩, hn⟩, hz⟩ := hc
    have hrows := scaleRows_sound a.denom rows a.nums (FieldCertificate.matrix_valid ha).1 hs
    have he : A = FieldCertificate.matrix n n a := hA.trans (congrArg (ofLists n n) hrows)
    change FieldCertificate.vector n v ≠ 0 ∧
      A.mulVec (FieldCertificate.vector n v) = 0 ∧ A.det = 0 ∧ A⁻¹ = 0
    rw [he]
    have hnonzero := FieldCertificate.nonzero hv hk hn
    have hkernel := FieldCertificate.kernel ha hz
    have hh := FieldCertificate.singular hnonzero hkernel
    exact ⟨hnonzero, hkernel, hh.1, hh.2⟩

/-- Accepted inverse-product and kernel certificates produce either certified outcome. -/
@[expose] noncomputable def inverse_of_checkList {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (List Rat))
    (c : Hex.Matrix.InverseWitness) (hA : A = ofLists n n rows)
    (hc : Hex.Matrix.checkInverseList n rows c = true) : InverseResult A := by
  cases c with
  | invertible a value =>
    have h := inverse_facts A rows (.invertible a value) hA hc
    exact .invertible (FieldCertificate.matrix n n value) h.1 h.2.1 h.2.2
  | singular a kernel k =>
    have h := inverse_facts A rows (.singular a kernel k) hA hc
    exact .singular (FieldCertificate.vector n kernel) h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Direct residual soundness for literal matrices and vectors. -/
theorem solve_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ) (x : Fin m → ℚ)
    (rows : List (List Rat)) (rhs candidate : List Rat)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hx : x = vecOfList m candidate)
    (hc : Hex.Matrix.checkSolutionList n m rows rhs candidate = true) :
    A.mulVec x = b := by
  simp only [Hex.Matrix.checkSolutionList, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨ha, hs⟩, hb'⟩, ht⟩, hx'⟩, hu⟩, hp⟩ := hc
  have hrows := scaleRows_sound _ _ _ (FieldCertificate.matrix_valid ha).1 hs
  have hrhs := scaleRow_sound _ _ _ (FieldCertificate.vector_valid hb').1 ht
  have hcand := scaleRow_sound _ _ _ (FieldCertificate.vector_valid hx').1 hu
  rw [hA, hb, hx, hrows, hrhs, hcand]
  exact FieldCertificate.residual ha hb' hx' hp

/-- Soundness for both complete solve certificate alternatives. -/
theorem solve_facts {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ)
    (rows : List (List Rat)) (rhs : List Rat) (c : Hex.Matrix.SolveWitness)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hc : Hex.Matrix.checkSolveList n m rows rhs c = true) : SolveFacts A b c := by
  cases c with
  | consistent a v d =>
    simp only [Hex.Matrix.checkSolveList, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hs⟩, hv⟩, ht⟩, hr⟩, hu⟩, hw⟩, hx⟩, hk⟩, hp⟩, hi⟩, he⟩, hsol⟩, hf⟩ := hc
    have hrows := scaleRows_sound _ _ _ (FieldCertificate.matrix_valid ha).1 hs
    have hrhs := scaleRow_sound _ _ _ (FieldCertificate.vector_valid hv).1 ht
    change _ ∧ _
    rw [hA, hb, hrows, hrhs]
    have hh := FieldCertificate.complete ha hv hr hu hw hx hk hp hi he hsol hf
    exact hh
  | inconsistent a v y =>
    simp only [Hex.Matrix.checkSolveList, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨ha, hs⟩, hv⟩, ht⟩, hy⟩, hsep⟩ := hc
    have hrows := scaleRows_sound _ _ _ (FieldCertificate.matrix_valid ha).1 hs
    have hrhs := scaleRow_sound _ _ _ (FieldCertificate.vector_valid hv).1 ht
    change _ ∧ _
    rw [hA, hb, hrows, hrhs]
    have hh := FieldCertificate.separator hv hy hsep
    exact ⟨hh.1, hh.2, FieldCertificate.impossible hh.1 hh.2⟩

/-- Complete positive and negative outcomes from arbitrary accepted list data. -/
@[expose] noncomputable def solveResult_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ)
    (rows : List (List Rat)) (rhs : List Rat) (c : Hex.Matrix.SolveWitness)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hc : Hex.Matrix.checkSolveList n m rows rhs c = true) : SolveResult A b := by
  cases c with
  | consistent a rhs d =>
    have h := solve_facts A b rows _ (.consistent a rhs d) hA hb hc
    exact .consistent (FieldCertificate.vector m d.value) d.nullity
      (FieldCertificate.matrix m d.nullity d.basis) h.1 h.2
  | inconsistent a rhs y =>
    have h := solve_facts A b rows _ (.inconsistent a rhs y) hA hb hc
    exact .inconsistent (FieldCertificate.vector n y) h.1 h.2.1 h.2.2

/-- The inverse matrix, when present. -/
@[expose] def InverseResult.value? {F : Type u} [Field F] {n : Nat}
    {A : Matrix (Fin n) (Fin n) F} : InverseResult A → Option (Matrix (Fin n) (Fin n) F)
  | .invertible value _ _ _ => some value
  | .singular _ _ _ _ _ => none

/-- The nonzero kernel witness in the singular branch. -/
@[expose] def InverseResult.kernel? {F : Type u} [Field F] {n : Nat}
    {A : Matrix (Fin n) (Fin n) F} : InverseResult A → Option (Fin n → F)
  | .invertible _ _ _ _ => none
  | .singular kernel _ _ _ _ => some kernel

/-- Literal nullity, particular solution and basis, when the system is consistent. -/
@[expose] def SolveResult.data? {F : Type u} [Field F] {n m : Nat}
    {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} :
    SolveResult A b → Option (Σ k : Nat, (Fin m → F) × Matrix (Fin m) (Fin k) F)
  | .consistent value k basis _ _ => some ⟨k, value, basis⟩
  | .inconsistent _ _ _ _ => none

/-- The separating row in the inconsistent branch. -/
@[expose] def SolveResult.separator? {F : Type u} [Field F] {n m : Nat}
    {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} : SolveResult A b → Option (Fin n → F)
  | .consistent _ _ _ _ _ => none
  | .inconsistent y _ _ _ => some y

theorem inverse_value {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (rows : List (List Rat)) (a value : ScaledRows) (hA : A = ofLists n n rows)
    (hc : Hex.Matrix.checkInverseList n rows (.invertible a value) = true) :
    (inverse_of_checkList A rows (.invertible a value) hA hc).value? =
      some (FieldCertificate.matrix n n value) := rfl

theorem inverse_kernel {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (rows : List (List Rat)) (a : ScaledRows) (v : Scaled) (k : Nat)
    (hA : A = ofLists n n rows)
    (hc : Hex.Matrix.checkInverseList n rows (.singular a v k) = true) :
    (inverse_of_checkList A rows (.singular a v k) hA hc).kernel? =
      some (FieldCertificate.vector n v) := rfl

theorem solve_data {n m : Nat} (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ)
    (rows : List (List Rat)) (rhs : List Rat) (a : ScaledRows) (v : Scaled) (d : Hex.Matrix.SolveBasis)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hc : Hex.Matrix.checkSolveList n m rows rhs (.consistent a v d) = true) :
    (solveResult_of_checkList A b rows rhs (.consistent a v d) hA hb hc).data? =
      some ⟨d.nullity, FieldCertificate.vector m d.value, FieldCertificate.matrix m d.nullity d.basis⟩ := rfl

theorem solve_separator {n m : Nat} (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ)
    (rows : List (List Rat)) (rhs : List Rat) (a : ScaledRows) (v y : Scaled)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hc : Hex.Matrix.checkSolveList n m rows rhs (.inconsistent a v y) = true) :
    (solveResult_of_checkList A b rows rhs (.inconsistent a v y) hA hb hc).separator? =
      some (FieldCertificate.vector n y) := rfl

namespace FieldCertificate

/-- A literal matrix is identified with its scaled encoding by cross products. -/
theorem identify_matrix {n m : Nat} (A : Matrix (Fin n) (Fin m) ℚ)
    (rows : List (List Rat)) (s : ScaledRows) (hA : A = ofLists n m rows)
    (hd : 0 < s.denom) (hs : scaleRows s.denom rows s.nums = true) :
    A = matrix n m s := by
  rw [hA, scaleRows_sound s.denom rows s.nums hd hs]
  rfl

/-- A literal vector is identified without normalizing decoded fractions. -/
theorem identify_vector {n : Nat} (v : Fin n → ℚ) (xs : List Rat) (s : Scaled)
    (hv : v = vecOfList n xs) (hd : 0 < s.denom) (hs : scaleRow s.denom xs s.nums = true) :
    v = vector n s := by
  rw [hv, scaleRow_sound s.denom xs s.nums hd hs]
  rfl

theorem inverse_literal {n : Nat} {A B : Matrix (Fin n) (Fin n) ℚ} {a s : ScaledRows}
    (h : InverseFacts A (.invertible a s)) (hB : B = matrix n n s) :
    A * B = 1 ∧ B * A = 1 ∧ A⁻¹ = B := by
  rw [hB]
  exact h

theorem singular_literal {n : Nat} {A : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    {a : ScaledRows} {s : Scaled} {k : Nat}
    (h : InverseFacts A (.singular a s k)) (hv : v = vector n s) :
    v ≠ 0 ∧ A.mulVec v = 0 ∧ A.det = 0 ∧ A⁻¹ = 0 := by
  rw [hv]
  exact h

theorem solve_literal {n m : Nat} {A : Matrix (Fin n) (Fin m) ℚ} {b : Fin n → ℚ}
    {a : ScaledRows} {rhs : Scaled} {d : Hex.Matrix.SolveBasis}
    {v : Fin m → ℚ} {B : Matrix (Fin m) (Fin d.nullity) ℚ}
    (h : SolveFacts A b (.consistent a rhs d))
    (hv : v = vector m d.value) (hB : B = matrix m d.nullity d.basis) :
    A.mulVec v = b ∧ ∀ x, A.mulVec x = b ↔ ∃! c, x = v + B.mulVec c := by
  rw [hv, hB]
  exact h

theorem separator_literal {n m : Nat} {A : Matrix (Fin n) (Fin m) ℚ} {b y : Fin n → ℚ}
    {a : ScaledRows} {rhs s : Scaled} (h : SolveFacts A b (.inconsistent a rhs s))
    (hy : y = vector n s) :
    Matrix.vecMul y A = 0 ∧ dotProduct y b ≠ 0 ∧ ¬ ∃ x, A.mulVec x = b := by
  rw [hy]
  exact h

theorem zero_matrix (n m : Nat) :
    matrix n m ⟨1, List.replicate n (List.replicate m 0)⟩ = 0 := by
  ext i j
  simp [matrix_apply, Hex.Matrix.Lists.get, entry_eq_getD, List.getD_eq_getElem?_getD,
    i.isLt, j.isLt]

end FieldCertificate

end HexMatrixMathlib
