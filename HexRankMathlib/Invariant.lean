/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Sound
public import HexRankMathlib.Bordered
public import HexBareissMathlib.Bareiss

public section

/-!
The loop invariant of `rowReduceWith`.

After the columns `0 … t - 1` have been scanned, with `B` the pivot block
(rows in elimination order) and `p = det B`: the pivot rows of the state are
the rows of `adjugate B * P`, every non-pivot row `i` is
`p • A[i, :] - A[i, cols] * (adjugate B * P)`, the denominator is `p`, every
non-pivot row is zero on the scanned columns, and the pivot columns are
strictly increasing among the scanned columns. The pivot step identifies the
new pivot with the determinant of the enlarged block by the
bordered-determinant identity, and verifies the Bareiss update against the
invariant by left-multiplying by the enlarged block and cancelling.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n m : Nat}

namespace RowReduce

/-- `Vector.get` of a push is `Fin.snoc`. -/
theorem get_push {α : Type u} {k : Nat} (v : Vector α k) (a : α) :
    (v.push a).get = Fin.snoc v.get a := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    show (v.push a)[k] = _
    simp [Fin.snoc]
  | cast i =>
    show (v.push a)[i.val] = _
    simp [Fin.snoc, Vector.get]

/-- Membership in the list of a vector is being one of its entries. -/
theorem mem_toList_iff {α : Type u} {k : Nat} (v : Vector α k) (a : α) :
    a ∈ v.toList ↔ ∃ i, v.get i = a := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, by simpa using hi⟩, by simpa [Vector.get] using h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, by simp, by simpa [Vector.get] using h⟩

/-- The pivot block of a state: the selected submatrix at its profile. -/
@[expose]
def block (A : Matrix (Fin n) (Fin m) R) (S : Hex.Matrix.ReducedForm R n m) :
    Matrix (Fin S.profile.rank) (Fin S.profile.rank) R :=
  A.submatrix S.profile.rows.get S.profile.cols.get

/-- The coefficient matrix `adjugate B * P` of a state. -/
@[expose]
def coeff (A : Matrix (Fin n) (Fin m) R) (S : Hex.Matrix.ReducedForm R n m) :
    Matrix (Fin S.profile.rank) (Fin m) R :=
  (block A S).adjugate * A.submatrix S.profile.rows.get id

/-- The loop invariant after `t` columns have been scanned. -/
structure Inv (A : Matrix (Fin n) (Fin m) R) (t : Nat) (S : Hex.Matrix.ReducedForm R n m) :
    Prop where
  /-- The denominator is the determinant of the pivot block. -/
  denom_eq : S.denom = (block A S).det
  /-- The denominator is nonzero. -/
  denom_ne : S.denom ≠ 0
  /-- Pivot row `k` of the state is row `k` of `adjugate B * P`. -/
  pivot_row : ∀ k, matrixEquiv S.matrix (S.profile.rows.get k) = coeff A S k
  /-- Every non-pivot row is `p • A[i, :] - A[i, cols] * (adjugate B * P)`. -/
  other_row : ∀ i, i ∉ S.profile.rows.toList →
    matrixEquiv S.matrix i =
      S.denom • A i - (fun l => A i (S.profile.cols.get l)) ᵥ* coeff A S
  /-- Every non-pivot row is zero on the scanned columns. -/
  cleared : ∀ i, i ∉ S.profile.rows.toList → ∀ j : Fin m, j.val < t →
    matrixEquiv S.matrix i j = 0
  /-- Every pivot column has been scanned. -/
  cols_lt : ∀ k, (S.profile.cols.get k).val < t
  /-- The pivot columns are strictly increasing. -/
  cols_mono : StrictMono S.profile.cols.get

omit [DecidableEq R] in
/-- `B * (adjugate B * P) = det B • P`. -/
theorem block_mul_coeff (A : Matrix (Fin n) (Fin m) R) (S : Hex.Matrix.ReducedForm R n m) :
    block A S * coeff A S = (block A S).det • A.submatrix S.profile.rows.get id := by
  rw [coeff, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]

omit [DecidableEq R] in
/-- Left-cancel a nonsingular square matrix over a domain. -/
theorem mul_left_cancel_of_det_ne_zero [IsDomain R] {k : Nat}
    {B : Matrix (Fin k) (Fin k) R} (hB : B.det ≠ 0) {X Y : Matrix (Fin k) (Fin m) R}
    (h : B * X = B * Y) : X = Y := by
  have h' := congrArg (fun Z => B.adjugate * Z) h
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h'
  ext i j
  exact mul_left_cancel₀ hB (congrFun (congrFun h' i) j)

omit [DecidableEq R] in
/-- The seed satisfies the invariant with no column scanned. -/
theorem inv_initial [Nontrivial R] (A : Hex.Matrix R n m) :
    Inv (matrixEquiv A) 0 (Hex.Matrix.initialForm A) where
  denom_eq := by simp [Hex.Matrix.initialForm, block]
  denom_ne := one_ne_zero
  pivot_row k := k.elim0
  other_row i _ := by
    funext j
    simp only [Hex.Matrix.initialForm, coeff, Matrix.vecMul, dotProduct, Pi.sub_apply, one_smul]
    rw [Finset.sum_eq_zero (fun x _ => Fin.elim0 x), sub_zero]
  cleared _ _ j hj := absurd hj (Nat.not_lt_zero _)
  cols_lt k := k.elim0
  cols_mono a := a.elim0

/-- A skipped column preserves the invariant and extends the scanned range. -/
theorem inv_step_skip {quot : R → R → R} {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) {j : Fin m} (hj : j.val = t)
    (hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j = none) :
    Inv A (t + 1) (Hex.Matrix.reduceStep quot S j) := by
  rw [Hex.Matrix.reduceStep_skip hp]
  have hzero := Hex.Matrix.findPivotRow?_none hp
  refine ⟨hS.denom_eq, hS.denom_ne, hS.pivot_row, hS.other_row, ?_, ?_, hS.cols_mono⟩
  · intro i hi j' hj'
    by_cases hjj : j' = j
    · subst hjj
      rw [matrixEquiv_apply]
      exact hzero i hi
    · exact hS.cleared i hi j' (by
        have : j'.val ≠ j.val := fun h => hjj (Fin.ext h)
        omega)
  · intro k
    exact Nat.lt_succ_of_lt (hS.cols_lt k)

/-- A pivot column preserves the invariant: the new pivot is the determinant
of the enlarged block by the bordered-determinant identity, and the Bareiss
update produces the invariant's values, each division being exact. -/
theorem inv_step_pivot {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) {j : Fin m} (hj : j.val = t) {p : Fin n}
    (hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j = some p) :
    Inv A (t + 1) (Hex.Matrix.reduceStep quot S j) := by
  have := isDomain_of_quot quot hquot h1
  obtain ⟨⟨k, rows, cols⟩, d, M⟩ := S
  obtain ⟨hp_notin, hpivot_ne, -⟩ := Hex.Matrix.findPivotRow?_some hp
  set E := matrixEquiv M with hEdef
  have hE : ∀ x y, E x y = M[x][y] := fun x y => matrixEquiv_apply M x y
  set U : Matrix (Fin k) (Fin m) R :=
    (A.submatrix rows.get cols.get).adjugate * A.submatrix rows.get id with hUdef
  have hd : d = (A.submatrix rows.get cols.get).det := hS.denom_eq
  have hd0 : d ≠ 0 := hS.denom_ne
  have hB0 : (A.submatrix rows.get cols.get).det ≠ 0 := hd ▸ hd0
  have hrow : ∀ (l : Fin k) (j' : Fin m), E (rows.get l) j' = U l j' :=
    fun l j' => congrFun (hS.pivot_row l) j'
  have hother : ∀ i, i ∉ rows.toList → ∀ j',
      E i j' = d * A i j' - ∑ l, A i (cols.get l) * U l j' := by
    intro i hi j'
    exact congrFun (hS.other_row i hi) j'
  have hcleared : ∀ i, i ∉ rows.toList → ∀ j' : Fin m, j'.val < t → E i j' = 0 := hS.cleared
  have hcols_lt : ∀ l, (cols.get l).val < t := hS.cols_lt
  have hcols_mono : StrictMono cols.get := hS.cols_mono
  have hBU : ∀ (l : Fin k) (j' : Fin m),
      ∑ l', A (rows.get l) (cols.get l') * U l' j' = d * A (rows.get l) j' := by
    intro l j'
    have h := congrFun (congrFun (block_mul_coeff A ⟨⟨k, rows, cols⟩, d, M⟩) l) j'
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [block] at h
    rw [← hd] at h
    exact h
  -- the pivot
  have hpivE : E p j = M[p][j] := hE p j
  have hpiv : E p j = d * A p j - ∑ l, A p (cols.get l) * U l j := hother p hp_notin j
  rw [← hpivE] at hpivot_ne
  -- the enlarged block
  set B' : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
    A.submatrix (Fin.snoc rows.get p) (Fin.snoc cols.get j) with hB'def
  set P' : Matrix (Fin (k + 1)) (Fin m) R := A.submatrix (Fin.snoc rows.get p) id with hP'def
  set U' : Matrix (Fin (k + 1)) (Fin m) R := B'.adjugate * P' with hU'def
  have hB'det : B'.det = E p j := by
    rw [hB'def, det_submatrix_snoc A rows.get cols.get p j hB0, hpiv, ← hd]
    simp only [dotProduct, Matrix.mulVec, hUdef, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
    ring
  have hB'0 : B'.det ≠ 0 := hB'det ▸ hpivot_ne
  have hB'U' : B' * U' = E p j • P' := by
    rw [hU'def, ← Matrix.mul_assoc, Matrix.mul_adjugate, hB'det, Matrix.smul_mul, Matrix.one_mul]
  -- the numerators of the update, as a matrix
  set Z : Matrix (Fin (k + 1)) (Fin m) R :=
    Matrix.of (Fin.snoc (fun l => E p j • U l - U l j • E p) (d • E p)) with hZdef
  have hZc : ∀ (l : Fin k) (j' : Fin m),
      Z (Fin.castSucc l) j' = E p j * U l j' - U l j * E p j' := by
    intro l j'
    simp [hZdef, Fin.snoc_castSucc]
  have hZl : ∀ j', Z (Fin.last k) j' = d * E p j' := by
    intro j'
    simp [hZdef, Fin.snoc_last]
  have hB'Z : B' * Z = (d * E p j) • P' := by
    ext r j'
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [hZc, hZl, Matrix.smul_apply, smul_eq_mul, hB'def, hP'def, Matrix.submatrix_apply,
      Fin.snoc_castSucc, Fin.snoc_last, id_eq]
    induction r using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      have hs : ∀ x, ∑ l, A p (cols.get l) * U l x = d * A p x - E p x := fun x => by
        rw [hother p hp_notin x]; ring
      have hsum : ∑ l, A p (cols.get l) * (E p j * U l j' - U l j * E p j') =
          E p j * (∑ l, A p (cols.get l) * U l j') - E p j' * (∑ l, A p (cols.get l) * U l j) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hsum, hs, hs]
      ring
    | cast r =>
      simp only [Fin.snoc_castSucc]
      have hsum : ∑ l, A (rows.get r) (cols.get l) * (E p j * U l j' - U l j * E p j') =
          E p j * (∑ l, A (rows.get r) (cols.get l) * U l j') -
            E p j' * (∑ l, A (rows.get r) (cols.get l) * U l j) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hsum, hBU, hBU]
      ring
  have hZU : Z = d • U' := by
    apply mul_left_cancel_of_det_ne_zero hB'0
    rw [hB'Z, Matrix.mul_smul, hB'U', smul_smul]
  have hU'c : ∀ (l : Fin k) (j' : Fin m),
      d * U' (Fin.castSucc l) j' = E p j * U l j' - U l j * E p j' := by
    intro l j'
    rw [← hZc, hZU]
    simp
  have hU'l : ∀ j', U' (Fin.last k) j' = E p j' := by
    intro j'
    have h := hZl j'
    rw [hZU] at h
    simp only [Matrix.smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ hd0 h
  have hU'cj : ∀ l : Fin k, U' (Fin.castSucc l) j = 0 := by
    intro l
    have h0 : d * U' (Fin.castSucc l) j = 0 := by rw [hU'c]; ring
    exact (mul_eq_zero.mp h0).resolve_left hd0
  -- the new state
  simp only [Hex.Matrix.reduceStep, hp, Hex.Matrix.getElem_pair_eq_nested]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [block, get_push]
    show M[p][j] = B'.det
    rw [hB'det, hpivE]
  · rw [← hpivE]
    exact hpivot_ne
  · intro k'
    funext j'
    simp only [coeff, block, get_push, matrixEquiv_ofFn]
    change _ = U' k' j'
    simp only [← hE]
    induction k' using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, ite_true]
      exact (hU'l j').symm
    | cast l =>
      have hne : rows.get l ≠ p := fun h => hp_notin ((mem_toList_iff rows p).mpr ⟨l, h⟩)
      simp only [Fin.snoc_castSucc, hne, ite_false]
      by_cases hjj : j' = j
      · subst hjj
        simp only [ite_true]
        exact (hU'cj l).symm
      · simp only [hjj, ite_false]
        rw [hrow, hrow, show E p j * U l j' - U l j * E p j' = U' (Fin.castSucc l) j' * d by
          rw [← hU'c, mul_comm]]
        exact hquot _ _ hd0
  · intro i hi
    funext j'
    simp only [Vector.toList_push, List.mem_append, List.mem_singleton, not_or] at hi
    obtain ⟨hi_rows, hi_p⟩ := hi
    simp only [coeff, block, get_push, matrixEquiv_ofFn, ← hE]
    change _ = (E p j • A i - (fun l => A i ((Fin.snoc cols.get j : Fin (k + 1) → Fin m) l)) ᵥ* U') j'
    have hR : (E p j • A i - (fun l => A i ((Fin.snoc cols.get j : Fin (k + 1) → Fin m) l)) ᵥ* U') j' =
        E p j * A i j' -
          (∑ l, A i (cols.get l) * U' (Fin.castSucc l) j' + A i j * U' (Fin.last k) j') := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
        Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    rw [hR]
    have hkey : d * (E p j * A i j' -
        (∑ l, A i (cols.get l) * U' (Fin.castSucc l) j' + A i j * U' (Fin.last k) j')) =
        E p j * E i j' - E i j * E p j' := by
      have hdS : d * ∑ l, A i (cols.get l) * U' (Fin.castSucc l) j' =
          E p j * (∑ l, A i (cols.get l) * U l j') - E p j' * (∑ l, A i (cols.get l) * U l j) := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show d * (A i (cols.get l) * U' (Fin.castSucc l) j') =
          A i (cols.get l) * (d * U' (Fin.castSucc l) j') by ring, hU'c]
        ring
      have hi1 := hother i hi_rows j'
      have hi2 := hother i hi_rows j
      have hl := hU'l j'
      rw [mul_sub, mul_add, hdS, hl, hi1, hi2]
      ring
    simp only [hi_p, ite_false]
    by_cases hjj : j' = j
    · subst hjj
      simp only [ite_true]
      have h0 : d * (E p j' * A i j' -
          (∑ l, A i (cols.get l) * U' (Fin.castSucc l) j' + A i j' * U' (Fin.last k) j')) = 0 := by
        rw [hkey]; ring
      exact ((mul_eq_zero.mp h0).resolve_left hd0).symm
    · simp only [hjj, ite_false]
      rw [show E p j * E i j' - E i j * E p j' = (E p j * A i j' -
          (∑ l, A i (cols.get l) * U' (Fin.castSucc l) j' + A i j * U' (Fin.last k) j')) * d by
        rw [← hkey, mul_comm]]
      exact hquot _ _ hd0
  · intro i hi j' hj'
    simp only [Vector.toList_push, List.mem_append, List.mem_singleton, not_or] at hi
    obtain ⟨hi_rows, hi_p⟩ := hi
    simp only [matrixEquiv_ofFn, hi_p, ite_false]
    by_cases hjj : j' = j
    · simp only [hjj, ite_true]
    · simp only [hjj, ite_false]
      have hlt : j'.val < t := by
        have : j'.val ≠ j.val := fun h => hjj (Fin.ext h)
        omega
      simp only [← hE]
      rw [hcleared i hi_rows j' hlt, hcleared p hp_notin j' hlt,
        show E p j * 0 - E i j * 0 = 0 * d by ring]
      exact hquot _ _ hd0
  · intro k'
    simp only [get_push]
    induction k' using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; omega
    | cast l => simp only [Fin.snoc_castSucc]; exact Nat.lt_succ_of_lt (hcols_lt l)
  · simp only [get_push]
    intro a b hab
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.mpr (Fin.le_last b))
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [Fin.lt_def]
        have := hcols_lt a
        omega
      | cast b =>
        simp only [Fin.snoc_castSucc]
        exact hcols_mono (Fin.castSucc_lt_castSucc_iff.mp hab)

/-- One column, pivot or skip, preserves the invariant. -/
theorem inv_step {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) {A : Matrix (Fin n) (Fin m) R} {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S) {j : Fin m} (hj : j.val = t) :
    Inv A (t + 1) (Hex.Matrix.reduceStep quot S j) := by
  cases hp : Hex.Matrix.findPivotRow? S.matrix S.profile.rows.toList j with
  | none => exact inv_step_skip hS hj hp
  | some p => exact inv_step_pivot hquot h1 hS hj hp

/-- Scanning a run of consecutive columns preserves the invariant. -/
theorem inv_foldl {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) {A : Matrix (Fin n) (Fin m) R} (l : List (Fin m)) {t : Nat}
    {S : Hex.Matrix.ReducedForm R n m} (hS : Inv A t S)
    (hl : ∀ (i : Nat) (hi : i < l.length), (l[i]).val = t + i) :
    Inv A (t + l.length) (l.foldl (Hex.Matrix.reduceStep quot) S) := by
  induction l generalizing t S with
  | nil => simpa using hS
  | cons j l ih =>
    rw [List.foldl_cons]
    have hj : j.val = t := by
      have h := hl 0 (Nat.succ_pos _)
      rw [List.getElem_cons_zero] at h
      simpa using h
    have hS' := inv_step hquot h1 hS hj
    have := ih hS' (fun i hi => by
      have h := hl (i + 1) (by simpa using hi)
      rw [List.getElem_cons_succ] at h
      rw [h]
      omega)
    rw [List.length_cons, show t + (l.length + 1) = t + 1 + l.length by omega]
    exact this

/-- The invariant after the whole pass. -/
theorem inv_rowReduceWith {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    Inv (matrixEquiv A) m (Hex.Matrix.rowReduceWith quot A) := by
  have : Nontrivial R := ⟨⟨1, 0, h1⟩⟩
  have h := inv_foldl hquot h1 (List.finRange m) (inv_initial A)
    (fun i hi => by simp [List.getElem_finRange])
  simpa [Hex.Matrix.rowReduceWith] using h

/-- The state after the first `t` columns. -/
@[expose]
def reduceCols (quot : R → R → R) (A : Hex.Matrix R n m) (t : Nat) :
    Hex.Matrix.ReducedForm R n m :=
  ((List.finRange m).take t).foldl (Hex.Matrix.reduceStep quot) (Hex.Matrix.initialForm A)

/-- The invariant after the first `t` columns. -/
theorem inv_reduceCols {quot : R → R → R} (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) {t : Nat} (ht : t ≤ m) :
    Inv (matrixEquiv A) t (reduceCols quot A t) := by
  have : Nontrivial R := ⟨⟨1, 0, h1⟩⟩
  have h := inv_foldl hquot h1 ((List.finRange m).take t) (inv_initial A)
    (fun i hi => by simp [List.getElem_take, List.getElem_finRange])
  simpa [reduceCols, List.length_take, ht] using h

/-- The whole pass is the state after all `m` columns. -/
theorem rowReduceWith_eq_reduceCols (quot : R → R → R) (A : Hex.Matrix R n m) :
    Hex.Matrix.rowReduceWith quot A = reduceCols quot A m := by
  simp [reduceCols, Hex.Matrix.rowReduceWith, List.take_of_length_le]

/-- Scanning one more column steps the state. -/
theorem reduceCols_succ (quot : R → R → R) (A : Hex.Matrix R n m) {t : Nat} (ht : t < m) :
    reduceCols quot A (t + 1) = Hex.Matrix.reduceStep quot (reduceCols quot A t) ⟨t, ht⟩ := by
  have hget : (List.finRange m)[t]? = some ⟨t, ht⟩ := by
    rw [List.getElem?_eq_getElem (by simpa using ht)]
    simp [List.getElem_finRange]
  simp [reduceCols, List.take_add_one, hget, List.foldl_append]

end RowReduce

end HexMatrixMathlib
