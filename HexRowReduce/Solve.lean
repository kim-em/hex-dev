/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.Api
import all HexMatrix.MatrixAlgebra
import all HexRowReduce.Nullspace

public section

namespace Hex.Matrix

universe u
variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}

namespace IsRowReduced

variable {A : Matrix F n m} {D : RowEchelonData F n m}

/-- Place the pivot-row coordinates in their pivot columns, with zero free
coordinates. Columns beyond the rank are zero. -/
private def pivotLift (D : RowEchelonData F n m) : Matrix F m n :=
  Matrix.ofFn fun i j =>
    if h : j.val < D.rank then
      if D.pivotCols.get ⟨j.val, h⟩ = i then 1 else 0
    else 0

omit [DecidableEq F] in
private theorem pivotLift_col (j : Fin n) (hj : j.val < D.rank) :
    col (pivotLift D) j = Vector.unit F (D.pivotCols.get ⟨j.val, hj⟩) := by
  ext i hi
  change (col (pivotLift D) j)[(⟨i, hi⟩ : Fin m)] = _
  rw [getElem_col]
  simp only [pivotLift, getElem_ofFn, dite_eq_left hj]
  simp only [Vector.unit, Vector.getElem_ofFn]
  rfl

omit [DecidableEq F] in
private theorem pivotLift_col_zero (j : Fin n) (hj : ¬j.val < D.rank) :
    col (pivotLift D) j = 0 := by
  ext i hi
  change (col (pivotLift D) j)[(⟨i, hi⟩ : Fin m)] = _
  rw [getElem_col]
  simp only [pivotLift, getElem_ofFn, dite_eq_right hj]
  simp

omit [DecidableEq F] in
private theorem echelon_pivot (E : IsRowReduced A D) (i : Fin n) (j : Fin D.rank) :
    D.echelon[i][D.pivotCols.get j] = if i.val = j.val then 1 else 0 := by
  by_cases hij : i.val = j.val
  · rw [ite_eq_left hij]
    have hi : i = E.toIsEchelonForm.pivotRow j := Fin.ext hij
    rw [hi]
    exact E.pivot_one j
  · rw [ite_eq_right hij]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact E.above_pivot_zero j i h
    · exact E.below_pivot_zero j i h

omit [DecidableEq F] in
private theorem echelon_lift (E : IsRowReduced A D) :
    D.echelon * pivotLift D =
      Matrix.ofFn (fun i j : Fin n => if i = j ∧ j.val < D.rank then 1 else 0) := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_ofFn]
  by_cases hj : j.val < D.rank
  · have hc := congrArg (fun v : Vector F n => v[i])
      (mulVec_unit D.echelon (D.pivotCols.get ⟨j.val, hj⟩))
    rw [getElem_mulVec, getElem_col] at hc
    rw [getElem_mul, pivotLift_col j hj, hc, echelon_pivot E]
    simp [hj, Fin.ext_iff]
  · rw [getElem_mul, pivotLift_col_zero j hj]
    have hz := congrArg (fun v : Vector F n => v[i]) (mulVec_zero D.echelon)
    rw [getElem_mulVec] at hz
    simpa [hj] using hz

omit [DecidableEq F] in
/-- Lifting a transformed right-hand side solves the reduced equations when
its coordinates below the rank vanish. -/
private theorem pivotLift_spec (E : IsRowReduced A D) (c : Vector F n)
    (hc : ∀ i : Fin n, D.rank ≤ i.val → c[i] = 0) :
    D.echelon * (pivotLift D * c) = c := by
  rw [← mul_assoc_vec, echelon_lift E]
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  change (Matrix.ofFn (fun i j : Fin n =>
    if i = j ∧ j.val < D.rank then (1 : F) else 0) * c)[ii] = c[ii]
  rw [getElem_mulVec, Vector.dotProduct]
  have he : ∀ j : Fin n,
      (row (Matrix.ofFn (fun i j : Fin n =>
        if i = j ∧ j.val < D.rank then (1 : F) else 0)) ii)[j] * c[j] =
        (if ii = j then 1 else 0) * c[j] := by
    intro j
    rw [getElem_row, getElem_ofFn]
    by_cases hj : j.val < D.rank
    · simp [hj]
    · rw [hc j (by omega)]
      grind
  rw [List.foldl_add_congr (List.finRange n) _ _ 0 (fun j _ => he j),
    foldl_indicator_mul_unique (List.finRange n) ii (fun j => c[j])
      (List.mem_finRange ii) (List.nodup_finRange n) 0]
  grind

omit [DecidableEq F] in
private theorem pivotLift_free (E : IsRowReduced A D) (k : Fin (m - D.rank)) :
    row (pivotLift D) (E.freeCols.get k) = 0 := by
  apply Vector.ext
  intro j hj
  let jj : Fin n := ⟨j, hj⟩
  change (row (pivotLift D) (E.freeCols.get k))[jj] = (0 : Vector F n)[jj]
  rw [getElem_row]
  simp only [pivotLift, getElem_ofFn]
  split
  next h =>
    rw [ite_eq_right (E.pivotCols_disjoint_freeCols ⟨j, h⟩ k)]
    simp
  next => simp

end IsRowReduced

open IsRowReduced

/-- A particular solution and the canonical nullspace matrix, sized by the
computed rank of the coefficient matrix. -/
abbrev SolveData (A : Matrix F n m) :=
  Vector F m × Matrix F m (m - rowReduce_rank A)

/-- Solve a field system completely. An error carries the first separating
row of the RREF transform; success includes the canonical nullspace basis. -/
def solve (A : Matrix F n m) (b : Vector F n) : Except (Vector F n) (SolveData A) :=
  let D := rowReduce A
  let c := D.transform * b
  match (List.finRange n).find? (fun i => decide (D.rank ≤ i.val ∧ c[i] ≠ 0)) with
  | some i => .error (row D.transform i)
  | none => .ok (pivotLift D * c, (rowReduce_isRowReduced A).nullspaceMatrix)

/-- The option view of `solve`, forgetting only the inconsistency witness. -/
@[expose]
def solve? (A : Matrix F n m) (b : Vector F n) : Option (SolveData A) :=
  (solve A b).toOption

omit [DecidableEq F] in
private theorem row_vecMul {k : Nat} (T : Matrix F k n) (A : Matrix F n m) (i : Fin k) :
    vecMul (row T i) A = row (T * A) i := by
  ext j hj
  let jj : Fin m := ⟨j, hj⟩
  change (vecMul (row T i) A)[jj] = (row (T * A) i)[jj]
  rw [vecMul, getElem_mulVec, row_transpose, getElem_row, getElem_mul,
    Vector.dotProduct_comm]

/-- Failure returns a left-kernel separator with nonzero pairing against the RHS. -/
theorem solve_error (A : Matrix F n m) (b y : Vector F n) :
    solve A b = .error y → vecMul y A = 0 ∧ Vector.dotProduct y b ≠ 0 := by
  intro h
  unfold solve at h
  dsimp only at h
  split at h
  next i hi =>
    cases Except.error.inj h
    have hp := List.find?_some hi
    have hp' : (rowReduce A).rank ≤ i.val ∧ ((rowReduce A).transform * b)[i] ≠ 0 :=
      of_decide_eq_true hp
    constructor
    · rw [row_vecMul, (rowReduce_isRowReduced A).transform_mul]
      exact (rowReduce_isRowReduced A).zero_row i hp'.1
    · simpa only [getElem_mulVec] using hp'.2
  next => contradiction

private theorem solve_ok (A : Matrix F n m) (b : Vector F n) (s : SolveData A)
    (h : solve A b = .ok s) : A * s.1 = b ∧ s.2 = nullspaceBasisMatrix A := by
  unfold solve at h
  dsimp only at h
  split at h
  next => contradiction
  next hn =>
    cases Except.ok.inj h
    refine ⟨?_, rfl⟩
    let D := rowReduce A
    let E := rowReduce_isRowReduced A
    have hc : ∀ i : Fin n, D.rank ≤ i.val → (D.transform * b)[i] = 0 := by
      intro i hi
      have hz := (List.find?_eq_none.mp hn) i (List.mem_finRange i)
      simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hz
      exact Classical.byContradiction (fun hne => hz ⟨hi, hne⟩)
    have he := E.pivotLift_spec (D.transform * b) hc
    obtain ⟨T, hT⟩ := E.transform_inv
    have ht : D.transform * (A * (pivotLift D * (D.transform * b))) =
        D.transform * b := by
      rw [← mul_assoc_vec, E.transform_mul]
      exact he
    have hh := congrArg (fun v : Vector F n => T * v) ht
    rw [← mul_assoc_vec T D.transform, ← mul_assoc_vec T D.transform,
      hT, identity_mulVec, identity_mulVec] at hh
    exact hh

omit [DecidableEq F] in
private theorem dot_mulVec (y : Vector F n) (A : Matrix F n m) (x : Vector F m) :
    Vector.dotProduct (vecMul y A) x = Vector.dotProduct y (A * x) := by
  let Y : Matrix F 1 n := Matrix.ofFn fun _ j => y[j]
  have hy : row Y 0 = y := by
    ext j hj
    change (row Y 0)[(⟨j, hj⟩ : Fin n)] = y[j]
    rw [getElem_row, getElem_ofFn]
    rfl
  have hh := congrArg (fun v : Vector F 1 => v[(0 : Fin 1)]) (mul_assoc_vec Y A x)
  rw [getElem_mulVec, getElem_mulVec, ← row_vecMul, hy] at hh
  exact hh

omit [DecidableEq F] in
private theorem dot_zero (x : Vector F m) : Vector.dotProduct (0 : Vector F m) x = 0 := by
  unfold Vector.dotProduct
  apply List.foldl_add_eq_self
  intro j _
  have hz : (0 : Vector F m)[j] = 0 := by simp
  rw [hz]
  grind

omit [DecidableEq F] in
private theorem separator_no_solution (A : Matrix F n m) (b y : Vector F n)
    (hy : vecMul y A = 0 ∧ Vector.dotProduct y b ≠ 0) :
    ¬ ∃ x : Vector F m, A * x = b := by
  rintro ⟨x, hx⟩
  apply hy.2
  rw [← hx, ← dot_mulVec, hy.1, dot_zero]

/-- Success is equivalent to mathematical consistency, with no resource-failure case. -/
theorem solve?_isSome (A : Matrix F n m) (b : Vector F n) :
    (solve? A b).isSome ↔ ∃ x : Vector F m, A * x = b := by
  unfold solve?
  cases h : solve A b with
  | ok s =>
    simp only [Except.toOption, Option.isSome_some, true_iff]
    exact ⟨s.1, (solve_ok A b s h).1⟩
  | error y =>
    simp only [Except.toOption, Option.isSome_none, Bool.false_eq_true, false_iff]
    exact separator_no_solution A b y (solve_error A b y h)

/-- The option API fails exactly on inconsistent systems. -/
theorem solve?_eq_none (A : Matrix F n m) (b : Vector F n) :
    solve? A b = none ↔ ¬ ∃ x : Vector F m, A * x = b := by
  rw [← solve?_isSome]
  cases solve? A b <;> simp

/-- Inconsistency is equivalent to existence of a separating row functional. -/
theorem solve?_none_witness (A : Matrix F n m) (b : Vector F n) :
    solve? A b = none ↔
      ∃ y : Vector F n, vecMul y A = 0 ∧ Vector.dotProduct y b ≠ 0 := by
  constructor
  · intro h
    cases hs : solve A b with
    | error y => exact ⟨y, solve_error A b y hs⟩
    | ok s => simp [solve?, hs, Except.toOption] at h
  · rintro ⟨y, hy⟩
    exact (solve?_eq_none A b).mpr (separator_no_solution A b y hy)

private theorem basis_mul (A : Matrix F n m) : A * nullspaceBasisMatrix A = 0 := by
  apply Matrix.ext_getElem
  intro i j
  have h := congrArg (fun v : Vector F n => v[i]) (nullspace_sound A j)
  rw [← nullspaceBasisMatrix_col] at h
  rw [getElem_mul, getElem_zero]
  rw [getElem_mulVec] at h
  have hz : (0 : Vector F n)[i] = 0 := by simp
  exact h.trans hz

omit [DecidableEq F] in
private theorem mulVec_sub (A : Matrix F n m) (x y : Vector F m) :
    A * (x - y) = A * x - A * y := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  change (A * (x - y))[ii] = (A * x - A * y)[ii]
  have hs : (A * x - A * y)[ii] = (A * x)[ii] - (A * y)[ii] :=
    Vector.getElem_sub (A * x) (A * y) i hi
  rw [hs, getElem_mulVec, getElem_mulVec, getElem_mulVec,
    Vector.dotProduct_sub_right]

/-- Every solution is the particular solution plus a combination of the
returned nullspace columns, and every such combination is a solution. -/
theorem solve?_spec (A : Matrix F n m) (b : Vector F n) (s : SolveData A) :
    solve? A b = some s →
      A * s.1 = b ∧ s.2 = nullspaceBasisMatrix A ∧
      ∀ x : Vector F m, A * x = b ↔
        ∃ c : Vector F (m - rowReduce_rank A), x = s.1 + s.2 * c := by
  intro h
  have hs : solve A b = .ok s := by
    cases hh : solve A b with
    | error y => simp [solve?, hh, Except.toOption] at h
    | ok t => simpa [solve?, hh, Except.toOption] using h
  obtain ⟨hp, hb⟩ := solve_ok A b s hs
  refine ⟨hp, hb, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hd : A * (x - s.1) = 0 := by
      rw [mulVec_sub, hx, hp]
      ext i hi
      simp only [Vector.getElem_sub, Vector.getElem_zero]
      grind
    obtain ⟨c, hc⟩ := nullspace_complete A (x - s.1) hd
    refine ⟨c, ?_⟩
    rw [hb, hc]
    ext i hi
    simp only [Vector.getElem_add, Vector.getElem_sub]
    grind
  · rintro ⟨c, rfl⟩
    rw [mulVec_add, hp, hb, ← mul_assoc_vec, basis_mul, zero_mulVec]
    ext i hi
    simp only [Vector.getElem_add, Vector.getElem_zero]
    grind

omit [DecidableEq F] in
private theorem basis_coordinate {A : Matrix F n m} {D : RowEchelonData F n m}
    (E : IsRowReduced A D) (c : Vector F (m - D.rank)) (k : Fin (m - D.rank)) :
    (E.nullspaceMatrix * c)[E.freeCols.get k] = c[k] := by
  have hr : row E.nullspaceMatrix (E.freeCols.get k) =
      row (Matrix.identity (R := F) (m - D.rank)) k := by
    ext j hj
    let jj : Fin (m - D.rank) := ⟨j, hj⟩
    change (row E.nullspaceMatrix (E.freeCols.get k))[jj] =
      (row (Matrix.identity _) k)[jj]
    rw [getElem_row, getElem_row, getElem_identity]
    by_cases hk : k = jj
    · rw [ite_eq_left hk, ← hk]
      exact E.nullspaceMatrix_free k
    · rw [ite_eq_right hk]
      exact E.nullspaceMatrix_free_ne (Ne.symm hk)
  rw [getElem_mulVec, hr]
  have h := congrArg (fun v : Vector F (m - D.rank) => v[k]) (identity_mulVec c)
  simpa only [getElem_mulVec] using h

/-- The canonical free coordinates make nullspace coefficients unique. -/
theorem solve?_unique (A : Matrix F n m) (b : Vector F n) (s : SolveData A)
    (c₁ c₂ : Vector F (m - rowReduce_rank A)) :
    solve? A b = some s → s.2 * c₁ = s.2 * c₂ → c₁ = c₂ := by
  intro hs hc
  rw [(solve?_spec A b s hs).2.1] at hc
  ext k hk
  let kk : Fin (m - rowReduce_rank A) := ⟨k, hk⟩
  have h := congrArg (fun v : Vector F m =>
    v[(rowReduce_isRowReduced A).freeCols.get kk]) hc
  exact (basis_coordinate (rowReduce_isRowReduced A) c₁ kk).symm.trans
    (h.trans (basis_coordinate (rowReduce_isRowReduced A) c₂ kk))

/-- The particular solution sets every canonical free coordinate to zero. -/
theorem solve?_free (A : Matrix F n m) (b : Vector F n) (s : SolveData A)
    (h : solve? A b = some s) (k : Fin (m - rowReduce_rank A)) :
    s.1[(rowReduce_isRowReduced A).freeCols.get k] = 0 := by
  unfold solve? solve at h
  dsimp only at h
  split at h
  next => simp [Except.toOption] at h
  next =>
    simp only [Except.toOption, Option.some.injEq] at h
    cases h
    rw [getElem_mulVec]
    exact (congrArg (fun v : Vector F n => v.dotProduct ((rowReduce A).transform * b))
      (pivotLift_free (rowReduce_isRowReduced A) k)).trans (dot_zero _)

/-- A system with no unknowns is consistent exactly for a zero RHS. -/
theorem solve?_noCols (A : Matrix F n 0) (b : Vector F n) :
    (solve? A b).isSome ↔ b = 0 := by
  rw [solve?_isSome]
  constructor
  · rintro ⟨x, hx⟩
    have hz : x = 0 := by apply Vector.ext; intro i hi; omega
    rw [hz, mulVec_zero] at hx
    exact hx.symm
  · intro hb
    exact ⟨0, by rw [mulVec_zero, hb]⟩

/-- With no equations, every RHS is empty and solve always succeeds. -/
theorem solve?_noRows (A : Matrix F 0 m) (b : Vector F 0) : (solve? A b).isSome := by
  rw [solve?_isSome]
  refine ⟨0, ?_⟩
  apply Vector.ext
  intro i hi
  omega

end Hex.Matrix
