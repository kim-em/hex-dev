/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Step

public section

/-!
The classical Euclidean-pivot Smith loop. Transform accumulation is optional:
`snf` and `snfRank` run the same loop with `none`, while `snfData` supplies the
four transformation matrices.
-/

namespace Hex.PolyMatrix

universe u

open Hex

@[expose] def polyZero {F : Type u} [Zero F] [DecidableEq F] : DensePoly F := Zero.zero
@[expose] def polyOne {F : Type u} [Lean.Grind.Field F] [DecidableEq F] : DensePoly F :=
  DensePoly.C (One.one : F)
@[expose] def polyNeg {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (p : DensePoly F) : DensePoly F := polyZero - p

/-- Executable polynomial identity matrix. -/
@[expose]
def polyIdentity {F : Type u} [Lean.Grind.Field F] [DecidableEq F] (n : Nat) :
    Matrix (DensePoly F) n n :=
  Matrix.ofFn fun i j => if i = j then polyOne else polyZero

/-- The executable identity agrees with the proof-oriented matrix identity. -/
theorem polyIdentity_eq_identity {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (n : Nat) :
    polyIdentity (F := F) n = Matrix.identity n := by
  apply Matrix.ext_getElem
  intro i j
  unfold polyIdentity
  rw [Matrix.getElem_ofFn, Matrix.getElem_identity]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij]
    rfl
  · rw [ite_eq_right hij, ite_eq_right hij]
    rfl

structure Transforms (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  left : Matrix (DensePoly F) n n
  leftInv : Matrix (DensePoly F) n n
  right : Matrix (DensePoly F) m m
  rightInv : Matrix (DensePoly F) m m

structure LoopState (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  work : Matrix (DensePoly F) n m
  pivot : Nat
  transforms : Option (Transforms F n m)

/-- Replace rows `i,j` by the two linear combinations encoded by `E`.
The source rows are snapshotted before either destination is written. -/
@[expose]
def pairRows {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin n) (E : Matrix R 2 2) : Matrix R n m :=
  let ri := Matrix.getRow A i
  let rj := Matrix.getRow A j
  let a := Vector.ofFn fun k => E[((0 : Fin 2), (0 : Fin 2))] * ri[k] +
    E[((0 : Fin 2), (1 : Fin 2))] * rj[k]
  let b := Vector.ofFn fun k => E[((1 : Fin 2), (0 : Fin 2))] * ri[k] +
    E[((1 : Fin 2), (1 : Fin 2))] * rj[k]
  (A.setRow i a).setRow j b

/-- Replace columns `i,j` by the transpose action of `E`. Thus every matrix
row pair `(a,b)` is sent to the transpose of `E * (a,b)`. -/
@[expose]
def pairCols {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin m) (E : Matrix R 2 2) : Matrix R n m :=
  let ci := Matrix.col A i
  let cj := Matrix.col A j
  let a : Vector R n := Vector.ofFn fun k => E[((0 : Fin 2), (0 : Fin 2))] * ci[k] +
    E[((0 : Fin 2), (1 : Fin 2))] * cj[k]
  let b : Vector R n := Vector.ofFn fun k => E[((1 : Fin 2), (0 : Fin 2))] * ci[k] +
    E[((1 : Fin 2), (1 : Fin 2))] * cj[k]
  (A.setCol i fun k : Fin n => a[k]).setCol j fun k : Fin n => b[k]

/-- The first replaced row of a two-row operation. -/
theorem pairRows_left {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin n) (E : Matrix R 2 2) (hij : i ≠ j)
    (k : Fin m) :
    (pairRows A i j E)[i][k] = E[((0 : Fin 2), (0 : Fin 2))] * A[i][k] +
      E[((0 : Fin 2), (1 : Fin 2))] * A[j][k] := by
  unfold pairRows
  rw [Matrix.setRow_row_ne _ _ _ _ hij, Matrix.setRow_get_self]
  simp

/-- The second replaced row of a two-row operation. -/
theorem pairRows_right {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin n) (E : Matrix R 2 2) (k : Fin m) :
    (pairRows A i j E)[j][k] = E[((1 : Fin 2), (0 : Fin 2))] * A[i][k] +
      E[((1 : Fin 2), (1 : Fin 2))] * A[j][k] := by
  unfold pairRows
  rw [Matrix.setRow_get_self]
  simp

/-- The first replaced column of a two-column operation. -/
theorem pairCols_left {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin m) (E : Matrix R 2 2) (hij : i ≠ j)
    (k : Fin n) :
    (pairCols A i j E)[k][i] = E[((0 : Fin 2), (0 : Fin 2))] * A[k][i] +
      E[((0 : Fin 2), (1 : Fin 2))] * A[k][j] := by
  unfold pairCols
  rw [Matrix.getElem_setCol, ite_eq_right hij, Matrix.getElem_setCol, ite_eq_left rfl]
  simp [Matrix.col]

/-- The second replaced column of a two-column operation. -/
theorem pairCols_right {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j : Fin m) (E : Matrix R 2 2) (k : Fin n) :
    (pairCols A i j E)[k][j] = E[((1 : Fin 2), (0 : Fin 2))] * A[k][i] +
      E[((1 : Fin 2), (1 : Fin 2))] * A[k][j] := by
  unfold pairCols
  rw [Matrix.getElem_setCol, ite_eq_left rfl]
  simp [Matrix.col]

/-- Rows outside the selected pair are unchanged. -/
theorem pairRows_other {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j r : Fin n) (E : Matrix R 2 2)
    (hri : r ≠ i) (hrj : r ≠ j) (k : Fin m) :
    (pairRows A i j E)[r][k] = A[r][k] := by
  unfold pairRows
  rw [Matrix.setRow_row_ne _ _ _ _ hrj,
    Matrix.setRow_row_ne _ _ _ _ hri]

/-- Columns outside the selected pair are unchanged. -/
theorem pairCols_other {R : Type u} [Zero R] [Add R] [Mul R] {n m : Nat}
    (A : Matrix R n m) (i j r : Fin m) (E : Matrix R 2 2)
    (hri : r ≠ i) (hrj : r ≠ j) (k : Fin n) :
    (pairCols A i j E)[k][r] = A[k][r] := by
  unfold pairCols
  rw [Matrix.getElem_setCol, ite_eq_right hrj,
    Matrix.getElem_setCol, ite_eq_right hri]

@[expose] def mapTransforms {F : Type u} [Zero F] [DecidableEq F] {n m : Nat}
    (s : LoopState F n m) (f : Transforms F n m → Transforms F n m) :
    LoopState F n m :=
  { s with transforms := s.transforms.map f }

@[expose] def swapRows {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin n) : LoopState F n m :=
  mapTransforms { s with work := s.work.rowSwap i j } fun t =>
    { t with
      left := t.left.rowSwap i j
      leftInv := t.leftInv.colSwap i j }

@[expose] def swapCols {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin m) : LoopState F n m :=
  mapTransforms { s with work := s.work.colSwap i j } fun t =>
    { t with
      right := t.right.colSwap i j
      rightInv := t.rightInv.rowSwap i j }

@[expose] def scaleRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i : Fin n) (c cinv : DensePoly F) :
    LoopState F n m :=
  mapTransforms { s with work := s.work.rowScale i c } fun t =>
    { t with
      left := t.left.rowScale i c
      leftInv := t.leftInv.colScale i cinv }

@[expose] def addRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (src dst : Fin n) (c : DensePoly F) :
    LoopState F n m :=
  mapTransforms { s with work := s.work.rowAdd src dst c } fun t =>
    { t with
      left := t.left.rowAdd src dst c
      leftInv := t.leftInv.colAdd dst src (polyNeg c) }

@[expose] def addCol {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (src dst : Fin m) (c : DensePoly F) :
    LoopState F n m :=
  mapTransforms { s with work := s.work.colAdd src dst c } fun t =>
    { t with
      right := t.right.colAdd src dst c
      rightInv := t.rightInv.rowAdd dst src (polyNeg c) }

@[expose] def bezoutRows {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin n) (e : PairStep F) :
    LoopState F n m :=
  mapTransforms { s with work := pairRows s.work i j e.forward } fun t =>
    { t with
      left := pairRows t.left i j e.forward
      leftInv := pairCols t.leftInv i j e.inverse.transpose }

@[expose] def bezoutCols {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin m) (e : PairStep F) :
    LoopState F n m :=
  mapTransforms { s with work := pairCols s.work i j e.forward } fun t =>
    { t with
      right := pairCols t.right i j e.forward
      rightInv := pairRows t.rightInv i j e.inverse.transpose }

@[simp] private theorem work_addRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (src dst : Fin n) (c : DensePoly F) :
    (addRow s src dst c).work = s.work.rowAdd src dst c := rfl

@[simp] private theorem work_addCol {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (src dst : Fin m) (c : DensePoly F) :
    (addCol s src dst c).work = s.work.colAdd src dst c := rfl

@[simp] private theorem work_bezoutRows {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin n) (e : PairStep F) :
    (bezoutRows s i j e).work = pairRows s.work i j e.forward := rfl

@[simp] private theorem work_bezoutCols {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin m) (e : PairStep F) :
    (bezoutCols s i j e).work = pairCols s.work i j e.forward := rfl

/-- A Bézout row step puts the pair-step pivot in the first row. -/
theorem bezoutRows_pivot {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin n) (k : Fin m)
  (hij : i ≠ j) :
    (bezoutRows s i j (pairStep s.work[(i, k)] s.work[(j, k)])).work[(i, k)] =
      (pairStep s.work[(i, k)] s.work[(j, k)]).pivot := by
  rw [work_bezoutRows]
  rw [Matrix.getElem_pair_eq_nested]
  rw [pairRows_left _ _ _ _ hij]
  have h := congrArg Prod.fst
    (pairStep_apply s.work[(i, k)] s.work[(j, k)])
  simpa [applyPair, Matrix.getElem_pair_eq_nested] using h

/-- A Bézout column step puts the pair-step pivot in the first column. -/
theorem bezoutCols_pivot {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (i j : Fin m) (k : Fin n)
    (hij : i ≠ j) :
    (bezoutCols s i j (pairStep s.work[(k, i)] s.work[(k, j)])).work[(k, i)] =
      (pairStep s.work[(k, i)] s.work[(k, j)]).pivot := by
  rw [work_bezoutCols]
  rw [Matrix.getElem_pair_eq_nested]
  rw [pairCols_left _ _ _ _ hij]
  have h := congrArg Prod.fst
    (pairStep_apply s.work[(k, i)] s.work[(k, j)])
  simpa [applyPair, Matrix.getElem_pair_eq_nested] using h

theorem addRow_keeps_pivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (jk : Fin m) (c : DensePoly F) (hi : ik ≠ i) :
    (addRow s ik i c).work[(ik, jk)] = s.work[(ik, jk)] := by
  rw [work_addRow, Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
    ite_eq_right hi]
  rw [Matrix.getElem_pair_eq_nested]

theorem addCol_keeps_pivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n)
    (jk j : Fin m) (c : DensePoly F) (hj : jk ≠ j) :
    (addCol s jk j c).work[(ik, jk)] = s.work[(ik, jk)] := by
  rw [work_addCol, Matrix.getElem_pair_eq_nested, Matrix.getElem_colAdd,
    ite_eq_right hj]
  rw [Matrix.getElem_pair_eq_nested]

private theorem bezoutRows_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (jk : Fin m) :
    (bezoutRows s ik i
      (pairStep s.work[(ik, jk)] s.work[(i, jk)])).work[(i, jk)] = 0 := by
  rw [work_bezoutRows, Matrix.getElem_pair_eq_nested,
    pairRows_right]
  have h := congrArg Prod.snd
    (pairStep_apply s.work[(ik, jk)] s.work[(i, jk)])
  simpa [applyPair, Matrix.getElem_pair_eq_nested] using h

private theorem bezoutCols_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n)
    (jk j : Fin m) :
    (bezoutCols s jk j
      (pairStep s.work[(ik, jk)] s.work[(ik, j)])).work[(ik, j)] = 0 := by
  rw [work_bezoutCols, Matrix.getElem_pair_eq_nested,
    pairCols_right]
  have h := congrArg Prod.snd
    (pairStep_apply s.work[(ik, jk)] s.work[(ik, j)])
  simpa [applyPair, Matrix.getElem_pair_eq_nested] using h

private theorem addRow_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (jk : Fin m) (hp : s.work[(ik, jk)] ≠ 0)
    (hmod : (s.work[(i, jk)] % s.work[(ik, jk)]).isZero = true) :
    (addRow s ik i
      (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))).work[(i, jk)] = 0 := by
  have hmod' : s.work[(i, jk)] % s.work[(ik, jk)] = 0 :=
    (DensePoly.size_eq_zero_iff _).mp ((DensePoly.isZero_eq_true_iff _).mp hmod)
  have hdiv := DensePoly.dvd_of_mod_eq_zero _ _ hmod'
  have hexact := DensePoly.exactDiv_mul_eq_of_dvd
    s.work[(i, jk)] s.work[(ik, jk)] hp hdiv
  have hexact' :
      Hex.exactDiv s.work[i][jk] s.work[ik][jk] * s.work[ik][jk] = s.work[i][jk] := by
    simpa [Matrix.getElem_pair_eq_nested] using hexact
  rw [work_addRow, Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
    ite_eq_left rfl]
  unfold polyNeg polyZero
  simp only [Matrix.getElem_pair_eq_nested]
  change s.work[i][jk] +
    ((0 : DensePoly F) - Hex.exactDiv s.work[i][jk] s.work[ik][jk]) *
      s.work[ik][jk] = 0
  rw [DensePoly.mul_comm_poly (0 - Hex.exactDiv s.work[i][jk] s.work[ik][jk])
      s.work[ik][jk],
    DensePoly.mul_sub_zero_comm, hexact']
  grind

private theorem addCol_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n)
    (jk j : Fin m) (hp : s.work[(ik, jk)] ≠ 0)
    (hmod : (s.work[(ik, j)] % s.work[(ik, jk)]).isZero = true) :
    (addCol s jk j
      (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))).work[(ik, j)] = 0 := by
  have hmod' : s.work[(ik, j)] % s.work[(ik, jk)] = 0 :=
    (DensePoly.size_eq_zero_iff _).mp ((DensePoly.isZero_eq_true_iff _).mp hmod)
  have hdiv := DensePoly.dvd_of_mod_eq_zero _ _ hmod'
  have hexact := DensePoly.exactDiv_mul_eq_of_dvd
    s.work[(ik, j)] s.work[(ik, jk)] hp hdiv
  have hexact' :
      Hex.exactDiv s.work[ik][j] s.work[ik][jk] * s.work[ik][jk] = s.work[ik][j] := by
    simpa [Matrix.getElem_pair_eq_nested] using hexact
  rw [work_addCol, Matrix.getElem_pair_eq_nested, Matrix.getElem_colAdd,
    ite_eq_left rfl]
  unfold polyNeg polyZero
  simp only [Matrix.getElem_pair_eq_nested]
  change s.work[ik][j] +
    ((0 : DensePoly F) - Hex.exactDiv s.work[ik][j] s.work[ik][jk]) *
      s.work[ik][jk] = 0
  rw [DensePoly.mul_comm_poly (0 - Hex.exactDiv s.work[ik][j] s.work[ik][jk])
      s.work[ik][jk],
    DensePoly.mul_sub_zero_comm, hexact']
  grind

private theorem addRow_other {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i r : Fin n)
    (jk : Fin m) (c : DensePoly F) (hri : r ≠ i) :
    (addRow s ik i c).work[(r, jk)] = s.work[(r, jk)] := by
  rw [work_addRow, Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
    ite_eq_right hri, Matrix.getElem_pair_eq_nested]

private theorem addCol_other {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n)
    (jk j r : Fin m) (c : DensePoly F) (hrj : r ≠ j) :
    (addCol s jk j c).work[(ik, r)] = s.work[(ik, r)] := by
  rw [work_addCol, Matrix.getElem_pair_eq_nested, Matrix.getElem_colAdd,
    ite_eq_right hrj, Matrix.getElem_pair_eq_nested]

private theorem bezoutRows_other {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i r : Fin n)
    (jk : Fin m) (hrk : r ≠ ik) (hri : r ≠ i) :
    (bezoutRows s ik i
      (pairStep s.work[(ik, jk)] s.work[(i, jk)])).work[(r, jk)] =
      s.work[(r, jk)] := by
  rw [work_bezoutRows, Matrix.getElem_pair_eq_nested,
    pairRows_other _ _ _ _ _ hrk hri, Matrix.getElem_pair_eq_nested]

private theorem bezoutCols_other {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n)
    (jk j r : Fin m) (hrk : r ≠ jk) (hrj : r ≠ j) :
    (bezoutCols s jk j
      (pairStep s.work[(ik, jk)] s.work[(ik, j)])).work[(ik, r)] =
      s.work[(ik, r)] := by
  rw [work_bezoutCols, Matrix.getElem_pair_eq_nested,
    pairCols_other _ _ _ _ _ hrk hrj, Matrix.getElem_pair_eq_nested]

@[expose] def trailingColStep {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat) (i : Fin n)
    (best : Option (Fin n × Fin m)) (j : Fin m) : Option (Fin n × Fin m) :=
  if j.val < k then best else
    let p := A[(i, j)]
    if p.isZero then best else
      match best with
      | none => some (i, j)
      | some q => if p.size < A[q].size then some (i, j) else best

@[expose] def trailingRowStep {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (best : Option (Fin n × Fin m)) (i : Fin n) : Option (Fin n × Fin m) :=
  if i.val < k then best else
    (List.finRange m).foldl (trailingColStep A k i) best

@[expose] def trailingMin {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat) : Option (Fin n × Fin m) :=
  (List.finRange n).foldl (trailingRowStep A k) none

@[expose] def normalizePivot {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (k : Nat) (hkN : k < n) (hkM : k < m) :
    LoopState F n m :=
  let i : Fin n := ⟨k, hkN⟩
  let j : Fin m := ⟨k, hkM⟩
  let p := s.work[(i, j)]
  let u := 1 / p.leadingCoeff
  scaleRow s i (DensePoly.C u) (DensePoly.C p.leadingCoeff)

/-- Check one entry while searching the strict trailing block. -/
@[expose] def badBlockEntry {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (ik : Fin n) (jk : Fin m)
    (i : Fin n) (j : Fin m) : Option (Fin n × Fin m) :=
  if ik.val < i.val ∧ jk.val < j.val ∧
      (A[(i, j)] % A[(ik, jk)]).isZero = false then some (i, j) else none

/-- Search one row of the strict trailing block without constructing a row of
coordinate pairs. -/
@[expose] def badBlockRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (ik : Fin n) (jk : Fin m)
    (i : Fin n) : Option (Fin n × Fin m) :=
  (List.finRange m).findSome? (badBlockEntry A ik jk i)

/-- Find an entry in the strict trailing block not divisible by the pivot. -/
@[expose] def badBlock {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (ik : Fin n) (jk : Fin m) :
    Option (Fin n × Fin m) :=
  (List.finRange n).findSome? (badBlockRow A ik jk)

theorem badBlock_some {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {ik : Fin n} {jk : Fin m}
    {i : Fin n} {j : Fin m} (h : badBlock A ik jk = some (i, j)) :
    ik.val < i.val ∧ jk.val < j.val ∧ (A[(i, j)] % A[(ik, jk)]).isZero = false := by
  unfold badBlock at h
  obtain ⟨i', hi'mem, hi'⟩ := List.exists_of_findSome?_eq_some h
  unfold badBlockRow at hi'
  obtain ⟨j', hj'mem, hj'⟩ := List.exists_of_findSome?_eq_some hi'
  unfold badBlockEntry at hj'
  split at hj'
  · rename_i hvalid
    simp only [Option.some.injEq, Prod.mk.injEq] at hj'
    rcases hj' with ⟨rfl, rfl⟩
    exact hvalid
  · simp at hj'

/-- Result of one structural clearing scan. A `dropped` result stops at the
first Bézout step, so the caller can restart under the smaller pivot. -/
structure ScanResult (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  state : LoopState F n m
  dropped : Bool

@[expose] def clearColumnScan {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (ik : Fin n) (jk : Fin m) :
    LoopState F n m → List (Fin n) → ScanResult F n m
  | s, [] => ⟨s, false⟩
  | s, i :: is =>
      if i = ik then clearColumnScan ik jk s is
      else
        let p := s.work[(ik, jk)]
        let b := s.work[(i, jk)]
        if b.isZero then clearColumnScan ik jk s is
        else if (b % p).isZero then
          clearColumnScan ik jk
            (addRow s ik i (polyNeg (Hex.exactDiv b p))) is
        else
          ⟨bezoutRows s ik i (pairStep p b), true⟩

@[expose] def clearRowScan {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (ik : Fin n) (jk : Fin m) :
    LoopState F n m → List (Fin m) → ScanResult F n m
  | s, [] => ⟨s, false⟩
  | s, j :: js =>
      if j = jk then clearRowScan ik jk s js
      else
        let p := s.work[(ik, jk)]
        let b := s.work[(ik, j)]
        if b.isZero then clearRowScan ik jk s js
        else if (b % p).isZero then
          clearRowScan ik jk
            (addCol s jk j (polyNeg (Hex.exactDiv b p))) js
        else
          ⟨bezoutCols s jk j (pairStep p b), true⟩

private theorem clearColumnScan_other {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik r : Fin n) (jk : Fin m) (s : LoopState F n m) (is : List (Fin n))
    (hrk : r ≠ ik) (hr : r ∉ is) :
    (clearColumnScan ik jk s is).state.work[(r, jk)] = s.work[(r, jk)] := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      have hri : r ≠ i := by
        intro h
        subst i
        exact hr (by simp)
      have hrTail : r ∉ is := by
        intro h
        exact hr (by simp [h])
      rw [clearColumnScan]
      split
      case isTrue => exact ih _ hrTail
      case isFalse =>
        simp only
        split
        case isTrue => exact ih _ hrTail
        case isFalse =>
          split
          case isTrue =>
            calc
              (clearColumnScan ik jk (addRow s ik i _) is).state.work[(r, jk)]
                  = (addRow s ik i _).work[(r, jk)] := ih _ hrTail
              _ = s.work[(r, jk)] := addRow_other s ik i r jk _ hri
          case isFalse => exact bezoutRows_other s ik i r jk hrk hri

private theorem clearRowScan_other {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk r : Fin m) (s : LoopState F n m) (js : List (Fin m))
    (hrk : r ≠ jk) (hr : r ∉ js) :
    (clearRowScan ik jk s js).state.work[(ik, r)] = s.work[(ik, r)] := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih =>
      have hrj : r ≠ j := by
        intro h
        subst j
        exact hr (by simp)
      have hrTail : r ∉ js := by
        intro h
        exact hr (by simp [h])
      rw [clearRowScan]
      split
      case isTrue => exact ih _ hrTail
      case isFalse =>
        simp only
        split
        case isTrue => exact ih _ hrTail
        case isFalse =>
          split
          case isTrue =>
            calc
              (clearRowScan ik jk (addCol s jk j _) js).state.work[(ik, r)]
                  = (addCol s jk j _).work[(ik, r)] := ih _ hrTail
              _ = s.work[(ik, r)] := addCol_other s ik jk j r _ hrj
          case isFalse => exact bezoutCols_other s ik jk j r hrk hrj

theorem clearColumnScan_pivot_ne_zero {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk : Fin m) (s : LoopState F n m) (is : List (Fin n))
    (hp : s.work[(ik, jk)] ≠ 0) :
    (clearColumnScan ik jk s is).state.work[(ik, jk)] ≠ 0 := by
  induction is generalizing s with
  | nil => exact hp
  | cons i is ih =>
      rw [clearColumnScan]
      split
      case isTrue => exact ih _ hp
      case isFalse hi =>
        simp only
        split
        case isTrue => exact ih _ hp
        case isFalse =>
          split
          case isTrue =>
            have hkeep := addRow_keeps_pivot s ik i jk
              (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))
              (Ne.symm hi)
            apply ih
            rw [hkeep]
            exact hp
          case isFalse =>
            rw [bezoutRows_pivot s ik i jk (Ne.symm hi)]
            exact pairStep_pivot_ne_zero_left hp

theorem clearRowScan_pivot_ne_zero {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk : Fin m) (s : LoopState F n m) (js : List (Fin m))
    (hp : s.work[(ik, jk)] ≠ 0) :
    (clearRowScan ik jk s js).state.work[(ik, jk)] ≠ 0 := by
  induction js generalizing s with
  | nil => exact hp
  | cons j js ih =>
      rw [clearRowScan]
      split
      case isTrue => exact ih _ hp
      case isFalse hj =>
        simp only
        split
        case isTrue => exact ih _ hp
        case isFalse =>
          split
          case isTrue =>
            have hkeep := addCol_keeps_pivot s ik jk j
              (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))
              (Ne.symm hj)
            apply ih
            rw [hkeep]
            exact hp
          case isFalse =>
            rw [bezoutCols_pivot s jk j ik (Ne.symm hj)]
            exact pairStep_pivot_ne_zero_left hp

theorem clearColumnScan_drop {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk : Fin m) (s : LoopState F n m) (is : List (Fin n))
    (hp : s.work[(ik, jk)] ≠ 0)
    (hd : (clearColumnScan ik jk s is).dropped = true) :
    (clearColumnScan ik jk s is).state.work[(ik, jk)].size <
      s.work[(ik, jk)].size := by
  induction is generalizing s with
  | nil => simp [clearColumnScan] at hd
  | cons i is ih =>
      rw [clearColumnScan] at hd ⊢
      split
      case isTrue h =>
        simp only [h] at hd ⊢
        exact ih _ hp hd
      case isFalse hi =>
        simp only [hi] at hd ⊢
        split
        case isTrue hzero =>
          simp only [hzero] at hd ⊢
          exact ih _ hp hd
        case isFalse hzero =>
          simp only [hzero] at hd ⊢
          split
          case isTrue hmod =>
            simp only [hmod] at hd ⊢
            have hkeep := addRow_keeps_pivot s ik i jk
              (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))
              (Ne.symm hi)
            have hp' : (addRow s ik i
                (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))).work[(ik, jk)] ≠ 0 := by
              rw [hkeep]
              exact hp
            have hlt := ih _ hp' hd
            rw [hkeep] at hlt
            exact hlt
          case isFalse hmod =>
            simp only [hmod] at hd ⊢
            have hnot : ¬s.work[(ik, jk)] ∣ s.work[(i, jk)] := by
              intro hdiv
              apply hmod
              rw [DensePoly.mod_eq_zero_of_dvd _ _ hdiv]
              rfl
            rw [bezoutRows_pivot s ik i jk (Ne.symm hi)]
            exact pairStep_pivot_size_lt_left hp hnot

theorem clearRowScan_drop {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk : Fin m) (s : LoopState F n m) (js : List (Fin m))
    (hp : s.work[(ik, jk)] ≠ 0)
    (hd : (clearRowScan ik jk s js).dropped = true) :
    (clearRowScan ik jk s js).state.work[(ik, jk)].size <
      s.work[(ik, jk)].size := by
  induction js generalizing s with
  | nil => simp [clearRowScan] at hd
  | cons j js ih =>
      rw [clearRowScan] at hd ⊢
      split
      case isTrue h =>
        simp only [h] at hd ⊢
        exact ih _ hp hd
      case isFalse hj =>
        simp only [hj] at hd ⊢
        split
        case isTrue hzero =>
          simp only [hzero] at hd ⊢
          exact ih _ hp hd
        case isFalse hzero =>
          simp only [hzero] at hd ⊢
          split
          case isTrue hmod =>
            simp only [hmod] at hd ⊢
            have hkeep := addCol_keeps_pivot s ik jk j
              (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))
              (Ne.symm hj)
            have hp' : (addCol s jk j
                (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))).work[(ik, jk)] ≠ 0 := by
              rw [hkeep]
              exact hp
            have hlt := ih _ hp' hd
            rw [hkeep] at hlt
            exact hlt
          case isFalse hmod =>
            simp only [hmod] at hd ⊢
            have hnot : ¬s.work[(ik, jk)] ∣ s.work[(ik, j)] := by
              intro hdiv
              apply hmod
              rw [DensePoly.mod_eq_zero_of_dvd _ _ hdiv]
              rfl
            rw [bezoutCols_pivot s jk j ik (Ne.symm hj)]
            exact pairStep_pivot_size_lt_left hp hnot

theorem clearColumnScan_zero {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik r : Fin n) (jk : Fin m) (s : LoopState F n m) (is : List (Fin n))
    (hp : s.work[(ik, jk)] ≠ 0) (hn : is.Nodup) (hrk : r ≠ ik)
    (hr : r ∈ is) (hd : (clearColumnScan ik jk s is).dropped = false) :
    (clearColumnScan ik jk s is).state.work[(r, jk)] = 0 := by
  induction is generalizing s with
  | nil => simp at hr
  | cons i is ih =>
      have hd0 := hd
      have hiTail : i ∉ is := (List.nodup_cons.mp hn).1
      have hnTail := (List.nodup_cons.mp hn).2
      rcases List.mem_cons.mp hr with hri | hrTail
      · subst i
        rw [clearColumnScan] at hd ⊢
        split
        case isTrue h => exact False.elim (hrk h)
        case isFalse hi =>
          simp only [hi] at hd ⊢
          split
          case isTrue hzero =>
            simp only [hzero] at hd ⊢
            rw [clearColumnScan_other ik r jk s is hrk hiTail]
            exact (DensePoly.size_eq_zero_iff _).mp
              ((DensePoly.isZero_eq_true_iff _).mp hzero)
          case isFalse hzero =>
            simp only [hzero] at hd ⊢
            split
            case isTrue hmod =>
              simp only [hmod] at hd ⊢
              rw [clearColumnScan_other ik r jk _ is hrk hiTail]
              exact addRow_zero s ik r jk hp hmod
            case isFalse hmod =>
              have hdtrue :
                  (clearColumnScan ik jk s (r :: is)).dropped = true := by
                simp_all [clearColumnScan, Matrix.getElem_pair_eq_nested,
                  Fin.getElem_fin]
              exact Bool.noConfusion (hdtrue.symm.trans hd0)
      · rw [clearColumnScan] at hd ⊢
        split
        case isTrue h =>
          simp only [h] at hd ⊢
          exact ih _ hp hnTail hrTail hd
        case isFalse hi =>
          simp only [hi] at hd ⊢
          split
          case isTrue hzero =>
            simp only [hzero] at hd ⊢
            exact ih _ hp hnTail hrTail hd
          case isFalse hzero =>
            simp only [hzero] at hd ⊢
            split
            case isTrue hmod =>
              simp only [hmod] at hd ⊢
              have hkeep := addRow_keeps_pivot s ik i jk
                (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))
                (Ne.symm hi)
              have hp' : (addRow s ik i
                  (polyNeg (Hex.exactDiv s.work[(i, jk)] s.work[(ik, jk)]))).work[(ik, jk)] ≠ 0 := by
                rw [hkeep]
                exact hp
              exact ih _ hp' hnTail hrTail hd
            case isFalse hmod =>
              have hdtrue :
                  (clearColumnScan ik jk s (i :: is)).dropped = true := by
                simp_all [clearColumnScan, Matrix.getElem_pair_eq_nested,
                  Fin.getElem_fin]
              exact Bool.noConfusion (hdtrue.symm.trans hd0)

theorem clearRowScan_zero {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk r : Fin m) (s : LoopState F n m) (js : List (Fin m))
    (hp : s.work[(ik, jk)] ≠ 0) (hn : js.Nodup) (hrk : r ≠ jk)
    (hr : r ∈ js) (hd : (clearRowScan ik jk s js).dropped = false) :
    (clearRowScan ik jk s js).state.work[(ik, r)] = 0 := by
  induction js generalizing s with
  | nil => simp at hr
  | cons j js ih =>
      have hd0 := hd
      have hjTail : j ∉ js := (List.nodup_cons.mp hn).1
      have hnTail := (List.nodup_cons.mp hn).2
      rcases List.mem_cons.mp hr with hrj | hrTail
      · subst j
        rw [clearRowScan] at hd ⊢
        split
        case isTrue h => exact False.elim (hrk h)
        case isFalse hj =>
          simp only [hj] at hd ⊢
          split
          case isTrue hzero =>
            simp only [hzero] at hd ⊢
            rw [clearRowScan_other ik jk r s js hrk hjTail]
            exact (DensePoly.size_eq_zero_iff _).mp
              ((DensePoly.isZero_eq_true_iff _).mp hzero)
          case isFalse hzero =>
            simp only [hzero] at hd ⊢
            split
            case isTrue hmod =>
              simp only [hmod] at hd ⊢
              rw [clearRowScan_other ik jk r _ js hrk hjTail]
              exact addCol_zero s ik jk r hp hmod
            case isFalse hmod =>
              have hdtrue :
                  (clearRowScan ik jk s (r :: js)).dropped = true := by
                simp_all [clearRowScan, Matrix.getElem_pair_eq_nested,
                  Fin.getElem_fin]
              exact Bool.noConfusion (hdtrue.symm.trans hd0)
      · rw [clearRowScan] at hd ⊢
        split
        case isTrue h =>
          simp only [h] at hd ⊢
          exact ih _ hp hnTail hrTail hd
        case isFalse hj =>
          simp only [hj] at hd ⊢
          split
          case isTrue hzero =>
            simp only [hzero] at hd ⊢
            exact ih _ hp hnTail hrTail hd
          case isFalse hzero =>
            simp only [hzero] at hd ⊢
            split
            case isTrue hmod =>
              simp only [hmod] at hd ⊢
              have hkeep := addCol_keeps_pivot s ik jk j
                (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))
                (Ne.symm hj)
              have hp' : (addCol s jk j
                  (polyNeg (Hex.exactDiv s.work[(ik, j)] s.work[(ik, jk)]))).work[(ik, jk)] ≠ 0 := by
                rw [hkeep]
                exact hp
              exact ih _ hp' hnTail hrTail hd
            case isFalse hmod =>
              have hdtrue :
                  (clearRowScan ik jk s (j :: js)).dropped = true := by
                simp_all [clearRowScan, Matrix.getElem_pair_eq_nested,
                  Fin.getElem_fin]
              exact Bool.noConfusion (hdtrue.symm.trans hd0)

theorem clearColumnScan_row {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik : Fin n) (jk c : Fin m) (s : LoopState F n m) (is : List (Fin n))
    (hd : (clearColumnScan ik jk s is).dropped = false) :
    (clearColumnScan ik jk s is).state.work[(ik, c)] = s.work[(ik, c)] := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      have hd0 := hd
      rw [clearColumnScan] at hd ⊢
      split
      case isTrue h =>
        simp only [h] at hd ⊢
        exact ih _ hd
      case isFalse hi =>
        simp only [hi] at hd ⊢
        split
        case isTrue hzero =>
          simp only [hzero] at hd ⊢
          exact ih _ hd
        case isFalse hzero =>
          simp only [hzero] at hd ⊢
          split
          case isTrue hmod =>
            simp only [hmod] at hd ⊢
            calc
              (clearColumnScan ik jk (addRow s ik i _) is).state.work[(ik, c)]
                  = (addRow s ik i _).work[(ik, c)] := ih _ hd
              _ = s.work[(ik, c)] := addRow_other s ik i ik c _ (Ne.symm hi)
          case isFalse hmod =>
            have hdtrue : (clearColumnScan ik jk s (i :: is)).dropped = true := by
              simp_all [clearColumnScan, Matrix.getElem_pair_eq_nested,
                Fin.getElem_fin]
            exact Bool.noConfusion (hdtrue.symm.trans hd0)

theorem clearRowScan_column {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (ik r : Fin n) (jk : Fin m) (s : LoopState F n m) (js : List (Fin m))
    (hd : (clearRowScan ik jk s js).dropped = false) :
    (clearRowScan ik jk s js).state.work[(r, jk)] = s.work[(r, jk)] := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih =>
      have hd0 := hd
      rw [clearRowScan] at hd ⊢
      split
      case isTrue h =>
        simp only [h] at hd ⊢
        exact ih _ hd
      case isFalse hj =>
        simp only [hj] at hd ⊢
        split
        case isTrue hzero =>
          simp only [hzero] at hd ⊢
          exact ih _ hd
        case isFalse hzero =>
          simp only [hzero] at hd ⊢
          split
          case isTrue hmod =>
            simp only [hmod] at hd ⊢
            calc
              (clearRowScan ik jk (addCol s jk j _) js).state.work[(r, jk)]
                  = (addCol s jk j _).work[(r, jk)] := ih _ hd
              _ = s.work[(r, jk)] := addCol_other s r jk j jk _ (Ne.symm hj)
          case isFalse hmod =>
            have hdtrue : (clearRowScan ik jk s (j :: js)).dropped = true := by
              simp_all [clearRowScan, Matrix.getElem_pair_eq_nested,
                Fin.getElem_fin]
            exact Bool.noConfusion (hdtrue.symm.trans hd0)

/-- The fused bad-block step: add a trailing row to the pivot row and
immediately apply the column Bézout operation that lowers the pivot. -/
@[expose] def blockStep {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (ik i : Fin n) (jk j : Fin m) :
    LoopState F n m :=
  let t := addRow s i ik polyOne
  bezoutCols t jk j (pairStep s.work[(ik, jk)] s.work[(i, j)])

private theorem blockAdd_pivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (jk : Fin m) (hzero : s.work[(i, jk)] = 0) :
    (addRow s i ik polyOne).work[(ik, jk)] = s.work[(ik, jk)] := by
  rw [work_addRow, Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
    ite_eq_left rfl]
  unfold polyOne
  simp only [Matrix.getElem_pair_eq_nested] at hzero ⊢
  rw [hzero]
  grind

private theorem blockAdd_entry {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (j : Fin m) (hzero : s.work[(ik, j)] = 0) :
    (addRow s i ik polyOne).work[(ik, j)] = s.work[(i, j)] := by
  rw [work_addRow, Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
    ite_eq_left rfl]
  unfold polyOne
  simp only [Matrix.getElem_pair_eq_nested] at hzero ⊢
  rw [hzero]
  change (0 : DensePoly F) + (1 : DensePoly F) * s.work[i][j] = s.work[i][j]
  rw [DensePoly.zero_add, DensePoly.mul_comm_poly,
    DensePoly.mul_one_right_poly]

theorem blockStep_pivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik i : Fin n)
    (jk j : Fin m) (hj : jk ≠ j) (hcol : s.work[(i, jk)] = 0)
    (hrow : s.work[(ik, j)] = 0) :
    (blockStep s ik i jk j).work[(ik, jk)] =
      (pairStep s.work[(ik, jk)] s.work[(i, j)]).pivot := by
  unfold blockStep
  let t := addRow s i ik polyOne
  have hp : t.work[(ik, jk)] = s.work[(ik, jk)] :=
    blockAdd_pivot s ik i jk hcol
  have hb : t.work[(ik, j)] = s.work[(i, j)] :=
    blockAdd_entry s ik i j hrow
  change (bezoutCols t jk j (pairStep s.work[(ik, jk)] s.work[(i, j)])).work[(ik, jk)] = _
  rw [← hp, ← hb, bezoutCols_pivot t jk j ik hj]

theorem bool_eq_false {b : Bool} (h : ¬b = true) : b = false := by
  cases b <;> simp_all

/-- Reduce one nonzero pivot until its row and column are clear and it divides
the strict trailing block. Restarts occur only after a strict pivot-size drop. -/
@[expose] def smithStage {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (ik : Fin n) (jk : Fin m)
    (hp : s.work[(ik, jk)] ≠ 0) : LoopState F n m :=
  let col := clearColumnScan ik jk s (List.finRange n)
  if hc : col.dropped then
    smithStage col.state ik jk
      (clearColumnScan_pivot_ne_zero ik jk s (List.finRange n) hp)
  else
    let row := clearRowScan ik jk col.state (List.finRange m)
    if hr : row.dropped then
      smithStage row.state ik jk
        (clearRowScan_pivot_ne_zero ik jk col.state (List.finRange m)
          (clearColumnScan_pivot_ne_zero ik jk s (List.finRange n) hp))
    else
      match hb : badBlock row.state.work ik jk with
      | none => row.state
      | some q =>
          have hc0 : col.dropped = false := bool_eq_false hc
          have hr0 : row.dropped = false := bool_eq_false hr
          have hq := badBlock_some hb
          have hki : ik ≠ q.1 := by omega
          have hkj : jk ≠ q.2 := by omega
          have hpCol := clearColumnScan_pivot_ne_zero
            ik jk s (List.finRange n) hp
          have hcol0 : col.state.work[(q.1, jk)] = 0 :=
            clearColumnScan_zero ik q.1 jk s (List.finRange n) hp
              (List.nodup_finRange n) (Ne.symm hki) (List.mem_finRange q.1) hc0
          have hcol : row.state.work[(q.1, jk)] = 0 := by
            rw [clearRowScan_column ik q.1 jk col.state (List.finRange m) hr0]
            exact hcol0
          have hrow : row.state.work[(ik, q.2)] = 0 :=
            clearRowScan_zero ik jk q.2 col.state (List.finRange m) hpCol
              (List.nodup_finRange m) (Ne.symm hkj) (List.mem_finRange q.2) hr0
          have hnot : ¬row.state.work[(ik, jk)] ∣ row.state.work[q] := by
            intro hd
            have hz := DensePoly.mod_eq_zero_of_dvd _ _ hd
            rw [hz] at hq
            exact Bool.noConfusion hq.2.2
          have hpRow := clearRowScan_pivot_ne_zero
            ik jk col.state (List.finRange m) hpCol
          have hpBlock : (blockStep row.state ik q.1 jk q.2).work[(ik, jk)] ≠ 0 := by
            rw [blockStep_pivot row.state ik q.1 jk q.2 hkj hcol hrow]
            exact pairStep_pivot_ne_zero_left hpRow
          smithStage (blockStep row.state ik q.1 jk q.2) ik jk hpBlock
termination_by s.work[(ik, jk)].size
decreasing_by
  · exact clearColumnScan_drop ik jk s (List.finRange n) hp hc
  · have hc0 : col.dropped = false := bool_eq_false hc
    have hcolEq := clearColumnScan_row ik jk jk s (List.finRange n) hc0
    calc
      row.state.work[(ik, jk)].size < col.state.work[(ik, jk)].size :=
        clearRowScan_drop ik jk col.state (List.finRange m)
          (clearColumnScan_pivot_ne_zero ik jk s (List.finRange n) hp) hr
      _ = s.work[(ik, jk)].size := congrArg DensePoly.size hcolEq
  · rw [blockStep_pivot row.state ik q.1 jk q.2 hkj hcol hrow]
    have hc0 : col.dropped = false := bool_eq_false hc
    have hr0 : row.dropped = false := bool_eq_false hr
    have hcolEq := clearColumnScan_row ik jk jk s (List.finRange n) hc0
    have hrowEq := clearRowScan_column ik ik jk col.state (List.finRange m) hr0
    calc
      (pairStep row.state.work[(ik, jk)] row.state.work[q]).pivot.size <
          row.state.work[(ik, jk)].size := pairStep_pivot_size_lt_left hpRow hnot
      _ = col.state.work[(ik, jk)].size := congrArg DensePoly.size hrowEq
      _ = s.work[(ik, jk)].size := congrArg DensePoly.size hcolEq

@[expose] def smithStageSafe {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (ik : Fin n) (jk : Fin m) :
    LoopState F n m :=
  if hp : s.work[(ik, jk)] = 0 then s else smithStage s ik jk hp

/-- Outer Smith loop, structurally bounded by the number of possible pivots.
The inner stage is independently well-founded by pivot size. -/
@[expose] def smithLoopTotal {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} : LoopState F n m → Nat → LoopState F n m
  | s, 0 => s
  | s, stages + 1 =>
      if hkN : s.pivot < n then
        if hkM : s.pivot < m then
          let ik : Fin n := ⟨s.pivot, hkN⟩
          let jk : Fin m := ⟨s.pivot, hkM⟩
          match trailingMin s.work s.pivot with
          | none => s
          | some q =>
              let moved := swapCols (swapRows s ik q.1) jk q.2
              let normalized := normalizePivot moved ik.val ik.isLt jk.isLt
              let reduced := smithStageSafe normalized ik jk
              smithLoopTotal { reduced with pivot := s.pivot + 1 } stages
        else s
      else s

@[expose] def runSmith {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (withTransforms : Bool) :
    LoopState F n m :=
  let transforms : Option (Transforms F n m) := if withTransforms then
    some (Transforms.mk (polyIdentity n) (polyIdentity n)
      (polyIdentity m) (polyIdentity m))
  else none
  let initial : LoopState F n m := { work := A, pivot := 0, transforms }
  smithLoopTotal initial (min n m)

/-- The optional transform accumulator is present. -/
@[expose] def HasTransforms {F : Type u} [Zero F] [DecidableEq F] {n m : Nat}
    (s : LoopState F n m) : Prop := ∃ t, s.transforms = some t

theorem hasTransforms_map {F : Type u} [Zero F] [DecidableEq F] {n m : Nat}
    {s : LoopState F n m} (f : Transforms F n m → Transforms F n m)
    (h : HasTransforms s) : HasTransforms (mapTransforms s f) := by
  rcases h with ⟨t, ht⟩
  refine ⟨f t, ?_⟩
  simp [mapTransforms, ht]

theorem hasTransforms_swapRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin n)
    (h : HasTransforms s) : HasTransforms (swapRows s i j) :=
  hasTransforms_map _ h

theorem hasTransforms_swapCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin m)
    (h : HasTransforms s) : HasTransforms (swapCols s i j) :=
  hasTransforms_map _ h

theorem hasTransforms_scaleRow {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i : Fin n)
    (c cinv : DensePoly F) (h : HasTransforms s) :
    HasTransforms (scaleRow s i c cinv) := hasTransforms_map _ h

theorem hasTransforms_addRow {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin n)
    (c : DensePoly F) (h : HasTransforms s) : HasTransforms (addRow s i j c) :=
  hasTransforms_map _ h

theorem hasTransforms_addCol {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin m)
    (c : DensePoly F) (h : HasTransforms s) : HasTransforms (addCol s i j c) :=
  hasTransforms_map _ h

theorem hasTransforms_bezoutRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin n)
    (e : PairStep F) (h : HasTransforms s) : HasTransforms (bezoutRows s i j e) :=
  hasTransforms_map _ h

theorem hasTransforms_bezoutCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (i j : Fin m)
    (e : PairStep F) (h : HasTransforms s) : HasTransforms (bezoutCols s i j e) :=
  hasTransforms_map _ h

theorem hasTransforms_clearColumnScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (is : List (Fin n)) {s : LoopState F n m} (h : HasTransforms s) :
    HasTransforms (clearColumnScan ik jk s is).state := by
  induction is generalizing s with
  | nil => exact h
  | cons i is ih =>
      rw [clearColumnScan]
      split
      · exact ih h
      · dsimp only
        split
        · exact ih h
        · split
          · exact ih (hasTransforms_addRow _ _ _ h)
          · exact hasTransforms_bezoutRows _ _ _ h

theorem hasTransforms_clearRowScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (js : List (Fin m)) {s : LoopState F n m} (h : HasTransforms s) :
    HasTransforms (clearRowScan ik jk s js).state := by
  induction js generalizing s with
  | nil => exact h
  | cons j js ih =>
      rw [clearRowScan]
      split
      · exact ih h
      · dsimp only
        split
        · exact ih h
        · split
          · exact ih (hasTransforms_addCol _ _ _ h)
          · exact hasTransforms_bezoutCols _ _ _ h

theorem hasTransforms_normalizePivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (k : Nat)
    (hkN : k < n) (hkM : k < m) (h : HasTransforms s) :
    HasTransforms (normalizePivot s k hkN hkM) := by
  unfold normalizePivot
  exact hasTransforms_scaleRow _ _ _ h

theorem hasTransforms_blockStep {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m}
    (ik i : Fin n) (jk j : Fin m) (h : HasTransforms s) :
    HasTransforms (blockStep s ik i jk j) := by
  unfold blockStep
  exact hasTransforms_bezoutCols _ _ _ (hasTransforms_addRow _ _ _ h)

theorem hasTransforms_smithStage {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m)
    (ik : Fin n) (jk : Fin m) (hp : s.work[(ik, jk)] ≠ 0)
    (h : HasTransforms s) : HasTransforms (smithStage s ik jk hp) := by
  induction s, hp using smithStage.induct ik jk with
  | case1 s hp col hc ih =>
      rw [smithStage]
      change (clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      simp [hc]
      exact ih (hasTransforms_clearColumnScan ik jk (List.finRange n) h)
  | case2 s hp col hc row hr ih =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      simp [hc, hr]
      exact ih (hasTransforms_clearRowScan ik jk (List.finRange m)
        (hasTransforms_clearColumnScan ik jk (List.finRange n) h))
  | case3 s hp col hc row hr hb =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = none at hb
      simp [hc, hr]
      split
      · exact hasTransforms_clearRowScan ik jk (List.finRange m)
          (hasTransforms_clearColumnScan ik jk (List.finRange n) h)
      · simp_all
  | case4 s hp col hc row hr q hb hc0 hr0 hq hki hkj hpCol hcol0 hcol hrow
      hnot hpRow hpBlock ih =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = some q at hb
      simp [hc, hr]
      split
      · simp_all
      · rename_i q' hb'
        have hqq : q' = q := by simp_all
        subst q'
        exact ih (hasTransforms_blockStep _ _ _ _
          (hasTransforms_clearRowScan ik jk (List.finRange m)
            (hasTransforms_clearColumnScan ik jk (List.finRange n) h)))

theorem hasTransforms_smithStageSafe {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m}
    (ik : Fin n) (jk : Fin m) (h : HasTransforms s) :
    HasTransforms (smithStageSafe s ik jk) := by
  unfold smithStageSafe
  split
  · exact h
  · exact hasTransforms_smithStage _ _ _ _ h

theorem hasTransforms_meta {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} {s : LoopState F n m} (pivot : Nat)
    (h : HasTransforms s) : HasTransforms { s with pivot } := h

theorem hasTransforms_smithLoopTotal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (stages : Nat)
    (h : HasTransforms s) : HasTransforms (smithLoopTotal s stages) := by
  induction stages generalizing s with
  | zero => exact h
  | succ stages ih =>
      rw [smithLoopTotal]
      split
      · split
        · cases trailingMin s.work s.pivot with
          | none => exact h
          | some q =>
              apply ih
              apply hasTransforms_meta
              apply hasTransforms_smithStageSafe
              apply hasTransforms_normalizePivot
              apply hasTransforms_swapCols
              apply hasTransforms_swapRows
              exact h
        · exact h
      · exact h

/-- A transform-accumulating run never loses its accumulator. -/
theorem hasTransforms_runSmith_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    HasTransforms (runSmith A true) := by
  unfold runSmith
  apply hasTransforms_smithLoopTotal
  exact ⟨_, rfl⟩

@[expose] def loopRank {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) : Nat := min s.pivot (min n m)

@[expose] def diagonalVector {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) : Vector (DensePoly F) (loopRank s) :=
  Vector.ofFn fun i =>
    let ii : Fin n := ⟨i.val, by
      have hi : i.val < min s.pivot (min n m) := by simpa [loopRank] using i.isLt
      exact Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))⟩
    let jj : Fin m := ⟨i.val, by
      have hi : i.val < min s.pivot (min n m) := by simpa [loopRank] using i.isLt
      exact Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))⟩
    s.work[(ii, jj)]

/-- Polynomial Smith normal form. This path does not allocate or update
transformation matrices. -/
@[expose]
def snf {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : Matrix (DensePoly F) n m :=
  (runSmith A false).work

/-- Rank returned by the same transform-free Smith run. -/
@[expose]
def snfRank {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : Nat :=
  loopRank (runSmith A false)

/-- Full Smith data, including explicit inverses of both transformations. -/
@[expose]
def snfData {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : SmithData F n m :=
  let s := runSmith A true
  let t := s.transforms.get (by
    rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
    simp [s, ht])
  { rank := loopRank s, diag := diagonalVector s,
    left := t.left, leftInv := t.leftInv, right := t.right, rightInv := t.rightInv }

/-- An explicit description of `snfData` from any witness carried by the full
Smith run. This keeps clients independent of the proof used by `Option.get`. -/
theorem snfData_eq_of_transforms {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (t : Transforms F n m) (ht : (runSmith A true).transforms = some t) :
    snfData A =
      { rank := loopRank (runSmith A true), diag := diagonalVector (runSmith A true),
        left := t.left, leftInv := t.leftInv, right := t.right, rightInv := t.rightInv } := by
  unfold snfData
  dsimp only
  rw [Option.get_of_eq_some _ ht]

end Hex.PolyMatrix
