/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Diagonal
public import HexHermite.Lattice
import Batteries.Data.Vector.Lemmas

public section

/-! Structural correctness facts for the accumulator-parametric Smith run. -/

namespace Hex.Matrix
namespace Smith

private theorem clearColumn_spec (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hne : pivotRow ≠ row)
    (hb : s.matrix[(row, pivotCol)] ≠ 0) :
    let p := s.matrix[(pivotRow, pivotCol)]
    let b := s.matrix[(row, pivotCol)]
    (clearColumn ops s pivotRow row pivotCol).matrix[(pivotRow, pivotCol)] =
        (if b % p = 0 then p else Int.ofNat (Int.gcd p b)) ∧
      (clearColumn ops s pivotRow row pivotCol).matrix[(row, pivotCol)] = 0 := by
  let p := s.matrix[(pivotRow, pivotCol)]
  let b := s.matrix[(row, pivotCol)]
  by_cases hdiv : b % p = 0
  · dsimp only [p, b] at hdiv ⊢
    have hdiv' : s.matrix[row][pivotCol] % s.matrix[pivotRow][pivotCol] = 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hdiv
    rw [clearColumn, ite_eq_left hdiv]
    dsimp only
    constructor
    · simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_rowAdd, ite_eq_right hne]
      rw [ite_eq_left hdiv']
    · simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_rowAdd, ite_eq_left rfl]
      have hdvd : p ∣ b := Int.dvd_of_emod_eq_zero hdiv
      have hquot : HexArith.Int.exactDiv b p * p = b := by
        simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hdvd
      dsimp only [p, b] at hquot
      simp only [Matrix.getElem_pair_eq_nested] at hquot
      rw [Int.neg_mul, hquot]
      omega
  · dsimp only [p, b] at hdiv ⊢
    have hdiv' : s.matrix[row][pivotCol] % s.matrix[pivotRow][pivotCol] ≠ 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hdiv
    rw [clearColumn, ite_eq_right hdiv]
    rcases hc : Hermite.gcdCoeffs p b with ⟨x, y, z, w⟩
    have hpivot := Hermite.gcdCoeffs_pivot p b
    have happly := Hermite.gcdCoeffs_apply (a := p) (b := b) hb
    rw [hc] at hpivot happly
    dsimp only [p, b] at hpivot happly ⊢
    simp only [Matrix.getElem_pair_eq_nested] at hpivot happly
    constructor
    · simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineRows,
        ite_eq_left]
      rw [ite_eq_right hdiv']
      exact hpivot
    · simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineRows,
        ite_eq_right (Ne.symm hne), ite_eq_left]
      exact happly.2

private theorem clearRow_spec (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hne : pivotCol ≠ col)
    (hb : s.matrix[(pivotRow, col)] ≠ 0) :
    let p := s.matrix[(pivotRow, pivotCol)]
    let b := s.matrix[(pivotRow, col)]
    (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, pivotCol)] =
        (if b % p = 0 then p else Int.ofNat (Int.gcd p b)) ∧
      (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, col)] = 0 := by
  let p := s.matrix[(pivotRow, pivotCol)]
  let b := s.matrix[(pivotRow, col)]
  by_cases hdiv : b % p = 0
  · dsimp only [p, b] at hdiv ⊢
    have hdiv' : s.matrix[pivotRow][col] % s.matrix[pivotRow][pivotCol] = 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hdiv
    rw [clearRow, ite_eq_left hdiv]
    dsimp only
    constructor
    · simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_colAdd, ite_eq_right hne, ite_eq_left hdiv']
    · simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_colAdd, ite_eq_left rfl]
      have hdvd : p ∣ b := Int.dvd_of_emod_eq_zero hdiv
      have hquot : HexArith.Int.exactDiv b p * p = b := by
        simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hdvd
      dsimp only [p, b] at hquot
      simp only [Matrix.getElem_pair_eq_nested] at hquot
      rw [Int.neg_mul, hquot]
      omega
  · dsimp only [p, b] at hdiv ⊢
    have hdiv' : s.matrix[pivotRow][col] % s.matrix[pivotRow][pivotCol] ≠ 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hdiv
    rw [clearRow, ite_eq_right hdiv]
    rcases hc : Hermite.gcdCoeffs p b with ⟨x, y, z, w⟩
    have hpivot := Hermite.gcdCoeffs_pivot p b
    have happly := Hermite.gcdCoeffs_apply (a := p) (b := b) hb
    rw [hc] at hpivot happly
    dsimp only [p, b] at hpivot happly ⊢
    simp only [Matrix.getElem_pair_eq_nested] at hpivot happly
    constructor
    · simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineCols,
        ite_eq_left]
      rw [ite_eq_right hdiv']
      exact hpivot
    · simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineCols,
        ite_eq_right (Ne.symm hne), ite_eq_left]
      exact happly.2

private theorem gcd_lt_natAbs {p b : Int} (hp : p ≠ 0) (hmod : b % p ≠ 0) :
    Int.gcd p b < p.natAbs := by
  have hpabs : 0 < p.natAbs := Int.natAbs_pos.mpr hp
  have hle := Nat.gcd_le_left b.natAbs hpabs
  apply Nat.lt_of_le_of_ne hle
  intro heq
  have hdvdNat : p.natAbs ∣ b.natAbs := by
    rw [← heq]
    exact Int.gcd_dvd_natAbs_right p b
  have hdvd : p ∣ b := Int.natAbs_dvd_natAbs.mp hdvdNat
  exact hmod (Int.emod_eq_zero_of_dvd hdvd)

private theorem clearColumn_pivot_lt (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hne : pivotRow ≠ row) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(row, pivotCol)] ≠ 0)
    (hmod : s.matrix[(row, pivotCol)] % s.matrix[(pivotRow, pivotCol)] ≠ 0) :
    (clearColumn ops s pivotRow row pivotCol).matrix[(pivotRow, pivotCol)].natAbs <
      s.matrix[(pivotRow, pivotCol)].natAbs := by
  have hs := clearColumn_spec ops s pivotRow row pivotCol hne hb
  dsimp only at hs
  rw [ite_eq_right hmod] at hs
  rw [hs.1]
  exact gcd_lt_natAbs hp hmod

private theorem clearRow_pivot_lt (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hne : pivotCol ≠ col) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(pivotRow, col)] ≠ 0)
    (hmod : s.matrix[(pivotRow, col)] % s.matrix[(pivotRow, pivotCol)] ≠ 0) :
    (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, pivotCol)].natAbs <
      s.matrix[(pivotRow, pivotCol)].natAbs := by
  have hs := clearRow_spec ops s pivotRow pivotCol col hne hb
  dsimp only at hs
  rw [ite_eq_right hmod] at hs
  rw [hs.1]
  exact gcd_lt_natAbs hp hmod

/-- Number of nonzero entries strictly below or right of the active pivot. -/
@[expose]
def crossCount (M : Matrix Int n m) (pivotRow : Fin n) (pivotCol : Fin m) : Nat :=
  (List.finRange n).foldl (fun count row => count +
    if pivotRow.val < row.val ∧ M[(row, pivotCol)] ≠ 0 then 1 else 0) 0 +
  (List.finRange m).foldl (fun count col => count +
    if pivotCol.val < col.val ∧ M[(pivotRow, col)] ≠ 0 then 1 else 0) 0

private theorem foldl_remove_one {R : Type} (xs : List R) (q : R)
    (f : R → Nat) [DecidableEq R] (hmem : q ∈ xs) (hnodup : xs.Nodup)
    (hfq : f q = 1) :
    xs.foldl (fun total x => total + f x) 0 =
      xs.foldl (fun total x => total + if x = q then 0 else f x) 0 + 1 := by
  calc
    xs.foldl (fun total x => total + f x) 0 =
        xs.foldl (fun total x => total +
          ((if x = q then 1 else 0) + (if x = q then 0 else f x))) 0 := by
      apply List.foldl_add_congr
      intro x _hx
      by_cases hx : x = q
      · subst x
        simp [hfq]
      · simp [hx]
    _ = xs.foldl (fun total x => total + if x = q then 1 else 0) 0 +
        xs.foldl (fun total x => total + if x = q then 0 else f x) 0 :=
      List.foldl_add_add (R := Nat) xs _ _
    _ = xs.foldl (fun total x => total + if x = q then 0 else f x) 0 + 1 := by
      rw [List.foldl_add_single xs 0 q (fun _ => 1) hmem hnodup]
      omega

private theorem foldl_add_le_length {R : Type} (xs : List R) (f : R → Nat)
    (acc : Nat) (hf : ∀ x ∈ xs, f x ≤ 1) :
    xs.foldl (fun total x => total + f x) acc ≤ acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      apply Nat.le_trans (ih (acc + f x) (by
        intro y hy
        exact hf y (List.mem_cons_of_mem x hy)))
      have hx := hf x (by simp)
      omega

private theorem crossCount_le (M : Matrix Int n m) (pivotRow : Fin n)
    (pivotCol : Fin m) : crossCount M pivotRow pivotCol ≤ n + m := by
  unfold crossCount
  have hr := foldl_add_le_length (List.finRange n)
    (fun row => if pivotRow.val < row.val ∧ M[(row, pivotCol)] ≠ 0 then 1 else 0)
    0 (by intro row _; split <;> omega)
  have hc := foldl_add_le_length (List.finRange m)
    (fun col => if pivotCol.val < col.val ∧ M[(pivotRow, col)] ≠ 0 then 1 else 0)
    0 (by intro col _; split <;> omega)
  simp only [List.length_finRange, Nat.zero_add] at hr hc
  omega

private theorem crossCount_clearColumn (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hr : pivotRow.val < row.val)
    (hb : s.matrix[(row, pivotCol)] ≠ 0)
    (hdiv : s.matrix[(row, pivotCol)] % s.matrix[(pivotRow, pivotCol)] = 0) :
    crossCount (clearColumn ops s pivotRow row pivotCol).matrix pivotRow pivotCol + 1 =
      crossCount s.matrix pivotRow pivotCol := by
  have hne : pivotRow ≠ row := by
    intro heq
    have := congrArg Fin.val heq
    omega
  have hs := clearColumn_spec ops s pivotRow row pivotCol hne hb
  dsimp only at hs
  rw [ite_eq_left hdiv] at hs
  have hb' : s.matrix[row][pivotCol] ≠ 0 := by
    simpa only [Matrix.getElem_pair_eq_nested] using hb
  have hsZero :
      (clearColumn ops s pivotRow row pivotCol).matrix[row][pivotCol] = 0 := by
    simpa only [Matrix.getElem_pair_eq_nested] using hs.2
  let oldCol : Fin n → Nat := fun r =>
    if pivotRow.val < r.val ∧ s.matrix[(r, pivotCol)] ≠ 0 then 1 else 0
  let newCol : Fin n → Nat := fun r =>
    if pivotRow.val < r.val ∧
        (clearColumn ops s pivotRow row pivotCol).matrix[(r, pivotCol)] ≠ 0 then 1 else 0
  let oldRow : Fin m → Nat := fun c =>
    if pivotCol.val < c.val ∧ s.matrix[(pivotRow, c)] ≠ 0 then 1 else 0
  let newRow : Fin m → Nat := fun c =>
    if pivotCol.val < c.val ∧
        (clearColumn ops s pivotRow row pivotCol).matrix[(pivotRow, c)] ≠ 0 then 1 else 0
  have hold := foldl_remove_one (List.finRange n) row oldCol
    (List.mem_finRange row) (List.nodup_finRange n) (by
      unfold oldCol
      rw [ite_eq_left ⟨hr, hb⟩])
  have hcol : (List.finRange n).foldl (fun total r => total + newCol r) 0 =
      (List.finRange n).foldl
        (fun total r => total + if r = row then 0 else oldCol r) 0 := by
    apply List.foldl_add_congr
    intro r _hmem
    by_cases hrr : r = row
    · subst r
      unfold newCol
      rw [ite_eq_right (by intro hbad; exact hbad.2 hs.2)]
      simp
    · have hentry :
          (clearColumn ops s pivotRow row pivotCol).matrix[(r, pivotCol)] =
            s.matrix[(r, pivotCol)] := by
        rw [clearColumn, ite_eq_left hdiv]
        dsimp only
        simp only [Matrix.getElem_pair_eq_nested]
        rw [Matrix.getElem_rowAdd, ite_eq_right hrr]
      unfold newCol oldCol
      rw [hentry]
      simp [hrr]
  have hrow : (List.finRange m).foldl (fun total c => total + newRow c) 0 =
      (List.finRange m).foldl (fun total c => total + oldRow c) 0 := by
    apply List.foldl_add_congr
    intro c _hmem
    have hentry :
        (clearColumn ops s pivotRow row pivotCol).matrix[(pivotRow, c)] =
          s.matrix[(pivotRow, c)] := by
      rw [clearColumn, ite_eq_left hdiv]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_rowAdd, ite_eq_right hne]
    unfold newRow oldRow
    rw [hentry]
  unfold crossCount
  change (List.finRange n).foldl (fun total r => total + newCol r) 0 +
      (List.finRange m).foldl (fun total c => total + newRow c) 0 + 1 =
    (List.finRange n).foldl (fun total r => total + oldCol r) 0 +
      (List.finRange m).foldl (fun total c => total + oldRow c) 0
  rw [hcol, hrow]
  omega

private theorem crossCount_clearRow (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hc : pivotCol.val < col.val)
    (hb : s.matrix[(pivotRow, col)] ≠ 0)
    (hdiv : s.matrix[(pivotRow, col)] % s.matrix[(pivotRow, pivotCol)] = 0) :
    crossCount (clearRow ops s pivotRow pivotCol col).matrix pivotRow pivotCol + 1 =
      crossCount s.matrix pivotRow pivotCol := by
  have hne : pivotCol ≠ col := by
    intro heq
    have := congrArg Fin.val heq
    omega
  have hs := clearRow_spec ops s pivotRow pivotCol col hne hb
  dsimp only at hs
  rw [ite_eq_left hdiv] at hs
  let oldCol : Fin n → Nat := fun r =>
    if pivotRow.val < r.val ∧ s.matrix[(r, pivotCol)] ≠ 0 then 1 else 0
  let newCol : Fin n → Nat := fun r =>
    if pivotRow.val < r.val ∧
        (clearRow ops s pivotRow pivotCol col).matrix[(r, pivotCol)] ≠ 0 then 1 else 0
  let oldRow : Fin m → Nat := fun c =>
    if pivotCol.val < c.val ∧ s.matrix[(pivotRow, c)] ≠ 0 then 1 else 0
  let newRow : Fin m → Nat := fun c =>
    if pivotCol.val < c.val ∧
        (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, c)] ≠ 0 then 1 else 0
  have hold := foldl_remove_one (List.finRange m) col oldRow
    (List.mem_finRange col) (List.nodup_finRange m) (by
      unfold oldRow
      rw [ite_eq_left ⟨hc, hb⟩])
  have hcol : (List.finRange n).foldl (fun total r => total + newCol r) 0 =
      (List.finRange n).foldl (fun total r => total + oldCol r) 0 := by
    apply List.foldl_add_congr
    intro r _hmem
    have hentry :
        (clearRow ops s pivotRow pivotCol col).matrix[(r, pivotCol)] =
          s.matrix[(r, pivotCol)] := by
      rw [clearRow, ite_eq_left hdiv]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_colAdd, ite_eq_right hne]
    unfold newCol oldCol
    rw [hentry]
  have hrow : (List.finRange m).foldl (fun total c => total + newRow c) 0 =
      (List.finRange m).foldl
        (fun total c => total + if c = col then 0 else oldRow c) 0 := by
    apply List.foldl_add_congr
    intro c _hmem
    by_cases hcc : c = col
    · subst c
      unfold newRow
      rw [ite_eq_right (by intro hbad; exact hbad.2 hs.2)]
      simp
    · have hentry :
          (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, c)] =
            s.matrix[(pivotRow, c)] := by
        rw [clearRow, ite_eq_left hdiv]
        dsimp only
        simp only [Matrix.getElem_pair_eq_nested]
        rw [Matrix.getElem_colAdd, ite_eq_right hcc]
      unfold newRow oldRow
      rw [hentry]
      simp [hcc]
  unfold crossCount
  change (List.finRange n).foldl (fun total r => total + newCol r) 0 +
      (List.finRange m).foldl (fun total c => total + newRow c) 0 + 1 =
    (List.finRange n).foldl (fun total r => total + oldCol r) 0 +
      (List.finRange m).foldl (fun total c => total + oldRow c) 0
  rw [hcol, hrow]
  omega

/-- Lexicographic termination measure combining pivot magnitude and uncleared
cross entries. -/
@[expose]
def reductionMeasure (M : Matrix Int n m) (pivotRow : Fin n)
    (pivotCol : Fin m) : Nat :=
  M[(pivotRow, pivotCol)].natAbs * (n + m + 1) + crossCount M pivotRow pivotCol

private theorem measure_pivot_lt (M M' : Matrix Int n m)
    (pivotRow : Fin n) (pivotCol : Fin m)
    (hpivot : M'[(pivotRow, pivotCol)].natAbs < M[(pivotRow, pivotCol)].natAbs) :
    reductionMeasure M' pivotRow pivotCol < reductionMeasure M pivotRow pivotCol := by
  unfold reductionMeasure
  let a := M'[(pivotRow, pivotCol)].natAbs
  let b := M[(pivotRow, pivotCol)].natAbs
  let width := n + m
  have hcount : crossCount M' pivotRow pivotCol ≤ width := by
    exact crossCount_le M' pivotRow pivotCol
  have hab : a + 1 ≤ b := Nat.succ_le_of_lt hpivot
  have hfirst : a * (width + 1) + crossCount M' pivotRow pivotCol <
      (a + 1) * (width + 1) := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hsecond : (a + 1) * (width + 1) ≤ b * (width + 1) :=
    Nat.mul_le_mul_right (width + 1) hab
  have hthird : b * (width + 1) ≤
      b * (width + 1) + crossCount M pivotRow pivotCol := Nat.le_add_right _ _
  exact Nat.lt_of_lt_of_le hfirst (Nat.le_trans hsecond hthird)

private theorem measure_clearColumn_lt (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hr : pivotRow.val < row.val) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(row, pivotCol)] ≠ 0) :
    reductionMeasure (clearColumn ops s pivotRow row pivotCol).matrix pivotRow pivotCol <
      reductionMeasure s.matrix pivotRow pivotCol := by
  have hne : pivotRow ≠ row := by
    intro heq
    have := congrArg Fin.val heq
    omega
  by_cases hdiv : s.matrix[(row, pivotCol)] % s.matrix[(pivotRow, pivotCol)] = 0
  · have hs := clearColumn_spec ops s pivotRow row pivotCol hne hb
    dsimp only at hs
    rw [ite_eq_left hdiv] at hs
    have hcount := crossCount_clearColumn ops s pivotRow row pivotCol hr hb hdiv
    unfold reductionMeasure
    rw [hs.1]
    omega
  · apply measure_pivot_lt
    exact clearColumn_pivot_lt ops s pivotRow row pivotCol hne hp hb hdiv

private theorem measure_clearRow_lt (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hc : pivotCol.val < col.val) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(pivotRow, col)] ≠ 0) :
    reductionMeasure (clearRow ops s pivotRow pivotCol col).matrix pivotRow pivotCol <
      reductionMeasure s.matrix pivotRow pivotCol := by
  have hne : pivotCol ≠ col := by
    intro heq
    have := congrArg Fin.val heq
    omega
  by_cases hdiv : s.matrix[(pivotRow, col)] % s.matrix[(pivotRow, pivotCol)] = 0
  · have hs := clearRow_spec ops s pivotRow pivotCol col hne hb
    dsimp only at hs
    rw [ite_eq_left hdiv] at hs
    have hcount := crossCount_clearRow ops s pivotRow pivotCol col hc hb hdiv
    unfold reductionMeasure
    rw [hs.1]
    omega
  · apply measure_pivot_lt
    exact clearRow_pivot_lt ops s pivotRow pivotCol col hne hp hb hdiv

private theorem repair_pivot (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol col : Fin m)
    (hrow : s.matrix[(row, pivotCol)] = 0)
    (hcol : s.matrix[(pivotRow, col)] = 0) :
    (repair ops s pivotRow row pivotCol col).matrix[(pivotRow, pivotCol)] =
      Int.ofNat (Int.gcd s.matrix[(pivotRow, pivotCol)] s.matrix[(row, col)]) := by
  let matrix := Matrix.rowAdd s.matrix row pivotRow 1
  have hpivot : matrix[(pivotRow, pivotCol)] = s.matrix[(pivotRow, pivotCol)] := by
    dsimp only [matrix]
    simp only [Matrix.getElem_pair_eq_nested]
    rw [Matrix.getElem_rowAdd, ite_eq_left rfl]
    have hrow' : s.matrix[row][pivotCol] = 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hrow
    rw [hrow']
    omega
  have hbad : matrix[(pivotRow, col)] = s.matrix[(row, col)] := by
    dsimp only [matrix]
    simp only [Matrix.getElem_pair_eq_nested]
    rw [Matrix.getElem_rowAdd, ite_eq_left rfl]
    have hcol' : s.matrix[pivotRow][col] = 0 := by
      simpa only [Matrix.getElem_pair_eq_nested] using hcol
    rw [hcol']
    omega
  rcases hc : Hermite.gcdCoeffs matrix[(pivotRow, pivotCol)]
      matrix[(pivotRow, col)] with ⟨x, y, z, w⟩
  have hg := Hermite.gcdCoeffs_pivot matrix[(pivotRow, pivotCol)]
    matrix[(pivotRow, col)]
  rw [hc] at hg
  dsimp only at hg
  rw [hpivot, hbad] at hg
  rw [repair]
  dsimp only
  rw [hc]
  dsimp only
  simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineCols,
    ite_eq_left]
  have hpivot' : (Matrix.rowAdd s.matrix row pivotRow 1)[pivotRow][pivotCol] =
      s.matrix[pivotRow][pivotCol] := by
    simpa only [Matrix.getElem_pair_eq_nested, matrix] using hpivot
  have hbad' : (Matrix.rowAdd s.matrix row pivotRow 1)[pivotRow][col] =
      s.matrix[row][col] := by
    simpa only [Matrix.getElem_pair_eq_nested, matrix] using hbad
  rw [hpivot', hbad']
  simpa only [Matrix.getElem_pair_eq_nested] using hg

private theorem measure_repair_lt (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol col : Fin m)
    (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hrow : s.matrix[(row, pivotCol)] = 0)
    (hcol : s.matrix[(pivotRow, col)] = 0)
    (hmod : s.matrix[(row, col)] % s.matrix[(pivotRow, pivotCol)] ≠ 0) :
    reductionMeasure (repair ops s pivotRow row pivotCol col).matrix pivotRow pivotCol <
      reductionMeasure s.matrix pivotRow pivotCol := by
  apply measure_pivot_lt
  rw [repair_pivot ops s pivotRow row pivotCol col hrow hcol]
  exact gcd_lt_natAbs hp hmod

/-- The local postcondition delivered by one completed Smith pivot. -/
structure Reduced (M : Matrix Int n m) (pivotRow : Fin n)
    (pivotCol : Fin m) : Prop where
  /-- The pivot is normalized to be positive. -/
  pivot_pos : 0 < M[(pivotRow, pivotCol)]
  /-- Entries below the pivot in its column vanish. -/
  column_zero : ∀ row : Fin n, pivotRow.val < row.val → M[(row, pivotCol)] = 0
  /-- Entries right of the pivot in its row vanish. -/
  row_zero : ∀ col : Fin m, pivotCol.val < col.val → M[(pivotRow, col)] = 0
  /-- The pivot divides every entry of the remaining block. -/
  divides : ∀ row : Fin n, ∀ col : Fin m, pivotRow.val < row.val →
    pivotCol.val < col.val → M[(pivotRow, pivotCol)] ∣ M[(row, col)]

private theorem clearColumn_pivot_ne (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hne : pivotRow ≠ row) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(row, pivotCol)] ≠ 0) :
    (clearColumn ops s pivotRow row pivotCol).matrix[(pivotRow, pivotCol)] ≠ 0 := by
  have hs := clearColumn_spec ops s pivotRow row pivotCol hne hb
  dsimp only at hs
  by_cases hdiv : s.matrix[(row, pivotCol)] % s.matrix[(pivotRow, pivotCol)] = 0
  · rw [ite_eq_left hdiv] at hs
    simpa only [hs.1] using hp
  · rw [ite_eq_right hdiv] at hs
    rw [hs.1]
    exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Int.gcd_pos_of_ne_zero_left _ hp))

private theorem clearRow_pivot_ne (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hne : pivotCol ≠ col) (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hb : s.matrix[(pivotRow, col)] ≠ 0) :
    (clearRow ops s pivotRow pivotCol col).matrix[(pivotRow, pivotCol)] ≠ 0 := by
  have hs := clearRow_spec ops s pivotRow pivotCol col hne hb
  dsimp only at hs
  by_cases hdiv : s.matrix[(pivotRow, col)] % s.matrix[(pivotRow, pivotCol)] = 0
  · rw [ite_eq_left hdiv] at hs
    simpa only [hs.1] using hp
  · rw [ite_eq_right hdiv] at hs
    rw [hs.1]
    exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Int.gcd_pos_of_ne_zero_left _ hp))

private theorem repair_pivot_ne (ops : Accumulator α n m)
    (s : Result α n m) (pivotRow row : Fin n) (pivotCol col : Fin m)
    (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hrow : s.matrix[(row, pivotCol)] = 0)
    (hcol : s.matrix[(pivotRow, col)] = 0) :
    (repair ops s pivotRow row pivotCol col).matrix[(pivotRow, pivotCol)] ≠ 0 := by
  rw [repair_pivot ops s pivotRow row pivotCol col hrow hcol]
  exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Int.gcd_pos_of_ne_zero_left _ hp))

private theorem crossCount_negateRow (M : Matrix Int n m)
    (pivotRow : Fin n) (pivotCol : Fin m) :
    crossCount (Matrix.rowScale M pivotRow (-1)) pivotRow pivotCol =
      crossCount M pivotRow pivotCol := by
  unfold crossCount
  congr 1
  · apply List.foldl_add_congr
    intro row _
    by_cases hne : row = pivotRow
    · subst row
      simp
    · simp only [Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_rowScale, ite_eq_right hne]
  · apply List.foldl_add_congr
    intro col _
    simp only [Matrix.getElem_pair_eq_nested]
    rw [Matrix.getElem_rowScale, ite_eq_left rfl, Int.neg_mul, Int.one_mul]
    by_cases hlt : pivotCol.val < col.val
    · by_cases hz : M[pivotRow][col] = 0 <;> simp [hlt]
    · simp [hlt]

private theorem measure_negateRow (M : Matrix Int n m)
    (pivotRow : Fin n) (pivotCol : Fin m) :
    reductionMeasure (Matrix.rowScale M pivotRow (-1)) pivotRow pivotCol =
      reductionMeasure M pivotRow pivotCol := by
  unfold reductionMeasure
  rw [crossCount_negateRow]
  simp only [Matrix.getElem_pair_eq_nested]
  rw [Matrix.getElem_rowScale, ite_eq_left rfl, Int.neg_mul, Int.one_mul, Int.natAbs_neg]

private theorem reduceFuel_reduced (ops : Accumulator α n m)
    (pivotRow : Fin n) (pivotCol : Fin m) (fuel : Nat) (s : Result α n m)
    (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0)
    (hfuel : reductionMeasure s.matrix pivotRow pivotCol < fuel) :
    Reduced (reduceFuel ops pivotRow pivotCol fuel s).matrix pivotRow pivotCol := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
      rw [reduceFuel]
      split
      · rename_i hpzero
        exact (hp hpzero).elim
      · split
        · rename_i row hfind
          have hs := findColumn?_some hfind
          have hne : pivotRow ≠ row := by
            intro heq
            subst row
            omega
          apply ih
          · exact clearColumn_pivot_ne ops s pivotRow row pivotCol hne hp hs.2
          · have hlt := measure_clearColumn_lt ops s pivotRow row pivotCol hs.1 hp hs.2
            omega
        · rename_i hcolumn
          split
          · rename_i col hfind
            have hs := findRow?_some hfind
            have hne : pivotCol ≠ col := by
              intro heq
              subst col
              omega
            apply ih
            · exact clearRow_pivot_ne ops s pivotRow pivotCol col hne hp hs.2
            · have hlt := measure_clearRow_lt ops s pivotRow pivotCol col hs.1 hp hs.2
              omega
          · rename_i hrow
            split
            · rename_i hneg
              let normalized : Result α n m :=
                { s with
                  matrix := Matrix.rowScale s.matrix pivotRow (-1)
                  accumulator := ops.rowNegate s.accumulator pivotRow }
              have hpivot : normalized.matrix[(pivotRow, pivotCol)] =
                  -s.matrix[(pivotRow, pivotCol)] := by
                dsimp only [normalized]
                simp only [Matrix.getElem_pair_eq_nested]
                rw [Matrix.getElem_rowScale, ite_eq_left rfl, Int.neg_mul, Int.one_mul]
              have hp' : normalized.matrix[(pivotRow, pivotCol)] ≠ 0 := by
                rw [hpivot]
                omega
              simp only
              split
              · rename_i hbad
                constructor
                · rw [hpivot]
                  omega
                · intro row hr
                  dsimp only [normalized]
                  simp only [Matrix.getElem_pair_eq_nested]
                  rw [Matrix.getElem_rowScale, ite_eq_right (by
                    intro heq
                    subst row
                    omega)]
                  simpa only [Matrix.getElem_pair_eq_nested] using
                    findColumn?_none hcolumn row hr
                · intro col hc
                  dsimp only [normalized]
                  simp only [Matrix.getElem_pair_eq_nested]
                  rw [Matrix.getElem_rowScale, ite_eq_left rfl]
                  have hz := findRow?_none hrow col hc
                  simp only [Matrix.getElem_pair_eq_nested] at hz
                  rw [hz]
                  omega
                · exact findBad?_none hbad
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hcolumnZero : normalized.matrix[(q.1, pivotCol)] = 0 := by
                  dsimp only [normalized]
                  simp only [Matrix.getElem_pair_eq_nested]
                  rw [Matrix.getElem_rowScale, ite_eq_right (by
                    intro heq
                    have := congrArg Fin.val heq
                    omega)]
                  simpa only [Matrix.getElem_pair_eq_nested] using
                    findColumn?_none hcolumn q.1 hs.1
                have hrowZero : normalized.matrix[(pivotRow, q.2)] = 0 := by
                  dsimp only [normalized]
                  simp only [Matrix.getElem_pair_eq_nested]
                  rw [Matrix.getElem_rowScale, ite_eq_left rfl]
                  have hz := findRow?_none hrow q.2 hs.2.1
                  simp only [Matrix.getElem_pair_eq_nested] at hz
                  rw [hz]
                  omega
                apply ih
                · exact repair_pivot_ne ops normalized pivotRow q.1 pivotCol q.2
                    hp' hcolumnZero hrowZero
                · have hlt := measure_repair_lt ops normalized pivotRow q.1 pivotCol q.2
                    hp' hcolumnZero hrowZero hs.2.2
                  have heq := measure_negateRow s.matrix pivotRow pivotCol
                  dsimp only [normalized] at hlt
                  omega
            · rename_i hnneg
              split
              · rename_i hbad
                constructor
                · omega
                · exact findColumn?_none hcolumn
                · exact findRow?_none hrow
                · exact findBad?_none hbad
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hcolumnZero := findColumn?_none hcolumn q.1 hs.1
                have hrowZero := findRow?_none hrow q.2 hs.2.1
                apply ih
                · exact repair_pivot_ne ops s pivotRow q.1 pivotCol q.2
                    hp hcolumnZero hrowZero
                · have hlt := measure_repair_lt ops s pivotRow q.1 pivotCol q.2
                    hp hcolumnZero hrowZero hs.2.2
                  omega

private theorem reduce_reduced (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow : Fin n) (pivotCol : Fin m)
    (hp : s.matrix[(pivotRow, pivotCol)] ≠ 0) :
    Reduced (reduce ops s pivotRow pivotCol).matrix pivotRow pivotCol := by
  rw [reduce]
  apply reduceFuel_reduced ops pivotRow pivotCol _ s hp
  unfold reductionMeasure
  have hcount := crossCount_le s.matrix pivotRow pivotCol
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

private theorem swapRows_diag (ops : Accumulator α n m) (s : Result α n m)
    (i k : Fin n) : (swapRows ops s i k).diag = s.diag := by
  rw [swapRows]
  split <;> rfl

private theorem swapCols_diag (ops : Accumulator α n m) (s : Result α n m)
    (i k : Fin m) : (swapCols ops s i k).diag = s.diag := by
  rw [swapCols]
  split <;> rfl

private theorem clearColumn_diag (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow row : Fin n) (pivotCol : Fin m) :
    (clearColumn ops s pivotRow row pivotCol).diag = s.diag := by
  simp only [clearColumn]
  split <;> rfl

private theorem clearRow_diag (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow : Fin n) (pivotCol col : Fin m) :
    (clearRow ops s pivotRow pivotCol col).diag = s.diag := by
  simp only [clearRow]
  split <;> rfl

private theorem repair_diag (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow row : Fin n) (pivotCol col : Fin m) :
    (repair ops s pivotRow row pivotCol col).diag = s.diag := by
  simp [repair]

private theorem reduceFuel_diag (ops : Accumulator α n m)
    (pivotRow : Fin n) (pivotCol : Fin m) (fuel : Nat) (s : Result α n m) :
    (reduceFuel ops pivotRow pivotCol fuel s).diag = s.diag := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [reduceFuel]
      split
      · rfl
      · split
        · rw [ih, clearColumn_diag]
        · split
          · rw [ih, clearRow_diag]
          · split
            · simp only
              split
              · rfl
              · rw [ih, repair_diag]
            · split
              · rfl
              · rw [ih, repair_diag]

private theorem reduce_diag (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow : Fin n) (pivotCol : Fin m) :
    (reduce ops s pivotRow pivotCol).diag = s.diag := by
  exact reduceFuel_diag ops pivotRow pivotCol _ s

/-- Invariant of the completed leading block in the outer Smith sweep. -/
structure Prefix (s : Result α n m) : Prop where
  /-- The completed prefix fits within the rows. -/
  length_le_n : s.diag.length ≤ n
  /-- The completed prefix fits within the columns. -/
  length_le_m : s.diag.length ≤ m
  /-- Completed diagonal entries agree with the working matrix. -/
  diagonal : ∀ (i : Nat) (hi : i < s.diag.length),
    s.matrix[((⟨i, Nat.lt_of_lt_of_le hi length_le_n⟩ : Fin n),
      (⟨i, Nat.lt_of_lt_of_le hi length_le_m⟩ : Fin m))] = s.diag[i]'hi
  /-- Every completed row or column is zero away from the diagonal. -/
  offDiagonal : ∀ (row : Fin n) (col : Fin m),
    (row.val < s.diag.length ∨ col.val < s.diag.length) →
      row.val ≠ col.val → s.matrix[(row, col)] = 0
  /-- Completed entries are positive. -/
  positive : ∀ (i : Nat) (hi : i < s.diag.length), 0 < s.diag[i]'hi
  /-- Completed entries form a divisibility chain. -/
  chain : ∀ (i : Nat) (hi : i + 1 < s.diag.length),
    s.diag[i]'(by omega) ∣ s.diag[i + 1]'hi
  /-- Every completed entry divides the unprocessed trailing block. -/
  dividesTail : ∀ (i : Nat) (hi : i < s.diag.length)
    (row : Fin n) (col : Fin m), s.diag.length ≤ row.val →
      s.diag.length ≤ col.val → s.diag[i]'hi ∣ s.matrix[(row, col)]

/-- The empty completed prefix satisfies the sweep invariant. -/
theorem Prefix.initial (A : Matrix Int n m) (acc : α) :
    Prefix ({ matrix := A, diag := [], accumulator := acc } : Result α n m) := by
  constructor
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

private theorem Prefix.transport {s t : Result α n m} (h : Prefix s)
    (hdiag : t.diag = s.diag)
    (hfixed : ∀ (row : Fin n) (col : Fin m),
      (row.val < s.diag.length ∨ col.val < s.diag.length) →
        t.matrix[(row, col)] = s.matrix[(row, col)])
    (htail : ∀ (i : Nat) (hi : i < s.diag.length)
      (row : Fin n) (col : Fin m), s.diag.length ≤ row.val →
        s.diag.length ≤ col.val → s.diag[i]'hi ∣ t.matrix[(row, col)]) :
    Prefix t := by
  refine
    { length_le_n := by simpa only [hdiag] using h.length_le_n
      length_le_m := by simpa only [hdiag] using h.length_le_m
      diagonal := ?_
      offDiagonal := ?_
      positive := ?_
      chain := ?_
      dividesTail := ?_ }
  · intro i hi
    have hi' : i < s.diag.length := by simpa only [hdiag] using hi
    rw [hfixed _ _ (Or.inl hi')]
    simpa only [hdiag] using h.diagonal i hi'
  · intro row col hsmall hne
    have hsmall' : row.val < s.diag.length ∨ col.val < s.diag.length := by
      simpa only [hdiag] using hsmall
    rw [hfixed row col hsmall']
    exact h.offDiagonal row col hsmall' hne
  · intro i hi
    have hi' : i < s.diag.length := by simpa only [hdiag] using hi
    simpa only [hdiag] using h.positive i hi'
  · intro i hi
    have hi' : i + 1 < s.diag.length := by simpa only [hdiag] using hi
    simpa only [hdiag] using h.chain i hi'
  · intro i hi row col hr hc
    have hi' : i < s.diag.length := by simpa only [hdiag] using hi
    have hd := htail i hi' row col (by simpa only [hdiag] using hr)
      (by simpa only [hdiag] using hc)
    simpa only [hdiag] using hd

private theorem swapRows_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (i j : Fin n) (hi : s.diag.length ≤ i.val)
    (hj : s.diag.length ≤ j.val) : Prefix (swapRows ops s i j) := by
  by_cases hij : i = j
  · rw [swapRows, ite_eq_left hij]
    exact h
  · apply h.transport (by rw [swapRows, ite_eq_right hij])
    · intro row col hsmall
      rw [swapRows, ite_eq_right hij]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
      by_cases hrj : row = j
      · subst row
        have hc : col.val < s.diag.length := by omega
        rw [ite_eq_left rfl]
        have hji : j.val ≠ col.val := by omega
        have hii : i.val ≠ col.val := by omega
        have hzj : s.matrix[j][col] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal j col (Or.inr hc) hji
        have hzi : s.matrix[i][col] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal i col (Or.inr hc) hii
        rw [hzi, hzj]
      · rw [ite_eq_right hrj]
        by_cases hri : row = i
        · subst row
          have hc : col.val < s.diag.length := by omega
          rw [ite_eq_left rfl]
          have hijc : i.val ≠ col.val := by omega
          have hjc : j.val ≠ col.val := by omega
          have hzi : s.matrix[i][col] = 0 := by
            simpa only [Matrix.getElem_pair_eq_nested] using
              h.offDiagonal i col (Or.inr hc) hijc
          have hzj : s.matrix[j][col] = 0 := by
            simpa only [Matrix.getElem_pair_eq_nested] using
              h.offDiagonal j col (Or.inr hc) hjc
          rw [hzj, hzi]
        · rw [ite_eq_right hri]
    · intro d hd row col hr hc
      rw [swapRows, ite_eq_right hij]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
      by_cases hrj : row = j
      · rw [ite_eq_left hrj]
        simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd i col hi hc
      · rw [ite_eq_right hrj]
        by_cases hri : row = i
        · rw [ite_eq_left hri]
          simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd j col hj hc
        · rw [ite_eq_right hri]
          simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row col hr hc

private theorem swapCols_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (i j : Fin m) (hi : s.diag.length ≤ i.val)
    (hj : s.diag.length ≤ j.val) : Prefix (swapCols ops s i j) := by
  by_cases hij : i = j
  · rw [swapCols, ite_eq_left hij]
    exact h
  · apply h.transport (by rw [swapCols, ite_eq_right hij])
    · intro row col hsmall
      rw [swapCols, ite_eq_right hij]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_colSwap]
      by_cases hcj : col = j
      · subst col
        have hr : row.val < s.diag.length := by omega
        rw [ite_eq_left rfl]
        have hji : row.val ≠ j.val := by omega
        have hii : row.val ≠ i.val := by omega
        have hzj : s.matrix[row][j] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal row j (Or.inl hr) hji
        have hzi : s.matrix[row][i] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal row i (Or.inl hr) hii
        rw [hzi, hzj]
      · rw [ite_eq_right hcj]
        by_cases hci : col = i
        · subst col
          have hr : row.val < s.diag.length := by omega
          rw [ite_eq_left rfl]
          have hijr : row.val ≠ i.val := by omega
          have hjr : row.val ≠ j.val := by omega
          have hzi : s.matrix[row][i] = 0 := by
            simpa only [Matrix.getElem_pair_eq_nested] using
              h.offDiagonal row i (Or.inl hr) hijr
          have hzj : s.matrix[row][j] = 0 := by
            simpa only [Matrix.getElem_pair_eq_nested] using
              h.offDiagonal row j (Or.inl hr) hjr
          rw [hzj, hzi]
        · rw [ite_eq_right hci]
    · intro d hd row col hr hc
      rw [swapCols, ite_eq_right hij]
      dsimp only
      simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_colSwap]
      by_cases hcj : col = j
      · rw [ite_eq_left hcj]
        simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row i hr hi
      · rw [ite_eq_right hcj]
        by_cases hci : col = i
        · rw [ite_eq_left hci]
          simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row j hr hj
        · rw [ite_eq_right hci]
          simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row col hr hc

private theorem dvd_linear {d x y a b : Int} (hx : d ∣ x) (hy : d ∣ y) :
    d ∣ a * x + b * y :=
  Int.dvd_add (Int.dvd_mul_of_dvd_right (b := a) hx)
    (Int.dvd_mul_of_dvd_right (b := b) hy)

private theorem rowAdd_prefix {s : Result α n m} (h : Prefix s)
    (src dst : Fin n) (c : Int) (acc : α)
    (hsrc : s.diag.length ≤ src.val) (hdst : s.diag.length ≤ dst.val) :
    Prefix ({ s with
      matrix := Matrix.rowAdd s.matrix src dst c
      accumulator := acc } : Result α n m) := by
  apply h.transport (t := { s with
    matrix := Matrix.rowAdd s.matrix src dst c
    accumulator := acc }) rfl
  · intro row col hsmall
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
    by_cases hrd : row = dst
    · subst row
      rw [ite_eq_left rfl]
      have hc : col.val < s.diag.length := by omega
      have hz : s.matrix[src][col] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal src col (Or.inr hc) (by omega)
      rw [hz, Int.mul_zero, Int.add_zero]
    · rw [ite_eq_right hrd]
  · intro d hd row col hr hc
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
    by_cases hrd : row = dst
    · rw [ite_eq_left hrd]
      simpa only [Int.one_mul] using dvd_linear (a := 1) (b := c)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail d hd dst col hdst hc)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail d hd src col hsrc hc)
    · rw [ite_eq_right hrd]
      simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row col hr hc

private theorem colAdd_prefix {s : Result α n m} (h : Prefix s)
    (src dst : Fin m) (c : Int) (acc : α)
    (hsrc : s.diag.length ≤ src.val) (hdst : s.diag.length ≤ dst.val) :
    Prefix ({ s with
      matrix := Matrix.colAdd s.matrix src dst c
      accumulator := acc } : Result α n m) := by
  apply h.transport (t := { s with
    matrix := Matrix.colAdd s.matrix src dst c
    accumulator := acc }) rfl
  · intro row col hsmall
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_colAdd]
    by_cases hcd : col = dst
    · subst col
      rw [ite_eq_left rfl]
      have hr : row.val < s.diag.length := by omega
      have hz : s.matrix[row][src] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal row src (Or.inl hr) (by omega)
      rw [hz, Int.mul_zero, Int.add_zero]
    · rw [ite_eq_right hcd]
  · intro d hd row col hr hc
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_colAdd]
    by_cases hcd : col = dst
    · subst col
      rw [ite_eq_left rfl]
      simpa only [Int.one_mul] using dvd_linear (a := 1) (b := c)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail d hd row dst hr hdst)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail d hd row src hr hsrc)
    · rw [ite_eq_right hcd]
      simpa only [Matrix.getElem_pair_eq_nested] using h.dividesTail d hd row col hr hc

private theorem combineRows_prefix {s : Result α n m} (h : Prefix s)
    (i j : Fin n) (a b c d : Int) (acc : α)
    (hi : s.diag.length ≤ i.val) (hj : s.diag.length ≤ j.val) :
    Prefix ({ s with
      matrix := Hermite.combineRows s.matrix i j a b c d
      accumulator := acc } : Result α n m) := by
  apply h.transport (t := { s with
    matrix := Hermite.combineRows s.matrix i j a b c d
    accumulator := acc }) rfl
  · intro row col hsmall
    simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineRows]
    by_cases hri : row = i
    · subst row
      rw [ite_eq_left rfl]
      have hc : col.val < s.diag.length := by omega
      have hzi : s.matrix[i][col] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal i col (Or.inr hc) (by omega)
      have hzj : s.matrix[j][col] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal j col (Or.inr hc) (by omega)
      simp only [hzi, hzj, Int.mul_zero, Int.zero_add]
    · rw [ite_eq_right hri]
      by_cases hrj : row = j
      · subst row
        rw [ite_eq_left rfl]
        have hc : col.val < s.diag.length := by omega
        have hzi : s.matrix[i][col] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal i col (Or.inr hc) (by omega)
        have hzj : s.matrix[j][col] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal j col (Or.inr hc) (by omega)
        simp only [hzi, hzj, Int.mul_zero, Int.zero_add]
      · rw [ite_eq_right hrj]
  · intro q hq row col hr hc
    simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineRows]
    by_cases hri : row = i
    · rw [ite_eq_left hri]
      exact dvd_linear
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq i col hi hc)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq j col hj hc)
    · rw [ite_eq_right hri]
      by_cases hrj : row = j
      · rw [ite_eq_left hrj]
        exact dvd_linear
          (by simpa only [Matrix.getElem_pair_eq_nested] using
            h.dividesTail q hq i col hi hc)
          (by simpa only [Matrix.getElem_pair_eq_nested] using
            h.dividesTail q hq j col hj hc)
      · rw [ite_eq_right hrj]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq row col hr hc

private theorem combineCols_prefix {s : Result α n m} (h : Prefix s)
    (i j : Fin m) (a b c d : Int) (acc : α)
    (hi : s.diag.length ≤ i.val) (hj : s.diag.length ≤ j.val) :
    Prefix ({ s with
      matrix := Hermite.combineCols s.matrix i j a b c d
      accumulator := acc } : Result α n m) := by
  apply h.transport (t := { s with
    matrix := Hermite.combineCols s.matrix i j a b c d
    accumulator := acc }) rfl
  · intro row col hsmall
    simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineCols]
    by_cases hci : col = i
    · subst col
      rw [ite_eq_left rfl]
      have hr : row.val < s.diag.length := by omega
      have hzi : s.matrix[row][i] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal row i (Or.inl hr) (by omega)
      have hzj : s.matrix[row][j] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal row j (Or.inl hr) (by omega)
      simp only [hzi, hzj, Int.mul_zero, Int.zero_add]
    · rw [ite_eq_right hci]
      by_cases hcj : col = j
      · subst col
        rw [ite_eq_left rfl]
        have hr : row.val < s.diag.length := by omega
        have hzi : s.matrix[row][i] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal row i (Or.inl hr) (by omega)
        have hzj : s.matrix[row][j] = 0 := by
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.offDiagonal row j (Or.inl hr) (by omega)
        simp only [hzi, hzj, Int.mul_zero, Int.zero_add]
      · rw [ite_eq_right hcj]
  · intro q hq row col hr hc
    simp only [Matrix.getElem_pair_eq_nested, Hermite.getElem_combineCols]
    by_cases hci : col = i
    · rw [ite_eq_left hci]
      exact dvd_linear
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq row i hr hi)
        (by simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq row j hr hj)
    · rw [ite_eq_right hci]
      by_cases hcj : col = j
      · rw [ite_eq_left hcj]
        exact dvd_linear
          (by simpa only [Matrix.getElem_pair_eq_nested] using
            h.dividesTail q hq row i hr hi)
          (by simpa only [Matrix.getElem_pair_eq_nested] using
            h.dividesTail q hq row j hr hj)
      · rw [ite_eq_right hcj]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq row col hr hc

private theorem rowScale_prefix {s : Result α n m} (h : Prefix s)
    (i : Fin n) (c : Int) (acc : α) (hi : s.diag.length ≤ i.val) :
    Prefix ({ s with
      matrix := Matrix.rowScale s.matrix i c
      accumulator := acc } : Result α n m) := by
  apply h.transport (t := { s with
    matrix := Matrix.rowScale s.matrix i c
    accumulator := acc }) rfl
  · intro row col hsmall
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
    by_cases hri : row = i
    · subst row
      rw [ite_eq_left rfl]
      have hc : col.val < s.diag.length := by omega
      have hz : s.matrix[i][col] = 0 := by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.offDiagonal i col (Or.inr hc) (by omega)
      rw [hz, Int.mul_zero]
    · rw [ite_eq_right hri]
  · intro q hq row col hr hc
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
    by_cases hri : row = i
    · rw [ite_eq_left hri]
      exact Int.dvd_mul_of_dvd_right (b := c) (by
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.dividesTail q hq i col hi hc)
    · rw [ite_eq_right hri]
      simpa only [Matrix.getElem_pair_eq_nested] using
        h.dividesTail q hq row col hr hc

private theorem clearColumn_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hpivot : s.diag.length ≤ pivotRow.val) (hrow : s.diag.length ≤ row.val) :
    Prefix (clearColumn ops s pivotRow row pivotCol) := by
  simp only [clearColumn]
  split
  · exact rowAdd_prefix h pivotRow row _ _ hpivot hrow
  · exact combineRows_prefix h pivotRow row _ _ _ _ _ hpivot hrow

private theorem clearRow_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hpivot : s.diag.length ≤ pivotCol.val) (hcol : s.diag.length ≤ col.val) :
    Prefix (clearRow ops s pivotRow pivotCol col) := by
  simp only [clearRow]
  split
  · exact colAdd_prefix h pivotCol col _ _ hpivot hcol
  · exact combineCols_prefix h pivotCol col _ _ _ _ _ hpivot hcol

private theorem repair_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (pivotRow row : Fin n) (pivotCol col : Fin m)
    (hpivotRow : s.diag.length ≤ pivotRow.val)
    (hrow : s.diag.length ≤ row.val)
    (hpivotCol : s.diag.length ≤ pivotCol.val)
    (hcol : s.diag.length ≤ col.val) :
    Prefix (repair ops s pivotRow row pivotCol col) := by
  rw [repair]
  let rowAdded : Result α n m :=
    { s with
      matrix := Matrix.rowAdd s.matrix row pivotRow 1
      accumulator := ops.rowAdd s.accumulator row pivotRow 1 }
  have hr := rowAdd_prefix h row pivotRow 1
    (ops.rowAdd s.accumulator row pivotRow 1) hrow hpivotRow
  change Prefix ({ rowAdded with
    matrix := Hermite.combineCols rowAdded.matrix pivotCol col _ _ _ _
    accumulator := ops.colCombine rowAdded.accumulator pivotCol col _ _ _ _ } :
      Result α n m)
  exact combineCols_prefix hr pivotCol col _ _ _ _ _ hpivotCol hcol

private theorem reduceFuel_prefix (ops : Accumulator α n m)
    (pivotRow : Fin n) (pivotCol : Fin m) (fuel : Nat) {s : Result α n m}
    (h : Prefix s) (hpivotRow : s.diag.length ≤ pivotRow.val)
    (hpivotCol : s.diag.length ≤ pivotCol.val) :
    Prefix (reduceFuel ops pivotRow pivotCol fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [reduceFuel]
      split
      · exact h
      · split
        · rename_i row hfind
          have hs := findColumn?_some hfind
          have h' := clearColumn_prefix ops h pivotRow row pivotCol hpivotRow (by omega)
          have hdiag : (clearColumn ops s pivotRow row pivotCol).diag = s.diag := by
            simp only [clearColumn]
            split <;> rfl
          exact ih h' (by rw [hdiag]; exact hpivotRow)
            (by rw [hdiag]; exact hpivotCol)
        · rename_i hcolumn
          split
          · rename_i col hfind
            have hs := findRow?_some hfind
            have h' := clearRow_prefix ops h pivotRow pivotCol col hpivotCol (by omega)
            have hdiag : (clearRow ops s pivotRow pivotCol col).diag = s.diag := by
              simp only [clearRow]
              split <;> rfl
            exact ih h' (by rw [hdiag]; exact hpivotRow)
              (by rw [hdiag]; exact hpivotCol)
          · rename_i hrowSearch
            split
            · have hneg := rowScale_prefix h pivotRow (-1)
                (ops.rowNegate s.accumulator pivotRow) hpivotRow
              simp only
              split
              · exact hneg
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hrepair := repair_prefix ops hneg pivotRow q.1 pivotCol q.2
                  (by simpa using hpivotRow)
                  (by change s.diag.length ≤ q.1.val; omega)
                  (by simpa using hpivotCol)
                  (by change s.diag.length ≤ q.2.val; omega)
                have hdiag : (repair ops
                    { s with
                      matrix := Matrix.rowScale s.matrix pivotRow (-1)
                      accumulator := ops.rowNegate s.accumulator pivotRow }
                    pivotRow q.1 pivotCol q.2).diag = s.diag := by
                  simp [repair]
                exact ih hrepair
                  (by rw [hdiag]; exact hpivotRow)
                  (by rw [hdiag]; exact hpivotCol)
            · split
              · exact h
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hrepair := repair_prefix ops h pivotRow q.1 pivotCol q.2
                  hpivotRow (by omega) hpivotCol (by omega)
                have hdiag : (repair ops s pivotRow q.1 pivotCol q.2).diag = s.diag := by
                  simp [repair]
                exact ih hrepair
                  (by rw [hdiag]; exact hpivotRow)
                  (by rw [hdiag]; exact hpivotCol)

private theorem reduce_prefix (ops : Accumulator α n m) {s : Result α n m}
    (h : Prefix s) (pivotRow : Fin n) (pivotCol : Fin m)
    (hpivotRow : s.diag.length ≤ pivotRow.val)
    (hpivotCol : s.diag.length ≤ pivotCol.val) :
    Prefix (reduce ops s pivotRow pivotCol) := by
  exact reduceFuel_prefix ops pivotRow pivotCol _ h hpivotRow hpivotCol

private theorem Prefix.appendPivot {s : Result α n m} (h : Prefix s)
    (hn : s.diag.length < n) (hm : s.diag.length < m)
    (hreduced : Reduced s.matrix ⟨s.diag.length, hn⟩ ⟨s.diag.length, hm⟩) :
    Prefix ({ s with diag := s.diag ++
      [s.matrix[((⟨s.diag.length, hn⟩ : Fin n),
        (⟨s.diag.length, hm⟩ : Fin m))]] } : Result α n m) := by
  let pivotRow : Fin n := ⟨s.diag.length, hn⟩
  let pivotCol : Fin m := ⟨s.diag.length, hm⟩
  let p := s.matrix[(pivotRow, pivotCol)]
  refine
    { length_le_n := by simp only [List.length_append, List.length_singleton]; omega
      length_le_m := by simp only [List.length_append, List.length_singleton]; omega
      diagonal := ?_
      offDiagonal := ?_
      positive := ?_
      chain := ?_
      dividesTail := ?_ }
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hold : i < s.diag.length
    · have hd := h.diagonal i hold
      rw [List.getElem_append, dite_eq_left hold]
      exact hd
    · have hieq : i = s.diag.length := by omega
      subst i
      simp
  · intro row col hsmall hne
    simp only [List.length_append, List.length_singleton] at hsmall
    by_cases hrow : row.val < s.diag.length
    · exact h.offDiagonal row col (Or.inl hrow) hne
    · by_cases hcol : col.val < s.diag.length
      · exact h.offDiagonal row col (Or.inr hcol) hne
      · have hone : row.val = s.diag.length ∨ col.val = s.diag.length := by omega
        rcases hone with hroweq | hcoleq
        · have hcolgt : s.diag.length < col.val := by omega
          have herow : row = pivotRow := Fin.ext hroweq
          subst row
          have hz := hreduced.row_zero col hcolgt
          simpa only [pivotRow, pivotCol, Matrix.getElem_pair_eq_nested] using hz
        · have hrowgt : s.diag.length < row.val := by omega
          have hecol : col = pivotCol := Fin.ext hcoleq
          subst col
          have hz := hreduced.column_zero row hrowgt
          simpa only [pivotRow, pivotCol, Matrix.getElem_pair_eq_nested] using hz
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hold : i < s.diag.length
    · rw [List.getElem_append, dite_eq_left hold]
      exact h.positive i hold
    · have hieq : i = s.diag.length := by omega
      subst i
      simpa [List.getElem_append, pivotRow, pivotCol, p] using hreduced.pivot_pos
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hold : i + 1 < s.diag.length
    · rw [List.getElem_append, dite_eq_left (by omega), List.getElem_append, dite_eq_left hold]
      exact h.chain i hold
    · have heq : i + 1 = s.diag.length := by omega
      have hiold : i < s.diag.length := by omega
      have hd := h.dividesTail i hiold pivotRow pivotCol (by simp [pivotRow])
        (by simp [pivotCol])
      rw [List.getElem_append, dite_eq_left hiold, List.getElem_append, dite_eq_right hold]
      simpa [heq, pivotRow, pivotCol, p] using hd
  · intro i hi row col hr hc
    simp only [List.length_append, List.length_singleton] at hi hr hc
    by_cases hold : i < s.diag.length
    · have hd := h.dividesTail i hold row col (by omega) (by omega)
      rw [List.getElem_append, dite_eq_left hold]
      exact hd
    · have hieq : i = s.diag.length := by omega
      subst i
      have hd := hreduced.divides row col
        (by dsimp only [pivotRow]; omega) (by dsimp only [pivotCol]; omega)
      simpa [List.getElem_append, pivotRow, pivotCol, p] using hd

private theorem Prefix.matrix_eq_diag {s : Result α n m} (h : Prefix s)
    (htail : ∀ (row : Fin n) (col : Fin m), s.diag.length ≤ row.val →
      s.diag.length ≤ col.val → s.matrix[(row, col)] = 0) :
    s.matrix = diagMatrix s.diagVector n m := by
  apply Matrix.ext_getElem
  intro row col
  by_cases hij : row.val = col.val
  · by_cases hr : row.val < s.diag.length
    · have hm := h.diagonal row.val hr
      simp only [Matrix.getElem_pair_eq_nested] at hm
      rw [Matrix.getElem_diagMatrix, dite_eq_left ⟨hij, hr⟩]
      have hm' : s.matrix[row][col] = s.diag[row.val] := by
        have hrow : (⟨row.val, Nat.lt_of_lt_of_le hr h.length_le_n⟩ : Fin n) = row :=
          Fin.ext rfl
        have hcol : (⟨row.val, Nat.lt_of_lt_of_le hr h.length_le_m⟩ : Fin m) = col :=
          Fin.ext hij
        rw [hrow, hcol] at hm
        exact hm
      rw [hm']
      exact (Result.diagVector_get s ⟨row.val, hr⟩).symm
    · have hz := htail row col (by omega) (by omega)
      simp only [Matrix.getElem_pair_eq_nested] at hz
      rw [hz, Matrix.getElem_diagMatrix]
      simp [hr]
  · have hz : s.matrix[(row, col)] = 0 := by
      by_cases hsmall : row.val < s.diag.length ∨ col.val < s.diag.length
      · exact h.offDiagonal row col hsmall hij
      · exact htail row col (by omega) (by omega)
    simp only [Matrix.getElem_pair_eq_nested] at hz
    rw [hz, Matrix.getElem_diagMatrix]
    simp [hij]

private theorem Prefix.matrix_eq_diag_of_row_full {s : Result α n m}
    (h : Prefix s) (hfull : n ≤ s.diag.length) :
    s.matrix = diagMatrix s.diagVector n m := by
  apply h.matrix_eq_diag
  intro row _ _ _
  omega

private theorem Prefix.matrix_eq_diag_of_col_full {s : Result α n m}
    (h : Prefix s) (hfull : m ≤ s.diag.length) :
    s.matrix = diagMatrix s.diagVector n m := by
  apply h.matrix_eq_diag
  intro _ col _ _
  omega

private theorem swapRows_pivot (ops : Accumulator α n m) (s : Result α n m)
    (target source : Fin n) (col : Fin m) :
    (swapRows ops s target source).matrix[(target, col)] = s.matrix[(source, col)] := by
  by_cases h : target = source
  · subst source
    rw [swapRows, ite_eq_left rfl]
  · rw [swapRows, ite_eq_right h]
    dsimp only
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap, ite_eq_right h]
    simp

private theorem swapCols_pivot (ops : Accumulator α n m) (s : Result α n m)
    (row : Fin n) (target source : Fin m) :
    (swapCols ops s target source).matrix[(row, target)] = s.matrix[(row, source)] := by
  by_cases h : target = source
  · subst source
    rw [swapCols, ite_eq_left rfl]
  · rw [swapCols, ite_eq_right h]
    dsimp only
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_colSwap, ite_eq_right h]
    simp

private theorem moved_pivot (ops : Accumulator α n m) (s : Result α n m)
    (pivotRow sourceRow : Fin n) (pivotCol sourceCol : Fin m) :
    (swapCols ops (swapRows ops s pivotRow sourceRow) pivotCol sourceCol).matrix[
      (pivotRow, pivotCol)] = s.matrix[(sourceRow, sourceCol)] := by
  rw [swapCols_pivot, swapRows_pivot]

/-- Sufficient outer-loop fuel completes a valid prefix and diagonalizes the
working matrix. -/
theorem runFuel_complete (ops : Accumulator α n m) (fuel : Nat)
    {s : Result α n m} (h : Prefix s)
    (hbudget : Nat.min n m ≤ s.diag.length + fuel) :
    let result := runFuel ops fuel s
    Prefix result ∧ result.matrix = diagMatrix result.diagVector n m := by
  induction fuel generalizing s with
  | zero =>
      simp only [runFuel]
      constructor
      · exact h
      · by_cases hnm : n ≤ m
        · apply h.matrix_eq_diag_of_row_full
          have hmin : n.min m = n := Nat.min_eq_left hnm
          omega
        · apply h.matrix_eq_diag_of_col_full
          have hmin : n.min m = m := Nat.min_eq_right (by omega)
          omega
  | succ fuel ih =>
      rw [runFuel]
      split
      · rename_i hn
        split
        · rename_i hm
          split
          · exact ⟨h, h.matrix_eq_diag (findPivot?_none (by assumption))⟩
          · rename_i q hfind
            have hq := findPivot?_some hfind
            let pivotRow : Fin n := ⟨s.diag.length, hn⟩
            let pivotCol : Fin m := ⟨s.diag.length, hm⟩
            let moved := swapCols ops (swapRows ops s pivotRow q.1) pivotCol q.2
            have hpivot : moved.matrix[(pivotRow, pivotCol)] ≠ 0 := by
              dsimp only [moved]
              rw [moved_pivot]
              exact hq.2.2
            have hmovedRows := swapRows_prefix ops h pivotRow q.1 (by simp [pivotRow])
              (by omega)
            have hmoved := swapCols_prefix ops hmovedRows pivotCol q.2
              (by rw [swapRows_diag]; simp [pivotCol])
              (by rw [swapRows_diag]; omega)
            let reduced := reduce ops moved pivotRow pivotCol
            have hprefix := reduce_prefix ops hmoved pivotRow pivotCol
              (by simp [swapCols_diag, swapRows_diag, pivotRow])
              (by simp [swapCols_diag, swapRows_diag, pivotCol])
            have hreduced := reduce_reduced ops moved pivotRow pivotCol hpivot
            simp only
            split
            · rename_i hpzero
              exact (Int.ne_of_gt hreduced.pivot_pos hpzero).elim
            · rename_i hpnonzero
              have hdiag : reduced.diag = s.diag := by
                simp [reduced, moved, reduce_diag, swapCols_diag, swapRows_diag]
              have hn' : reduced.diag.length < n := by rw [hdiag]; exact hn
              have hm' : reduced.diag.length < m := by rw [hdiag]; exact hm
              have hrow : (⟨reduced.diag.length, hn'⟩ : Fin n) = pivotRow :=
                Fin.ext (by simp [pivotRow, hdiag])
              have hcol : (⟨reduced.diag.length, hm'⟩ : Fin m) = pivotCol :=
                Fin.ext (by simp [pivotCol, hdiag])
              have hreduced' : Reduced reduced.matrix
                  ⟨reduced.diag.length, hn'⟩ ⟨reduced.diag.length, hm'⟩ := by
                rw [hrow, hcol]
                exact hreduced
              have happend := hprefix.appendPivot hn' hm' hreduced'
              have hnext : Nat.min n m ≤
                  (reduced.diag ++ [reduced.matrix[((⟨reduced.diag.length, hn'⟩ : Fin n),
                    (⟨reduced.diag.length, hm'⟩ : Fin m))]]).length + fuel := by
                simp only [List.length_append, List.length_singleton]
                rw [hdiag]
                omega
              have hcomplete := ih happend hnext
              rw [hrow, hcol] at hcomplete
              rw [ite_eq_right hpnonzero]
              simpa [reduced, hpnonzero] using hcomplete
        · exact ⟨h, h.matrix_eq_diag_of_col_full (by omega)⟩
      · exact ⟨h, h.matrix_eq_diag_of_row_full (by omega)⟩

/-- The outer loop can append at most one invariant factor per unit of fuel. -/
theorem runFuel_diag_le (ops : Accumulator α n m) (fuel : Nat) (s : Result α n m) :
    (runFuel ops fuel s).diag.length ≤ s.diag.length + fuel := by
  induction fuel generalizing s with
  | zero => simp [runFuel]
  | succ fuel ih =>
      simp only [runFuel]
      split <;> try split <;> try split <;> try split
      all_goals try simp_all only [reduce_diag, swapCols_diag, swapRows_diag]
      all_goals try omega
      all_goals
        apply Nat.le_trans (ih _)
        simp only [List.length_append, List.length_singleton]
        omega

/-- Results agree on the working matrix and completed diagonal whenever their
companion accumulators are ignored. -/
structure Same (s : Result α n m) (t : Result β n m) : Prop where
  /-- The erased working matrices agree. -/
  matrix : s.matrix = t.matrix
  /-- The erased completed diagonals agree. -/
  diag : s.diag = t.diag

private theorem swapRows_same (ops : Accumulator α n m) (ops' : Accumulator β n m)
    {s : Result α n m} {t : Result β n m} (h : Same s t) (i k : Fin n) :
    Same (swapRows ops s i k) (swapRows ops' t i k) := by
  simp only [swapRows]
  split
  · exact h
  · constructor
    · exact congrArg (fun M => Matrix.rowSwap M i k) h.matrix
    · exact h.diag

private theorem swapCols_same (ops : Accumulator α n m) (ops' : Accumulator β n m)
    {s : Result α n m} {t : Result β n m} (h : Same s t) (i k : Fin m) :
    Same (swapCols ops s i k) (swapCols ops' t i k) := by
  simp only [swapCols]
  split
  · exact h
  · constructor
    · exact congrArg (fun M => Matrix.colSwap M i k) h.matrix
    · exact h.diag

private theorem clearColumn_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) {s : Result α n m} {t : Result β n m}
    (h : Same s t) (pivotRow row : Fin n) (pivotCol : Fin m) :
    Same (clearColumn ops s pivotRow row pivotCol)
      (clearColumn ops' t pivotRow row pivotCol) := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  rw [clearColumn, clearColumn]
  split <;> exact ⟨rfl, rfl⟩

private theorem clearRow_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) {s : Result α n m} {t : Result β n m}
    (h : Same s t) (pivotRow : Fin n) (pivotCol col : Fin m) :
    Same (clearRow ops s pivotRow pivotCol col)
      (clearRow ops' t pivotRow pivotCol col) := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  rw [clearRow, clearRow]
  split <;> exact ⟨rfl, rfl⟩

private theorem repair_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) {s : Result α n m} {t : Result β n m}
    (h : Same s t) (pivotRow row : Fin n) (pivotCol col : Fin m) :
    Same (repair ops s pivotRow row pivotCol col)
      (repair ops' t pivotRow row pivotCol col) := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

private theorem reduceFuel_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) (pivotRow : Fin n) (pivotCol : Fin m)
    (fuel : Nat) {s : Result α n m} {t : Result β n m} (h : Same s t) :
    Same (reduceFuel ops pivotRow pivotCol fuel s)
      (reduceFuel ops' pivotRow pivotCol fuel t) := by
  induction fuel generalizing s t with
  | zero => exact h
  | succ fuel ih =>
      rcases s with ⟨matrix, diag, acc⟩
      rcases t with ⟨matrix', diag', acc'⟩
      rcases h with ⟨rfl, rfl⟩
      rw [reduceFuel, reduceFuel]
      by_cases hp : matrix[(pivotRow, pivotCol)] = 0
      · rw [ite_eq_left hp, ite_eq_left hp]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hp, ite_eq_right hp]
        cases hc : findColumn? matrix pivotRow pivotCol with
        | some row =>
            simp only []
            exact ih (clearColumn_same ops ops' ⟨rfl, rfl⟩ pivotRow row pivotCol)
        | none =>
            simp only []
            cases hr : findRow? matrix pivotRow pivotCol with
            | some col =>
                simp only []
                exact ih (clearRow_same ops ops' ⟨rfl, rfl⟩ pivotRow pivotCol col)
            | none =>
                simp only []
                by_cases hn : matrix[(pivotRow, pivotCol)] < 0
                · rw [ite_eq_left hn, ite_eq_left hn]
                  cases hb : findBad? (Matrix.rowScale matrix pivotRow (-1))
                      pivotRow pivotCol
                      (Matrix.rowScale matrix pivotRow (-1))[(pivotRow, pivotCol)] with
                  | none => simp only []; exact ⟨rfl, rfl⟩
                  | some q =>
                      simp only []
                      exact ih (repair_same ops ops' ⟨rfl, rfl⟩
                        pivotRow q.1 pivotCol q.2)
                · rw [ite_eq_right hn, ite_eq_right hn]
                  cases hb : findBad? matrix pivotRow pivotCol
                      matrix[(pivotRow, pivotCol)] with
                  | none => simp only []; exact ⟨rfl, rfl⟩
                  | some q =>
                      simp only []
                      exact ih (repair_same ops ops' ⟨rfl, rfl⟩
                        pivotRow q.1 pivotCol q.2)

private theorem reduce_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) {s : Result α n m} {t : Result β n m}
    (h : Same s t) (pivotRow : Fin n) (pivotCol : Fin m) :
    Same (reduce ops s pivotRow pivotCol) (reduce ops' t pivotRow pivotCol) := by
  rw [reduce, reduce]
  rw [h.matrix]
  exact reduceFuel_same ops ops' pivotRow pivotCol _ h

private theorem runFuel_same (ops : Accumulator α n m)
    (ops' : Accumulator β n m) (fuel : Nat)
    {s : Result α n m} {t : Result β n m} (h : Same s t) :
    Same (runFuel ops fuel s) (runFuel ops' fuel t) := by
  induction fuel generalizing s t with
  | zero => exact h
  | succ fuel ih =>
      rcases s with ⟨matrix, diag, acc⟩
      rcases t with ⟨matrix', diag', acc'⟩
      rcases h with ⟨rfl, rfl⟩
      rw [runFuel, runFuel]
      by_cases hn : diag.length < n
      · rw [dite_eq_left hn, dite_eq_left hn]
        by_cases hm : diag.length < m
        · rw [dite_eq_left hm, dite_eq_left hm]
          cases hp : findPivot? matrix diag.length with
          | none => simp only []; exact ⟨rfl, rfl⟩
          | some q =>
              simp only []
              let pivotRow : Fin n := ⟨diag.length, hn⟩
              let pivotCol : Fin m := ⟨diag.length, hm⟩
              have hmoved := swapCols_same ops ops'
                (swapRows_same ops ops' (⟨rfl, rfl⟩ :
                  Same ({ matrix := matrix, diag := diag, accumulator := acc } : Result α n m)
                    { matrix := matrix, diag := diag, accumulator := acc' }) pivotRow q.1)
                pivotCol q.2
              have hreduced := reduce_same ops ops' hmoved pivotRow pivotCol
              by_cases hz : (reduce ops
                  (swapCols ops (swapRows ops
                    ({ matrix := matrix, diag := diag, accumulator := acc } : Result α n m)
                    pivotRow q.1) pivotCol q.2) pivotRow pivotCol).matrix[(pivotRow, pivotCol)] = 0
              · rw [ite_eq_left hz]
                rw [hreduced.matrix] at hz
                rw [ite_eq_left hz]
                exact hreduced
              · rw [ite_eq_right hz]
                have hz' : (reduce ops'
                    (swapCols ops' (swapRows ops'
                      ({ matrix := matrix, diag := diag, accumulator := acc' } : Result β n m)
                      pivotRow q.1) pivotCol q.2) pivotRow pivotCol).matrix[(pivotRow, pivotCol)] ≠ 0 := by
                  rw [← hreduced.matrix]
                  exact hz
                rw [ite_eq_right hz']
                have hpivot := congrArg (fun M : Matrix Int n m => M[(pivotRow, pivotCol)])
                  hreduced.matrix
                have hdiag :
                    (reduce ops
                      (swapCols ops (swapRows ops
                        ({ matrix := matrix, diag := diag, accumulator := acc } : Result α n m)
                        pivotRow q.1) pivotCol q.2) pivotRow pivotCol).diag ++
                        [(reduce ops
                          (swapCols ops (swapRows ops
                            ({ matrix := matrix, diag := diag, accumulator := acc } : Result α n m)
                            pivotRow q.1) pivotCol q.2) pivotRow pivotCol).matrix[(pivotRow, pivotCol)]] =
                    (reduce ops'
                      (swapCols ops' (swapRows ops'
                        ({ matrix := matrix, diag := diag, accumulator := acc' } : Result β n m)
                        pivotRow q.1) pivotCol q.2) pivotRow pivotCol).diag ++
                        [(reduce ops'
                          (swapCols ops' (swapRows ops'
                            ({ matrix := matrix, diag := diag, accumulator := acc' } : Result β n m)
                            pivotRow q.1) pivotCol q.2) pivotRow pivotCol).matrix[(pivotRow, pivotCol)]] := by
                  rw [hreduced.diag, hpivot]
                exact ih ⟨hreduced.matrix, hdiag⟩
        · rw [dite_eq_right hm, dite_eq_right hm]
          exact ⟨rfl, rfl⟩
      · rw [dite_eq_right hn, dite_eq_right hn]
        exact ⟨rfl, rfl⟩

/-- Every companion accumulator follows the same working-matrix and diagonal
schedule. -/
theorem run_same (ops : Accumulator α n m) (ops' : Accumulator β n m)
    (A : Matrix Int n m) : Same (run ops A) (run ops' A) := by
  apply runFuel_same
  exact ⟨rfl, rfl⟩

end Smith
end Hex.Matrix
