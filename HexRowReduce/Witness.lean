/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRowReduce.Kernel
public import HexRowReduce.Solve
import all HexRowReduce.Pivot

public section

namespace Hex.Matrix

namespace Retained

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}

/-- Carry the inverse transform alongside the existing Gauss-Jordan steps.
The state projection uses exactly the ordinary elimination operation. -/
def loop (col fuel : Nat) (state : RowReduceState F n m) (W : Matrix F n n) :
    RowReduceState F n m × Matrix F n n :=
  match fuel with
  | 0 => (state, W)
  | fuel + 1 =>
    if hRow : state.row < n then
      if hCol : col < m then
        let colFin : Fin m := ⟨col, hCol⟩
        match findPivot? state.echelon colFin state.row with
        | none => loop (col + 1) fuel state W
        | some pivot =>
          let target : Fin n := ⟨state.row, hRow⟩
          let swappedEchelon := rowSwap state.echelon target pivot
          let swappedTransform := rowSwap state.transform target pivot
          let pivotVal := swappedEchelon[(target, colFin)]
          let scaledEchelon := rowScale swappedEchelon target pivotVal⁻¹
          let scaledTransform := rowScale swappedTransform target pivotVal⁻¹
          let eliminated := eliminateColumn scaledEchelon scaledTransform target colFin
          let inverse := (List.finRange n).foldl (fun V j =>
            if j = target then V else
              let coeff := scaledEchelon[(j, colFin)]
              if coeff = 0 then V else colAdd V j target coeff)
            (colScale (colSwap W target pivot) target pivotVal)
          loop (col + 1) fuel
            { row := state.row + 1, echelon := eliminated.1,
              transform := eliminated.2, pivots := state.pivots.concat colFin } inverse
      else (state, W)
    else (state, W)

/-- Retaining inverse operations leaves the executable RREF unchanged. -/
theorem loop_fst (col fuel : Nat) (state : RowReduceState F n m) (W : Matrix F n n) :
    (loop col fuel state W).1 = rowReduceLoop col fuel state := by
  induction fuel generalizing col state W with
  | zero => rfl
  | succ fuel ih =>
    simp only [loop, rowReduceLoop]
    split
    · split
      · split <;> simp_all only
      · rfl
    · rfl

/-- Package the ordinary final state without recomputing it. -/
def data (state : RowReduceState F n m) : RowEchelonData F n m :=
  ⟨state.pivots.length, state.echelon, state.transform,
    ⟨state.pivots.toArray, by simp⟩⟩

/-- One reduction, retaining the inverse transform for a complete certificate. -/
def reduce (A : Matrix F n m) : RowEchelonData F n m × Matrix F n n :=
  let final := loop 0 m
    { row := 0, echelon := A, transform := Matrix.identity n, pivots := [] }
    (Matrix.identity n)
  (data final.1, final.2)

theorem reduce_fst (A : Matrix F n m) : (reduce A).1 = rowReduce A := by
  change data (loop 0 m _ _).1 = data (rowReduceLoop 0 m _)
  rw [loop_fst]

end Retained

open Lists

/-- Produce either an inverse or a nonzero nullspace column from one RREF. -/
def inverseWitness {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (toRat : F → Rat) {n : Nat} (A : Matrix F n n) : InverseWitness :=
  let a := ScaledRows.encode ((rowLists A).map (List.map toRat))
  let D := rowReduce A
  let E := rowReduce_isRowReduced A
  if h : D.rank = n then .invertible a (ScaledRows.encode ((rowLists D.transform).map (List.map toRat)))
  else
    have hr : D.rank ≤ n := E.rank_le_n
    let k : Fin (n - D.rank) := ⟨0, by omega⟩
    .singular a (Scaled.encode ((E.nullspace.get k).toList.map toRat)) (E.freeCols.get k).val

/-- Produce complete affine data or a separator, retaining the inverse transform
without repeating elimination. The solving step is shared with `solve`. -/
def solveWitness {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (toRat : F → Rat) {n m : Nat} (A : Matrix F n m) (b : Vector F n) : SolveWitness :=
  let retained := Retained.reduce A
  let D := retained.1
  have E : IsRowReduced A D := by
    rw [show D = rowReduce A from Retained.reduce_fst A]
    exact rowReduce_isRowReduced A
  let a := ScaledRows.encode ((rowLists A).map (List.map toRat))
  let rhs := Scaled.encode (b.toList.map toRat)
  match solveFrom E b with
  | .error y => .inconsistent a rhs (Scaled.encode (y.toList.map toRat))
  | .ok (x, N) => .consistent a rhs {
      reduced := ScaledRows.encode ((rowLists D.echelon).map (List.map toRat))
      transform := ScaledRows.encode ((rowLists D.transform).map (List.map toRat))
      inverse := ScaledRows.encode ((rowLists retained.2).map (List.map toRat))
      rank := D.rank
      pivots := D.pivotCols.toList.map Fin.val
      free := E.freeCols.toList.map Fin.val
      value := Scaled.encode (x.toList.map toRat)
      nullity := m - D.rank
      basis := ScaledRows.encode ((rowLists N).map (List.map toRat)) }

end Hex.Matrix
