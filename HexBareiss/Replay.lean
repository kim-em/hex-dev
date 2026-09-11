/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss.Bareiss

public section

/-!
A kernel-evaluable restatement of the row-pivoted Bareiss loop.

`stepMatrixWith` updates rows through core `Vector` operations whose bodies
are not exposed across module boundaries, so a kernel `decide` on
`bareissWith` gets stuck in any importing `module` file.  `bareissReplay`
runs the same loop with the elimination step written through `Matrix.ofFn`,
and `bareissWith_eq_replay` transports a replayed value back to the
executable determinant.  Proof-producing frontends replay this form.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} {n : Nat}

/-- The Bareiss elimination step through `ofFn`: the `stepMatrixWith_eq_ofFn`
form as a definition the kernel evaluates. -/
@[expose]
def stepMatrixReplay [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) : Matrix R n n :=
  Matrix.ofFn fun i j =>
    if hkij : k < i.val ∧ k < j.val then
      let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
      let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
      quot (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
    else if k < i.val ∧ j.val = k then
      0
    else
      M[(i, j)]

/-- The replay step is the executable step. -/
theorem stepMatrixReplay_eq [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    stepMatrixReplay quot M k pivot prevPivot = stepMatrixWith quot M k pivot prevPivot :=
  (stepMatrixWith_eq_ofFn quot M k pivot prevPivot).symm

section Loop

variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]

/-- The row-pivoted Bareiss loop with the replay step. -/
@[expose]
def pivotLoopReplay (quot : R → R → R) (fuel : Nat)
    (state : BareissState R n) : BareissState R n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[(k, k)] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[(k, k)]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixReplay quot M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoopReplay quot fuel next
      else
        state

omit [One R] [Neg R] in
/-- The replay loop is the executable loop. -/
theorem pivotLoopReplay_eq (quot : R → R → R) (fuel : Nat) (state : BareissState R n) :
    pivotLoopReplay quot fuel state = pivotLoopWith quot fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [pivotLoopReplay, pivotLoopWith]
      simp only [stepMatrixReplay_eq, ih]
      rfl

/-- The row-pivoted Bareiss determinant in kernel-evaluable form. -/
@[expose]
def bareissReplay (quot : R → R → R) (M : Matrix R n n) : R :=
  (finish (pivotLoopReplay quot n (noPivotInitialState M))).det

/-- The executable determinant is its replay. -/
theorem bareissWith_eq_replay (quot : R → R → R) (M : Matrix R n n) :
    bareissWith quot M = bareissReplay quot M := by
  rw [bareissWith_eq_bareissDataWith_det, bareissDataWith_eq_finish_pivotLoopWith,
    bareissReplay, pivotLoopReplay_eq]

end Loop

end Hex.Matrix
