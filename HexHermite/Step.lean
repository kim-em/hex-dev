/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith
public import HexMatrix.Elementary

public section

/-!
Elementary two-row Hermite updates and accumulator operations.

The working matrix and every requested certificate follow the same schedule.
The form-only accumulator is `Unit`, so that path allocates no transform.
-/

namespace Hex.Matrix.Hermite

/-- Replace rows `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineRows (M : Matrix Int n m) (i k : Fin n)
    (a b c d : Int) : Matrix Int n m :=
  Matrix.ofFn fun r j =>
    if r = i then a * M[(i, j)] + b * M[(k, j)]
    else if r = k then c * M[(i, j)] + d * M[(k, j)]
    else M[(r, j)]

/-- Replace columns `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineCols (M : Matrix Int n n) (i k : Fin n)
    (a b c d : Int) : Matrix Int n n :=
  Matrix.ofFn fun r j =>
    if j = i then a * M[(r, i)] + b * M[(r, k)]
    else if j = k then c * M[(r, i)] + d * M[(r, k)]
    else M[(r, j)]

/-- Operations performed on a companion accumulator by the Hermite sweep. -/
structure Accumulator (α : Type) (n : Nat) where
  init : α
  swap : α → Fin n → Fin n → α
  combine : α → Fin n → Fin n → Int → Int → Int → Int → α
  negate : α → Fin n → α
  add : α → Fin n → Fin n → Int → α

/-- The form-only accumulator. -/
@[expose]
def formAccumulator (n : Nat) : Accumulator Unit n where
  init := ()
  swap acc _ _ := acc
  combine acc _ _ _ _ _ _ := acc
  negate acc _ := acc
  add acc _ _ _ := acc

/-- Accumulator for the left transform `U`. -/
@[expose]
def transformAccumulator (n : Nat) : Accumulator (Matrix Int n n) n where
  init := Matrix.identity n
  swap U i k := Matrix.rowSwap U i k
  combine U i k a b c d := combineRows U i k a b c d
  negate U i := Matrix.rowScale U i (-1)
  add U src dst c := Matrix.rowAdd U src dst c

/-- Transform and explicitly accumulated inverse transform. -/
structure TransformPair (n : Nat) where
  transform : Matrix Int n n
  inverse : Matrix Int n n

/-- Accumulator for `(U, W)` with `W = U⁻¹`. -/
@[expose]
def inverseAccumulator (n : Nat) : Accumulator (TransformPair n) n where
  init := ⟨Matrix.identity n, Matrix.identity n⟩
  swap acc i k :=
    ⟨Matrix.rowSwap acc.transform i k, Matrix.colSwap acc.inverse i k⟩
  combine acc i k a b c d :=
    -- The caller supplies `[[a,b],[c,d]]` with determinant one. Its inverse is
    -- `[[d,-b],[-c,a]]`, and right multiplication updates columns.
    ⟨combineRows acc.transform i k a b c d,
      combineCols acc.inverse i k d (-c) (-b) a⟩
  negate acc i :=
    ⟨Matrix.rowScale acc.transform i (-1), Matrix.colScale acc.inverse i (-1)⟩
  add acc src dst c :=
    ⟨Matrix.rowAdd acc.transform src dst c,
      Matrix.colAdd acc.inverse dst src (-c)⟩

/-- Extended-GCD elimination of the entry in row `k`, using pivot row `i`.
The four returned coefficients form a determinant-one two-row update. -/
@[expose]
def gcdCoeffs (a b : Int) : Int × Int × Int × Int :=
  let (g, s, t) := HexArith.Int.extGcd a b
  let g' : Int := Int.ofNat g
  let qa := HexArith.Int.exactDiv a g'
  let qb := HexArith.Int.exactDiv b g'
  (s, t, -qb, qa)

end Hex.Matrix.Hermite
