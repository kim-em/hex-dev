/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.MatrixAlgebra

public section

/-!
The Winograd seven-product schedule identity.

Strassen's algorithm computes a 2×2 block product with seven block
multiplications instead of eight. Winograd's schedule for those seven products
uses fifteen block additions and subtractions. This file proves the schedule
correct: the four result blocks it assembles equal the four blocks of the naive
2×2 block product `mul`.

The schedule is transcribed from `HexMatrix/SPEC/hex-matrix.md` §
"The Winograd schedule":

    S₁ = A₂₁ + A₂₂    T₁ = B₁₂ − B₁₁
    S₂ = S₁ − A₁₁     T₂ = B₂₂ − T₁
    S₃ = A₁₁ − A₂₁    T₃ = B₂₂ − B₁₂
    S₄ = A₁₂ − S₂     T₄ = T₂ − B₂₁

    P₁ = A₁₁ · B₁₁    P₅ = S₁ · T₁
    P₂ = A₁₂ · B₂₁    P₆ = S₂ · T₂
    P₃ = S₄ · B₂₂     P₇ = S₃ · T₃
    P₄ = A₂₂ · T₄

    U₁ = P₁ + P₂      U₅ = U₄ + P₃
    U₂ = P₁ + P₆      U₆ = U₃ − P₄
    U₃ = U₂ + P₇      U₇ = U₃ + P₅
    U₄ = U₂ + P₅

with output blocks `C₁₁ = U₁`, `C₁₂ = U₅`, `C₂₁ = U₆`, `C₂₂ = U₇`.

The blocks share uniform dimensions: the four `A`-blocks are `Matrix R n m` and
the four `B`-blocks are `Matrix R m k`. The heterogeneous split the SPEC's block
partition wants (`Aᵢⱼ` of possibly different shapes) does *not* typecheck: the
operand sum `S₁ = A₂₁ + A₂₂` adds two `A`-blocks, forcing their shapes to agree,
and likewise for `T₁ = B₁₂ − B₁₁`. This matches the SPEC's own observation that
the balanced schedule requires every dimension split exactly in half (equal
quadrants), not `⌊n/2⌋`/`⌈n/2⌉`.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-- The Winograd seven-product schedule over eight blocks of a 2×2 product.

The eight base blocks are the structure parameters; the fifteen operand and
result sums `S₁…S₄`, `T₁…T₄`, `U₁…U₇` and the seven products `P₁…P₇` are fields,
each pinned to the schedule by a defining equation. A consumer (the `mulStrassen`
correctness proof) instantiates the fields with its recursively-computed
intermediates and discharges the equations, then reads off the four output-block
identities `c11`, `c12`, `c21`, `c22`. -/
structure Winograd [Lean.Grind.Ring R]
    (A₁₁ A₁₂ A₂₁ A₂₂ : Matrix R n m) (B₁₁ B₁₂ B₂₁ B₂₂ : Matrix R m k) where
  /-- `S₁ = A₂₁ + A₂₂`. -/ S₁ : Matrix R n m
  /-- `S₂ = S₁ − A₁₁`. -/ S₂ : Matrix R n m
  /-- `S₃ = A₁₁ − A₂₁`. -/ S₃ : Matrix R n m
  /-- `S₄ = A₁₂ − S₂`. -/ S₄ : Matrix R n m
  /-- `T₁ = B₁₂ − B₁₁`. -/ T₁ : Matrix R m k
  /-- `T₂ = B₂₂ − T₁`. -/ T₂ : Matrix R m k
  /-- `T₃ = B₂₂ − B₁₂`. -/ T₃ : Matrix R m k
  /-- `T₄ = T₂ − B₂₁`. -/ T₄ : Matrix R m k
  /-- `P₁ = A₁₁ · B₁₁`. -/ P₁ : Matrix R n k
  /-- `P₂ = A₁₂ · B₂₁`. -/ P₂ : Matrix R n k
  /-- `P₃ = S₄ · B₂₂`. -/ P₃ : Matrix R n k
  /-- `P₄ = A₂₂ · T₄`. -/ P₄ : Matrix R n k
  /-- `P₅ = S₁ · T₁`. -/ P₅ : Matrix R n k
  /-- `P₆ = S₂ · T₂`. -/ P₆ : Matrix R n k
  /-- `P₇ = S₃ · T₃`. -/ P₇ : Matrix R n k
  /-- `U₁ = P₁ + P₂` (output block `C₁₁`). -/ U₁ : Matrix R n k
  /-- `U₂ = P₁ + P₆`. -/ U₂ : Matrix R n k
  /-- `U₃ = U₂ + P₇`. -/ U₃ : Matrix R n k
  /-- `U₄ = U₂ + P₅`. -/ U₄ : Matrix R n k
  /-- `U₅ = U₄ + P₃` (output block `C₁₂`). -/ U₅ : Matrix R n k
  /-- `U₆ = U₃ − P₄` (output block `C₂₁`). -/ U₆ : Matrix R n k
  /-- `U₇ = U₃ + P₅` (output block `C₂₂`). -/ U₇ : Matrix R n k
  hS₁ : S₁ = A₂₁ + A₂₂
  hS₂ : S₂ = S₁ - A₁₁
  hS₃ : S₃ = A₁₁ - A₂₁
  hS₄ : S₄ = A₁₂ - S₂
  hT₁ : T₁ = B₁₂ - B₁₁
  hT₂ : T₂ = B₂₂ - T₁
  hT₃ : T₃ = B₂₂ - B₁₂
  hT₄ : T₄ = T₂ - B₂₁
  hP₁ : P₁ = A₁₁ * B₁₁
  hP₂ : P₂ = A₁₂ * B₂₁
  hP₃ : P₃ = S₄ * B₂₂
  hP₄ : P₄ = A₂₂ * T₄
  hP₅ : P₅ = S₁ * T₁
  hP₆ : P₆ = S₂ * T₂
  hP₇ : P₇ = S₃ * T₃
  hU₁ : U₁ = P₁ + P₂
  hU₂ : U₂ = P₁ + P₆
  hU₃ : U₃ = U₂ + P₇
  hU₄ : U₄ = U₂ + P₅
  hU₅ : U₅ = U₄ + P₃
  hU₆ : U₆ = U₃ - P₄
  hU₇ : U₇ = U₃ + P₅

namespace Winograd

variable [Lean.Grind.Ring R]
  {A₁₁ A₁₂ A₂₁ A₂₂ : Matrix R n m} {B₁₁ B₁₂ B₂₁ B₂₂ : Matrix R m k}

/-- Output block `C₁₁ = U₁` of the Winograd schedule equals `A₁₁·B₁₁ + A₁₂·B₂₁`. -/
theorem c11 (w : Winograd A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂) :
    w.U₁ = A₁₁ * B₁₁ + A₁₂ * B₂₁ := by
  rw [w.hU₁, w.hP₁, w.hP₂]

/-- Output block `C₁₂ = U₅` of the Winograd schedule equals `A₁₁·B₁₂ + A₁₂·B₂₂`. -/
theorem c12 (w : Winograd A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂) :
    w.U₅ = A₁₁ * B₁₂ + A₁₂ * B₂₂ := by
  rw [w.hU₅, w.hU₄, w.hU₂, w.hP₃, w.hP₅, w.hP₆, w.hP₁, w.hS₄, w.hS₂, w.hS₁, w.hT₂, w.hT₁]
  apply ext_getElem
  intro i j
  simp only [getElem_add, getElem_mul, row_add, row_sub, col_sub,
    Vector.dotProduct_add_left, Vector.dotProduct_sub_left, Vector.dotProduct_sub_right]
  grind

/-- Output block `C₂₁ = U₆` of the Winograd schedule equals `A₂₁·B₁₁ + A₂₂·B₂₁`. -/
theorem c21 (w : Winograd A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂) :
    w.U₆ = A₂₁ * B₁₁ + A₂₂ * B₂₁ := by
  rw [w.hU₆, w.hU₃, w.hU₂, w.hP₄, w.hP₇, w.hP₆, w.hP₁, w.hT₄, w.hT₃, w.hT₂, w.hT₁,
    w.hS₃, w.hS₂, w.hS₁]
  apply ext_getElem
  intro i j
  simp only [getElem_add, getElem_sub, getElem_mul, row_add, row_sub, col_sub,
    Vector.dotProduct_add_left, Vector.dotProduct_sub_left, Vector.dotProduct_sub_right]
  grind

/-- Output block `C₂₂ = U₇` of the Winograd schedule equals `A₂₁·B₁₂ + A₂₂·B₂₂`. -/
theorem c22 (w : Winograd A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂) :
    w.U₇ = A₂₁ * B₁₂ + A₂₂ * B₂₂ := by
  rw [w.hU₇, w.hU₃, w.hU₂, w.hP₅, w.hP₇, w.hP₆, w.hP₁, w.hT₃, w.hT₂, w.hT₁,
    w.hS₃, w.hS₂, w.hS₁]
  apply ext_getElem
  intro i j
  simp only [getElem_add, getElem_mul, row_add, row_sub, col_sub,
    Vector.dotProduct_add_left, Vector.dotProduct_sub_left, Vector.dotProduct_sub_right]
  grind

end Winograd

end Matrix

end Hex
