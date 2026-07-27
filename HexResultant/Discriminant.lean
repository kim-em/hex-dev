/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Subresultant
public meta import HexResultant.Subresultant
public meta import HexPoly.Dense
public meta import HexPoly.Euclid.DivGcd
public meta import HexPoly.Operations

public section

/-!
Executable discriminants over exact coefficient structures.

Positive-degree polynomials use the standard signed resultant quotient. The
zero and constant cases are fixed at one, matching the default-formal-degree
convention used by `resultant`.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Standard polynomial discriminant, with value one for zero and constants. -/
@[expose]
noncomputable def disc [One R] [Add R] [Sub R] [Mul R] [Div R] [NatCast R]
    (f : DensePoly R) : R :=
  if f.size ≤ 1 then
    1
  else
    let n := f.size - 1
    negOnePow (n * (n - 1) / 2) *
      exactDiv (resultant f f.derivative) f.leadingCoeff

/-- Runtime implementation of `disc`, using the compiled derivative loop. -/
@[expose]
def discImpl [One R] [Add R] [Sub R] [Mul R] [Div R] [NatCast R]
    (f : DensePoly R) : R :=
  if f.size ≤ 1 then
    1
  else
    let n := f.size - 1
    negOnePow (n * (n - 1) / 2) *
      exactDiv (resultant f (derivativeImpl f)) f.leadingCoeff

/-- The kernel specification and executable discriminant agree. -/
theorem disc_eq_discImpl [One R] [Add R] [Sub R] [Mul R] [Div R] [NatCast R]
    (f : DensePoly R) : disc f = discImpl f := by
  simp only [disc, discImpl, derivative_eq_derivativeImpl]

/-- Register the executable discriminant for compiled evaluation. -/
@[csimp]
theorem disc_eq_impl : @disc = @discImpl := by
  funext R _ _ _ _ _ _ _ _ f
  exact disc_eq_discImpl f

/-! Compiled regression checks for resultants and discriminants. -/

-- Linear and quadratic resultants, including a reversed odd-degree sign.
#guard
    let xSub2 := ofList ([-2, 1] : List Int)
    let xSub5 := ofList ([-5, 1] : List Int)
    let xSqAdd1 := ofList ([1, 0, 1] : List Int)
    let xSub1 := ofList ([-1, 1] : List Int)
    resultant xSub2 xSub5 = -3 &&
      resultant xSqAdd1 xSub1 = 2 &&
      resultant xSub1 xSqAdd1 = 2

-- Default formal degrees make zero/constant resultants total.
#guard
    let c2 := C (2 : Int)
    let c3 := C (3 : Int)
    let quadratic := ofList ([1, 0, 1] : List Int)
    resultant 0 0 = (1 : Int) &&
      resultant c2 0 = 1 &&
      resultant quadratic 0 = 0 &&
      resultant quadratic c3 = 9 &&
      resultant c2 c3 = 1

-- Common roots and both defective Brown drops produce their pinned values.
#guard
    let commonLeft := ofList ([-1, 0, 1] : List Int)
    let commonRight := ofList ([-1, 1] : List Int)
    let defective1 := ofList ([2, 1, 0, 2, 2] : List Int)
    let defective2 := ofList ([1, 0, 0, 2] : List Int)
    let nonunit1 := ofList ([0, 0, 0, 0, -1] : List Int)
    let nonunit2 := ofList ([-1, 0, 0, 2] : List Int)
    resultant commonLeft commonRight = 0 &&
      resultant defective1 defective2 = 16 &&
      resultant nonunit1 nonunit2 = -1

-- Bivariate elimination executes the recursive exact-division instance.
#guard
    let t : DensePoly Int := ofList [0, 1]
    let one : DensePoly Int := 1
    let ySqSubT : DensePoly (DensePoly Int) := ofList [0 - t, 0, one]
    let ySubT : DensePoly (DensePoly Int) := ofList [0 - t, one]
    resultant ySqSubT ySubT = t * t - t

-- Quadratic, repeated-root, and total discriminant conventions.
#guard
    let quadratic := ofList ([2, 3, 1] : List Int)
    let xSqAdd1 := ofList ([1, 0, 1] : List Int)
    let repeated := ofList ([1, -2, 1] : List Int)
    disc 0 = (1 : Int) &&
      disc (C (2 : Int)) = 1 &&
      disc (ofList ([-7, 3] : List Int)) = 1 &&
      disc quadratic = 1 &&
      disc xSqAdd1 = -4 &&
      disc repeated = 0

end Hex.DensePoly
