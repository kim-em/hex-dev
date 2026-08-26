/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Subresultant
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

/-- Standard polynomial discriminant, with value one for zero and constants.

The leading-coefficient gap power promotes the derivative's default-degree
resultant to formal derivative degree `n - 1`. This matters in positive
characteristic, where the derivative's actual degree can drop. -/
@[expose]
def disc [One R] [Add R] [Sub R] [Mul R] [Div R] [NatCast R]
    (f : DensePoly R) : R :=
  if f.size ≤ 1 then
    1
  else
    let n := f.size - 1
    let d := f.derivative
    let gap := n - 1 - d.degree?.getD 0
    negOnePow (n * (n - 1) / 2) *
      exactDiv (powNat f.leadingCoeff gap * resultant f d) f.leadingCoeff

/-! Compiled regression checks for discriminants. -/

-- Quadratic, repeated-root, and total discriminant conventions.
#guard
    let quadratic := ofList ([2, 3, 1] : List Int)
    let xSqAdd1 := ofList ([1, 0, 1] : List Int)
    let repeated := ofList ([1, -2, 1] : List Int)
    let nonmonic := ofList ([1, 2, 3] : List Int)
    let cubic := ofList ([-1, 0, 0, 1] : List Int)
    disc 0 = (1 : Int) &&
      disc (C (2 : Int)) = 1 &&
      disc (ofList ([-7, 3] : List Int)) = 1 &&
      disc quadratic = 1 &&
      disc xSqAdd1 = -4 &&
      disc repeated = 0 &&
      disc nonmonic = -8 &&
      disc cubic = -27

/- The characteristic-five formal-degree regression (a `2X¹⁰ + 3X` fixture
whose derivative degree drops by nine) lives in
`conformance/HexResultant/Conformance.lean`. -/

/-- info: 'Hex.DensePoly.disc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disc

end Hex.DensePoly
