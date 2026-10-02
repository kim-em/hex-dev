/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicReencode
public meta import HexRealClosure.AlgebraicReencode

public section

namespace Hex.RealClosure.Algebraic.ReencodeTests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def factor : DensePoly Rat := DensePoly.ofCoeffs #[-2, 0, 1]
private def source : DensePoly Rat := factor * (x - DensePoly.C 3)

/-- Splitting a reducible definition retains the selected square-root value,
and dependent coefficients are repacked in the new immutable context. -/
private def splitSample : Option (Array Int) := do
  let d ← SignDet.Descriptor.validate Sturm.orderSign (7 : Nat)
    { context := 7, head := source, lower := .finite 1, upper := .finite 2,
      indices := [], signs := [] }
  let context := Context.adjoin d (fun q => q.den == 1)
  let candidate ← (context.root.buildReencoding factor (.finite 1) (.finite 2)).toOption
  let r ← candidate
  let nonmonicCandidate ← (context.root.buildReencoding (DensePoly.scale 2 factor)
    (.finite 1) (.finite 2)).toOption
  let nonmonic ← nonmonicCandidate
  let restored ← Element.restore? (context := context) (DensePoly.natPow x 4) 1
  let a := Element.ofPoly (context := context) x
  let b := Element.ofPoly (context := context) (x - DensePoly.C 3)
  let newer := context.reencode r
  let square := Element.ofPoly (context := context) (x * x)
  let cube := Element.ofPoly (context := context) (DensePoly.natPow x 3)
  let zero := Element.ofPoly (context := context) (x * x - 2)
  let mapped := Element.reencodePoly r (DensePoly.ofCoeffs #[a, zero, b])
  return #[a.sign, (a.reencode r).sign, b.sign, (b.reencode r).sign,
    ((a.reencode r) * (a.reencode r) - 2).sign,
    ((b.reencode r) * (b.reencode r)⁻¹ - 1).sign,
    (mapped.coeff 0).sign, (mapped.coeff 2).sign,
    (Element.ofPoly (context := newer) x).sign,
    if newer.root.raw.head == factor then 1 else 0,
    if square.polynomial.toArray == #[0, 0, 1] then 1 else 0,
    if (square.reencode r).polynomial.toArray == #[2] then 1 else 0,
    if cube.polynomial.toArray != #[0, 2] then 1 else 0,
    if (cube.reencode r).polynomial.toArray == #[0, 2] then 1 else 0,
    if zero == 0 && mapped.coeff 1 == 0 && mapped.coeff 3 == 0 then 1 else 0,
    if restored.polynomial.toArray == #[0, 0, 0, 0, 1] then 1 else 0,
    if (restored.reencode r).polynomial.toArray == #[4] then 1 else 0,
    if (restored.reencode nonmonic).polynomial.toArray == #[0, 0, 0, 0, 1] then 1 else 0]

#guard splitSample == some #[1, 1, -1, -1, 0, 0, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

end Hex.RealClosure.Algebraic.ReencodeTests
