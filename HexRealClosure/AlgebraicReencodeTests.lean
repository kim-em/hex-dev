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
  let a := Element.ofPoly (context := context) x
  let b := Element.ofPoly (context := context) (x - DensePoly.C 3)
  let newer := context.reencode r
  let mapped := Element.reencodePoly r (DensePoly.ofCoeffs #[a, b])
  return #[a.sign, (a.reencode r).sign, b.sign, (b.reencode r).sign,
    ((a.reencode r) * (a.reencode r) - 2).sign,
    ((b.reencode r) * (b.reencode r)⁻¹ - 1).sign,
    (mapped.coeff 0).sign, (mapped.coeff 1).sign,
    (Element.ofPoly (context := newer) x).sign]

#guard splitSample == some #[1, 1, -1, -1, 0, 0, 1, -1, 1]

end Hex.RealClosure.Algebraic.ReencodeTests
