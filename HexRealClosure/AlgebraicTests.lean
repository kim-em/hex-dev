/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicContext
public meta import HexRealClosure.AlgebraicContext

public section

namespace Hex.RealClosure.Algebraic.Tests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def definition : DensePoly Rat :=
  DensePoly.ofCoeffs #[-2, 0, 1] * (x - DensePoly.C 3)

/-- A reducible definition requires a selected-root zero check even after
monic reduction, and a local gcd split when inverting X-3. -/
private def rationalSample (scale : Rat) : Option (Array Int) := do
  let d ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale definition,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin d (fun q => q.den == 1)
  let a := Element.ofPoly (context := context) x
  let b := Element.ofPoly (context := context) (x - DensePoly.C 3)
  let square := a * a
  let two := Element.ofCoeff (context := context) 2
  let equation := square - two
  let expected := Element.ofPoly (context := context)
    (DensePoly.scale (-(1 / 7 : Rat)) (x + DensePoly.C 3))
  let qs := [x, x * x - DensePoly.C 2]
  let signs ← match context.buildSigns qs with
    | .ok signs => some signs
    | .error _ => none
  let _ ← if context.handle.isSome && signs.values.toList == [1, 0] &&
      context.root.checkSigns qs signs.values signs.evidence then some () else none
  return #[a.sign, b.sign, equation.sign, (b⁻¹).sign,
    (b * b⁻¹ - 1).sign, (b⁻¹ - expected).sign,
    if square.equal two then 1 else 0,
    if square == two then 1 else 0,
    if equation.inv?.isNone then 1 else 0,
    if a.compare two == .lt then 1 else 0,
    (context.reduce (DensePoly.natPow x 4)).natDegree]

#eval rationalSample 1
#guard rationalSample 1 == some #[1, -1, 0, -1, 0, 0, 1, 0, 1, 1, 2]
#eval rationalSample 2
#guard rationalSample 2 == some #[1, -1, 0, -1, 0, 0, 1, 0, 1, 1, 4]

/-- A fractional coefficient prevents retained reduction, even when the
leading coefficient is literal one. -/
private def uncleanSample : Option Bool := do
  let p : DensePoly Rat := DensePoly.ofCoeffs #[-(1 / 2), 0, 1]
  let d ← SignDet.Descriptor.validate Sturm.orderSign (8 : Nat)
    { context := 8, head := p, lower := .finite 0, upper := .finite 1,
      indices := [], signs := [] }
  let context := Context.adjoin d (fun q => q.den == 1)
  return context.reduce (DensePoly.natPow x 4) == DensePoly.natPow x 4

#guard uncleanSample == some true

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := (BaseContext.rational registry).infinitesimal
private abbrev B := BaseContext.Element base
private def epsilon : B := BaseContext.Element.infinitesimal (BaseContext.rational registry)

#guard epsilon.isClean
#guard (epsilon / 2).isClean = false
#guard (epsilon⁻¹).isClean = false

/-- The coefficient carrier has ordinary operations and sign only. Its
positive infinitesimal is smaller than its positive algebraic square root. -/
private def infinitesimalSample : Option (Array Int) := do
  let p : DensePoly B := DensePoly.ofCoeffs #[-epsilon, 0, 1]
  let d ← SignDet.Descriptor.validate BaseContext.Element.sign base.signature
    { context := base.signature, head := p, lower := .finite 0, upper := .finite 1,
      indices := [], signs := [] }
  let context := base.adjoin d
  let a := Element.ofPoly (context := context) (DensePoly.ofCoeffs #[0, 1])
  let e := Element.ofCoeff (context := context) epsilon
  let y : DensePoly B := DensePoly.ofCoeffs #[0, 1]
  let queries := [y, y * y - DensePoly.C epsilon]
  let signs ← match context.buildSigns queries with
    | .ok result => some result
    | .error _ => none
  let _ ← if context.handle.isSome && signs.values.toList == [1, 0] &&
      context.root.checkSigns queries signs.values signs.evidence then some () else none
  return #[a.sign, (a - e).sign, (a * a - e).sign,
    (a * a⁻¹ - 1).sign, (a⁻¹).sign, if a.isClean then 1 else 0,
    (context.reduce (DensePoly.ofCoeffs #[0, 0, 0, 1])).natDegree]

#eval infinitesimalSample
#guard infinitesimalSample == some #[1, 1, 0, 0, 1, 1, 1]

/-- The second descriptor computes over noncanonical selected-root values,
which deliberately have no Field instance. -/
private def nestedSample (scale : Nat) : Option (Array Int) := do
  let raw₁ : SignDet.RawDescriptor Rat Nat :=
    { context := 1, head := definition,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let d ← SignDet.Descriptor.validate Sturm.orderSign 1 raw₁
  let first := Context.adjoin d (fun q => q.den == 1)
  let a := Element.ofPoly (context := first) x
  let below := a - 3
  -- This represents one with nonconstant fractional coefficients.
  let semanticOne := below * below⁻¹
  let factor : Element first := if scale == 0 then semanticOne else scale
  let y : DensePoly (Element first) := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale factor
    (DensePoly.ofCoeffs #[-a, 0, 1] * (y - DensePoly.C 3))
  let raw : SignDet.RawDescriptor (Element first) Nat :=
    { context := 2, head := head,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let d₂ ← SignDet.Descriptor.validate Element.sign 2 raw
  let second := first.extend d₂
  let b := Element.ofPoly (context := second) y
  let old := Element.ofCoeff (context := second) a
  let below₂ := b - 3
  let poly : DensePoly (Element second) := DensePoly.ofCoeffs #[-old, 0, 1]
  let divisor : DensePoly (Element second) := DensePoly.ofCoeffs #[-b, 1]
  let remainder := (DensePoly.divMod poly divisor).2
  let qs := [y, y * y - DensePoly.C a]
  let signs ← match second.buildSigns qs with
    | .ok signs => some signs
    | .error _ => none
  let _ ← if first.handle.isSome && second.handle.isSome &&
      signs.values.toList == [1, 0] &&
      second.root.checkSigns qs signs.values signs.evidence then some () else none
  return #[b.sign, (b - old).sign, (b * b - old).sign, (b * b⁻¹ - 1).sign,
    if remainder.isZero then 1 else 0, (below₂⁻¹).sign,
    (below₂ * below₂⁻¹ - 1).sign,
    (second.reduce (DensePoly.natPow y 4)).natDegree,
    if semanticOne.equal 1 then 1 else 0, if semanticOne == 1 then 1 else 0]

#eval nestedSample 1
#guard nestedSample 1 == some #[1, -1, 0, 0, 1, -1, 0, 2, 1, 0]
#eval nestedSample 2
#guard nestedSample 2 == some #[1, -1, 0, 0, 1, -1, 0, 4, 1, 0]
#eval nestedSample 0
#guard nestedSample 0 == some #[1, -1, 0, 0, 1, -1, 0, 4, 1, 0]

-- Ownership includes the whole context, not only the descriptor's parent tag.
#check_failure Element.mk
#check_failure Context.mk
#check_failure (fun {d : SignDet.Descriptor Rat Nat Sturm.orderSign 7}
  (a : Element (Context.adjoin d (fun _ => true)))
  (b : Element (Context.adjoin d (fun _ => false))) => a + b)

end Hex.RealClosure.Algebraic.Tests
