/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Element

public section

namespace Hex.RealClosure.Tests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat :=
  (DensePoly.ofCoeffs #[-2, 0, 1]) * (x - DensePoly.C 3)

private def raw : SignDet.RawDescriptor Rat Nat :=
  { context := 7, head, lower := .finite 1, upper := .finite 2,
    indices := [], signs := [] }

/-- The interval selects √2 from a squarefree, reducible polynomial. -/
private def sample : Option (Int × Int × Int × Int × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let equation : Expression d := ⟨head⟩
  let sa ← a.sign?.toOption
  let sb ← below.sign?.toOption
  let se ← equation.sign?.toOption
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let squareMinusTwo := Expression.sub (Expression.mul a a)
    (Expression.ofPoly (DensePoly.C 2))
  let sz ← squareMinusTwo.sign?.toOption
  let expectedInverse : Expression d :=
    ⟨DensePoly.scale (-(1 / 7 : Rat)) (x + DensePoly.C 3)⟩
  let same ← (Expression.sub inv expectedInverse).sign?.toOption
  return (sa, sb, se, si, sz, same)

#eval sample
#guard sample == some (1, -1, 0, -1, 0, 0)
private def stale : Bool := (Root.validate 8 raw).isNone
#eval stale
#guard stale
example : Root.validate 8 raw = none :=
  Root.validate_context raw (by decide)

private def nonmonic : Option (Int × Int × Int × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let a : Expression d := ⟨x⟩
  let sa ← a.sign?.toOption
  let sz ← (Expression.sub a a).sign?.toOption
  let scalar ← (Expression.ofPoly (d := d) (DensePoly.C 6)).sign?.toOption
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  return (sa, sz, scalar, si)

#eval nonmonic
#guard nonmonic == some (1, 0, 1, -1)

private def zeroInverse : Option (Bool × Bool) := do
  let d ← Root.validate 7 raw
  let literal ← (Expression.zero (d := d)).inverse?.toOption
  let selected ← (Expression.ofPoly (d := d) (x * x - DensePoly.C 2)).inverse?.toOption
  return (literal.isNone, selected.isNone)

#eval zeroInverse
#guard zeroInverse == some (true, true)

private def splitDegree : Nat :=
  (DensePoly.gcd head (x - DensePoly.C 3)).natDegree

#eval splitDegree
#guard splitDegree == 1

private def constantGcd : Option (Nat × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let inv? ← a.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let expected : Expression d := ⟨DensePoly.scale (1 / 2 : Rat) x⟩
  let diff ← (Expression.sub inv expected).sign?.toOption
  return (a.inverseFactor.1.natDegree, si, diff)

#eval constantGcd
#guard constantGcd == some (0, 1, 0)

private def splitTransport : Option (Int × Int × Int × Int × Nat × Nat) := do
  let d ← Root.validate 7 raw
  let q := x - DensePoly.C 3
  let below : Expression d := ⟨q⟩
  let r? ← (below.split? 8 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let a : Expression d := ⟨x⟩
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let oldSign ← a.sign?.toOption
  let newSign ← (Expression.transport r.encoding a).sign?.toOption
  let reboundSign ← (Expression.refine r a).sign?.toOption
  let inverseSign ← (Expression.refine r inv).sign?.toOption
  return (oldSign, newSign, reboundSign, inverseSign,
    r.binding.target.raw.head.natDegree, r.binding.target.raw.context)

#eval splitTransport
#guard splitTransport == some (1, 1, 1, -1, 2, 8)

/-- A cofactor with no selected root cannot produce a refinement. -/
private def rejectedSplit : Option Bool := do
  let d ← Root.validate 7 raw
  let selectedZero : Expression d := ⟨x * x - DensePoly.C 2⟩
  let result ← (selectedZero.split? 8 (.finite 1) (.finite 2)).toOption
  return result.isNone

#eval rejectedSplit
#guard rejectedSplit == some true

/-- Splitting a non-monic definition retains its leading scalar. -/
private def nonmonicSplit : Option (Rat × Nat × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let r? ← (below.split? 10 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let sa ← (Expression.refine r (Expression.ofPoly x)).sign?.toOption
  return (r.binding.target.raw.head.leadingCoeff,
    r.binding.target.raw.head.natDegree, sa)

#eval nonmonicSplit
#guard nonmonicSplit == some (2, 2, 1)

/-- The selected-root cofactor yields a nonzero constant Bézout result. -/
private def splitBezout : Option (Nat × Rat) := do
  let d ← Root.validate 7 raw
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let eg := DensePoly.xgcdLeft below.polynomial below.inverseFactor.2
  return (eg.gcd.natDegree, eg.gcd.leadingCoeff)

#eval splitBezout
#guard splitBezout == some (0, 7)

/-- Inverting a representative above the defining degree exercises the first
Euclidean reduction before the constant gcd is found. -/
private def highDegreeInverse : Option (Nat × Int × Int) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x * x * x⟩
  let inv? ← a.inverse?.toOption
  let inv ← inv?
  let si ← inv.sign?.toOption
  let expected : Expression d := ⟨DensePoly.scale (1 / 4 : Rat) x⟩
  let diff ← (Expression.sub inv expected).sign?.toOption
  return (a.polynomial.natDegree, si, diff)

#eval highDegreeInverse
#guard highDegreeInverse == some (3, 1, 0)

/-- The independent canonical root list selects the same root and agrees
with the checked expression inverse at that root. -/
private def canonicalSelection : Option (Int × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let inv? ← below.inverse?.toOption
  let inv ← inv?
  let alpha := a.toCanonical
  return (d.toCanonical.sign,
    alpha * alpha == Hex.RealAlgebraicNumber.ofRat 2,
    below.toCanonical * inv.toCanonical == Hex.RealAlgebraicNumber.ofRat 1)

#eval canonicalSelection
#guard canonicalSelection == some (1, true, true)

/-- A wide interval contains both √2 and 3; the first derivative sign
selects √2 and agrees with the narrow-interval canonical root. -/
private def rawWide : SignDet.RawDescriptor Rat Nat :=
  { context := 11, head, lower := .finite 0, upper := .finite 4,
    indices := [1], signs := [-1] }

private def canonicalThom : Option (Bool × Int × Bool × Int) := do
  let narrow ← Root.validate 7 raw
  let wide ← Root.validate 11 rawWide
  let selected := wide.toCanonical
  return (selected == narrow.toCanonical, selected.sign,
    selected * selected == Hex.RealAlgebraicNumber.ofRat 2,
    (selected - Hex.RealAlgebraicNumber.ofRat 3).sign)

#eval canonicalThom
#guard canonicalThom == some (true, 1, true, -1)

/-- Scaling the reducible defining polynomial does not change the selected
canonical number. -/
private def canonicalNonmonic : Option (Bool × Int × Bool) := do
  let monic ← Root.validate 7 raw
  let scaled ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let selected := scaled.toCanonical
  return (selected == monic.toCanonical, selected.sign,
    selected * selected == Hex.RealAlgebraicNumber.ofRat 2)

#eval canonicalNonmonic
#guard canonicalNonmonic == some (true, 1, true)

/-- The unbounded lower endpoint selects the negative root. -/
private def rawNegative : SignDet.RawDescriptor Rat Nat :=
  { context := 12, head, lower := .negInf, upper := .finite 0,
    indices := [], signs := [] }

private def canonicalNegative : Option (Int × Bool × Int) := do
  let negative ← Root.validate 12 rawNegative
  let selected := negative.toCanonical
  return (selected.sign,
    selected * selected == Hex.RealAlgebraicNumber.ofRat 2,
    (selected + Hex.RealAlgebraicNumber.ofRat 1).sign)

#eval canonicalNegative
#guard canonicalNegative == some (-1, true, -1)

/-- Canonical-zero packing detects a nonliteral zero, cancellation, and the
gcd inverse at the selected root. -/
private def packedArithmetic :
    Option (Bool × Bool × Bool × Int × Int × Bool × Bool × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let alpha : Element d := Element.ofPoly x
  let selectedZero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let below : Element d := Element.ofPoly (x - DensePoly.C 3)
  let higher : Element d := Element.ofPoly (DensePoly.scale (1 / 2 : Rat) (x * x * x))
  return (selectedZero == 0, alpha + -alpha == 0,
    (below * below⁻¹).value == Hex.RealAlgebraicNumber.ofRat 1,
    alpha.sign, below.sign, Element.equal alpha higher, alpha == higher,
    selectedZero⁻¹ == 0, selectedZero.inverse?.isNone)

#eval packedArithmetic
#guard packedArithmetic == some (true, true, true, 1, -1, true, false, true, true)

/-- Repacking after a checked split preserves a nonzero value and the unique
zero representation under the new context version. -/
private def packedRefinement : Option (Bool × Bool × Int) := do
  let d ← Root.validate 7 raw
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let r? ← (below.split? 8 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let alpha : Element d := Element.ofPoly x
  let selectedZero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let newAlpha := Element.refine r alpha
  let newZero := Element.refine r selectedZero
  return (newAlpha.value == alpha.value, newZero == 0, newAlpha.sign)

#eval packedRefinement
#guard packedRefinement == some (true, true, 1)

/-- Numeric literals, division, and both outcomes of semantic comparison. -/
private def packedInterfaces : Option (Bool × Bool × Int × Bool) := do
  let d ← Root.validate 7 raw
  let alpha : Element d := Element.ofPoly x
  let below : Element d := Element.ofPoly (x - DensePoly.C 3)
  return (Element.equal alpha below,
    Element.equal (alpha / alpha) (1 : Element d),
    (3 : Element d).sign,
    Element.equal (below * below⁻¹) (1 : Element d))

#eval packedInterfaces
#guard packedInterfaces == some (false, true, 1, true)

/-- A scaled nonmonic head has the same packed selected-root arithmetic. -/
private def packedNonmonic : Option (Bool × Bool × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let alpha : Element d := Element.ofPoly x
  let selectedZero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  return (selectedZero == 0,
    (alpha * alpha).value == Hex.RealAlgebraicNumber.ofRat 2,
    alpha.sign)

#eval packedNonmonic
#guard packedNonmonic == some (true, true, 1)

/-- The shared polynomial division kernel works with packed selected-root
coefficients and removes a semantically zero remainder. -/
private def packedPolynomial : Option (Nat × Nat × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let alpha : Element d := Element.ofPoly x
  let y : DensePoly (Element d) := DensePoly.ofCoeffs #[0, 1]
  let divisor := y - DensePoly.C alpha
  let dividend := y * y - DensePoly.C 2
  let (quotient, remainder) := DensePoly.divMod dividend divisor
  return (dividend.natDegree, quotient.natDegree, remainder.isZero,
    Element.equal (quotient.eval (0 : Element d)) alpha)

#eval packedPolynomial
#guard packedPolynomial == some (2, 1, true, true)

/-- Extended gcd and differentiation over packed coefficients use selected-root
zero equality, including the coefficient `α² - 2`. -/
private def packedEuclid : Option (Nat × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let alpha : Element d := Element.ofPoly x
  let y : DensePoly (Element d) := DensePoly.ofCoeffs #[0, 1]
  let p := y * y - DensePoly.C 2
  let q := y - DensePoly.C alpha
  let eg := DensePoly.xgcd p q
  return (eg.gcd.natDegree,
    (eg.left * p + eg.right * q - eg.gcd).isZero,
    Element.equal (p.derivative.eval alpha) (2 * alpha))

#eval packedEuclid
#guard packedEuclid == some (1, true, true)

/-- Monic integral definitions retain the division remainder for integral and
fractional inputs; nonmonic and monic fractional heads retain the input. -/
private def packedStorage : Option
    (Nat × Bool × Nat × Nat × Nat × Bool × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let scaled ← Root.validate 9
    { raw with context := 9, head := DensePoly.scale 2 head }
  let fractionalHead ← Root.validate 10
    { raw with context := 10, head :=
      (DensePoly.ofCoeffs #[-2, 0, 1]) * (x - DensePoly.C (1 / 2 : Rat)) }
  let high := x * x * x
  let fractional := DensePoly.scale (1 / 2 : Rat) high
  let packed : Element d := Element.ofPoly high
  return (packed.polynomial.natDegree, Element.clean packed.polynomial,
    (Element.packedPoly scaled high).natDegree,
    (Element.packedPoly d fractional).natDegree,
    (Element.packedPoly fractionalHead high).natDegree,
    Element.packedPoly d head == 0,
    (Element.ofPoly head : Element d) == 0,
    packed.value == evalCanonical high d.toCanonical)

#eval packedStorage
#guard packedStorage == some (2, true, 3, 2, 3, true, true, true)

/-- A polynomial of packed coefficients survives re-encoding, rebinding and
the composite factor split, including a canonical zero interior coefficient. -/
private def packedPolyTransport : Option
    (Nat × Nat × Nat × Bool × Bool × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let r? ← (below.split? 8 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let alpha : Element d := Element.ofPoly x
  let zero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let low : Element d := Element.ofPoly (x - DensePoly.C 3)
  let p : DensePoly (Element d) := DensePoly.ofCoeffs #[alpha, zero, low, alpha]
  let encoded := Element.transportPoly r.encoding p
  let rebound := Element.rebindPoly r.binding encoded
  let refined := Element.refinePoly r p
  let same (q : DensePoly (Element r.binding.target)) : Bool :=
    (List.range 4).all (fun i => (q.coeff i).value == (p.coeff i).value)
  return (encoded.natDegree, rebound.natDegree, refined.natDegree,
    (encoded.coeff 1) == 0, same rebound, same refined,
    (refined.coeff 3).sign == 1)

#eval packedPolyTransport
#guard packedPolyTransport == some (3, 3, 3, true, true, true, true)

end Hex.RealClosure.Tests
