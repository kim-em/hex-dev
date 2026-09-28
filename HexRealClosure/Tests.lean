/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Yun
public import HexRealClosure.Bounds
public import HexRealClosure.Deflation
public import HexRealClosure.BaseTests
public import HexRealClosure.BasePolynomialTests
public import HexRealClosure.BaseCatalogTests
public import HexRealClosure.AlgebraicTests
public import HexRealClosure.TowerTests
public import HexRealClosure.FrameFormatTests
public import HexRealClosure.TowerOrderTests
public import HexRealClosure.TowerYunTests
public meta import HexSturm.Basic
public meta import HexRealClosure.Bounds
public meta import HexRealClosure.Deflation

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
    (Nat × Nat × Nat × Bool × Bool × Bool × Bool × Bool) := do
  let d ← Root.validate 7 raw
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let r? ← (below.split? 8 (.finite 1) (.finite 2)).toOption
  let r ← r?
  let alpha : Element d := Element.ofPoly x
  let zero : Element d := Element.ofPoly (x * x - DensePoly.C 2)
  let square : Element d := Element.ofPoly (x * x)
  let p : DensePoly (Element d) := DensePoly.ofCoeffs #[alpha, zero, square, alpha]
  let encoded := Element.transportPoly r.encoding p
  let rebound := Element.rebindPoly r.binding encoded
  let refined := Element.refinePoly r p
  let same (q : DensePoly (Element r.binding.target)) : Bool :=
    (List.range 4).all (fun i => (q.coeff i).value == (p.coeff i).value)
  return (encoded.natDegree, rebound.natDegree, refined.natDegree,
    (encoded.coeff 1) == 0, same rebound, same refined,
    (p.coeff 2).polynomial.natDegree == 2 &&
      (refined.coeff 2).polynomial.natDegree == 0,
    (refined.coeff 3).sign == 1)

#eval packedPolyTransport
#guard packedPolyTransport == some (3, 3, 3, true, true, true, true, true)

/-- One selected-root search serves repeated packing, arithmetic, and all
coefficient transports in a checked factor split. -/
private def cachedHandle : Option
    (Int × Bool × Bool × Bool × List Rat × List Rat ×
      List (List Rat) × List (List Rat) × List (List Rat)) := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let alpha := h.pack x
  let below := h.pack (x - DensePoly.C 3)
  let zero := h.pack (x * x - DensePoly.C 2)
  let inverse ← h.inverse? below
  let split? ← ((Expression.ofPoly (d := d)
    (x - DensePoly.C 3)).split? 8 (.finite 1) (.finite 2)).toOption
  let split ← split?
  let encodedHandle := Root.handle split.encoding.target
  let targetHandle := Root.handle split.binding.target
  let p : DensePoly (Element d) :=
    DensePoly.ofCoeffs #[alpha, zero, h.pack (x * x), alpha]
  let encoded := Element.transportPolyWith split.encoding encodedHandle p
  let rebound := Element.rebindPolyWith split.binding targetHandle encoded
  let refined := Element.refinePolyWith split targetHandle p
  let stored (a : Element d) : List Rat := a.polynomial.toArray.toList
  let encodedCoeffs := (List.range 4).map
    (fun i => (encoded.coeff i).polynomial.toArray.toList)
  let reboundCoeffs := (List.range 4).map
    (fun i => (rebound.coeff i).polynomial.toArray.toList)
  let refinedCoeffs := (List.range 4).map
    (fun i => (refined.coeff i).polynomial.toArray.toList)
  return (h.sign inverse,
    zero == 0,
    (h.inverse? zero).isNone,
    h.sub (h.mul below inverse) (h.pack 1) == 0,
    stored (h.mul alpha below), stored inverse,
    encodedCoeffs, reboundCoeffs, refinedCoeffs)

#eval cachedHandle
#guard cachedHandle == some (-1, true, true, true, [0, -3, 1],
  [-3 / 7, -1 / 7], [[0, 1], [], [2], [0, 1]],
  [[0, 1], [], [2], [0, 1]], [[0, 1], [], [2], [0, 1]])

/-- Distinct stored polynomials can represent the same selected value. -/
private def cachedEquality : Option (Bool × Bool) := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let square := h.pack (x * x)
  let two := h.pack 2
  return (h.equal square two, square == two)

#guard cachedEquality == some (true, false)

/-- The non-monic fallback retains raw storage while the cached root still
decides semantic zero and sign. -/
private def cachedNonmonic : Option (Nat × Bool × Int) := do
  let d ← Root.validate 9 { raw with context := 9, head := DensePoly.scale 2 head }
  let h := d.handle
  let high := h.pack (x * x * x)
  let zero := h.pack (x * x - DensePoly.C 2)
  let below := h.pack (x - DensePoly.C 3)
  return (high.polynomial.natDegree, zero == 0, h.sign below)

#eval cachedNonmonic
#guard cachedNonmonic == some (3, true, -1)

/-- Ordinary polynomial division uses the same handle for every coefficient
operation, including the semantic zero tests on leading coefficients. -/
private def cachedPolynomial : Option (Bool × Nat × Bool) := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let alpha : Root.Handle.Value h := Root.Handle.Value.ofPoly h x
  let y : DensePoly (Root.Handle.Value h) := DensePoly.ofCoeffs #[0, 1]
  let divisor := y - DensePoly.C alpha
  let dividend := y * y - DensePoly.C 2
  let (quotient, remainder) := DensePoly.divMod dividend divisor
  return (remainder.isZero, quotient.natDegree,
    (quotient.eval (0 : Root.Handle.Value h)).value == alpha.value)

#eval cachedPolynomial
#guard cachedPolynomial == some (true, 1, true)

/-- Yun's recurrence skips the first multiplicity when every root is repeated. -/
private def yunRat : Option (Rat × Array (Array Rat × Nat)) :=
  let p := x - DensePoly.C 1
  let q := x - DensePoly.C 2
  let f : DensePoly Rat := DensePoly.C 2 * (p * p) * (q * q * q)
  match Yun.decompose (K := Rat) f with
  | .zero => none
  | .factors u entries =>
      some (u, entries.map fun entry => (entry.1.toArray, entry.2))

#eval yunRat
#guard yunRat == some (2, #[(#[-1, 1], 2), (#[-2, 1], 3)])

private def yunRatReconstruct : Bool :=
  let p := x - DensePoly.C 1
  let q := x - DensePoly.C 2
  let f : DensePoly Rat := DensePoly.C 2 * (p * p) * (q * q * q)
  match Yun.decompose (K := Rat) f with
  | .zero => false
  | .factors u entries =>
      Yun.reconstruct u entries == f &&
        Yun.degreeSum entries == f.natDegree

#guard yunRatReconstruct

/-- Replay rejects a missing multiplicity and an out-of-order factor list. -/
private def yunReplay : Bool :=
  let p := x - DensePoly.C 1
  let q := x - DensePoly.C 2
  let f : DensePoly Rat := DensePoly.C 2 * (p * p) * (q * q * q)
  Yun.check f (Yun.decompose f) &&
    !(Yun.check f (.factors 2 #[(p, 1), (q, 3)])) &&
    !(Yun.check f (.factors 2 #[(q, 3), (p, 2)]))

#guard yunReplay

/-- A powered factor reconstructs but fails the squarefreeness replay. -/
private def yunRejectPower : Bool :=
  let p := x - DensePoly.C 1
  let f : DensePoly Rat := p * p
  !(Yun.check f (.factors 1 #[(f, 1)]))

#guard yunRejectPower

/-- Product and degree can match while overlapping factors invalidate replay. -/
private def yunRejectOverlap : Bool :=
  let p : DensePoly Rat := x - DensePoly.C 1
  let f := p ^ 3
  let entries := #[(p, 1), (p, 2)]
  Yun.reconstruct 1 entries == f &&
    Yun.degreeSum entries == f.natDegree &&
    !(Yun.check f (.factors 1 entries))

#guard yunRejectOverlap

/-- A rescaled factor can reconstruct correctly but is not monic. -/
private def yunRejectNonmonic : Bool :=
  let p : DensePoly Rat := x - DensePoly.C 1
  let q : DensePoly Rat := x - DensePoly.C 2
  let f := DensePoly.C 2 * p ^ 2 * q ^ 3
  let entries := #[(DensePoly.C 2 * p, 2), (q, 3)]
  Yun.reconstruct (1 / 2) entries == f &&
    Yun.degreeSum entries == f.natDegree &&
    !(Yun.check f (.factors (1 / 2) entries))

#guard yunRejectNonmonic

/-- Zero and nonzero constants have distinct Yun outputs. -/
private def yunZero : Bool :=
  match Yun.decompose (0 : DensePoly Rat) with
  | .zero => true
  | .factors .. => false

private def yunConstant : Bool :=
  match Yun.decompose (DensePoly.C (7 / 3 : Rat)) with
  | .zero => false
  | .factors u entries => u == 7 / 3 && entries.isEmpty

#guard yunZero
#guard yunConstant

private def yunReplayEdges : Bool :=
  Yun.check (0 : DensePoly Rat) (Yun.decompose 0) &&
    Yun.check (DensePoly.C (7 / 3 : Rat))
      (Yun.decompose (DensePoly.C (7 / 3 : Rat))) &&
    !(Yun.check (0 : DensePoly Rat) (.factors 1 #[]))

#guard yunReplayEdges

/-- Squarefree factors are grouped at multiplicity one. -/
private def yunSquarefree : Option (Rat × Array (Array Rat × Nat)) :=
  let f : DensePoly Rat := DensePoly.C 2 * (x - DensePoly.C 1) *
    (x - DensePoly.C 2)
  match Yun.decompose (K := Rat) f with
  | .zero => none
  | .factors u entries =>
      some (u, entries.map fun entry => (entry.1.toArray, entry.2))

#guard yunSquarefree == some (2, #[(#[2, -3, 1], 1)])

/-- A degree-five power requires four empty Yun rounds before emission. -/
private def yunGap : Option (Nat × Array Rat) :=
  let f : DensePoly Rat := (x - DensePoly.C 1) ^ 5
  match Yun.decompose (K := Rat) f with
  | .zero => none
  | .factors _ entries =>
      if entries.size = 1 then
        entries[0]?.map fun entry => (entry.2, entry.1.toArray)
      else none

#eval yunGap
#guard yunGap == some (5, #[-1, 1])

/-- A repeated irreducible quadratic does not need rational linear roots. -/
private def yunQuadratic : Bool :=
  let p : DensePoly Rat := x * x + 1
  let f := p * p * p
  match Yun.decompose f with
  | .zero => false
  | .factors u entries =>
      u == 1 && entries.size == 1 &&
        ((entries[0]?.map (fun entry => entry.1 == p && entry.2 == 3)).getD false) &&
        Yun.check f (.factors u entries)

#guard yunQuadratic

/-- Zero and nonzero roots retain their multiplicities and fractional unit. -/
private def yunMixed : Bool :=
  let x0 : DensePoly Rat := DensePoly.ofCoeffs #[0, 1, 0]
  let q : DensePoly Rat := x - DensePoly.C 1
  let f := DensePoly.C (-3 / 2 : Rat) * x0 ^ 2 * q ^ 4
  match Yun.decompose f with
  | .zero => false
  | .factors u entries =>
      u == -3 / 2 && entries == #[(x, 2), (q, 4)] &&
        Yun.check f (.factors u entries)

#guard yunMixed

/-- The same executable recurrence accepts packed selected-root coefficients. -/
private def yunNested : Option (Nat × Nat × Bool) := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let alpha : Root.Handle.Value h := Root.Handle.Value.ofPoly h x
  let y : DensePoly (Root.Handle.Value h) := DensePoly.ofCoeffs #[0, 1]
  let f := (y - DensePoly.C alpha) * (y - DensePoly.C alpha)
  match Yun.decomposeRaw f with
  | .zero => none
  | .factors u entries =>
      let factor := entries[0]?.map Prod.fst
      return (entries.size, entries[0]?.map Prod.snd |>.getD 0,
        u.value == 1 &&
          (factor.map fun p =>
            p.natDegree == 1 && (p.eval alpha).value == 0 &&
              (DensePoly.C u * (p * p)).toArray.map (fun c => c.value) ==
                f.toArray.map (fun c => c.value)).getD false)

#eval yunNested
#guard yunNested == some (1, 2, true)

-- Equality at the strict coefficient threshold must be rejected.
#guard !Bounds.check Sturm.orderSign (DensePoly.ofCoeffs (#[-2, 0, 1] : Array Rat)) 3
#guard Bounds.check Sturm.orderSign (DensePoly.ofCoeffs (#[-2, 0, 1] : Array Rat)) 4
#guard (Bounds.find? Sturm.orderSign (DensePoly.ofCoeffs (#[-2, 0, 1] : Array Rat))).map
  (fun b => b.value) == some 4
#guard (Bounds.find? Sturm.orderSign (DensePoly.ofCoeffs (#[2, 0, -1] : Array Rat))).map
  (fun b => b.value) == some 4
#guard (Bounds.find? Sturm.orderSign (0 : DensePoly Rat)).isNone

-- A finite-search failure can coexist with an ordinary rational root.
#guard (Bounds.find? Sturm.orderSign (DensePoly.ofCoeffs (#[-1000, 2] : Array Rat))).isNone
#guard (DensePoly.ofCoeffs (#[-1000, 2] : Array Rat)).eval 500 == 0

/-- The bound search accepts packed coefficients with structural inequality
between representatives of the same nonzero value. -/
private def packedBound : Option Bool := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let alpha : Root.Handle.Value h := Root.Handle.Value.ofPoly h x
  let square := alpha * alpha
  let p : DensePoly (Root.Handle.Value h) := DensePoly.ofCoeffs #[-square, 0, 1]
  let b ← Bounds.find? Root.Handle.Value.sign p
  return square != (2 : Root.Handle.Value h) && (square - 2).value == 0 && b.value.value == 4

#guard packedBound == some true

#guard (deflate? (0 : DensePoly Rat) 0).isNone
#guard (deflate? (DensePoly.C (3 : Rat)) 0).isNone
#guard (deflate? (DensePoly.ofCoeffs (#[-2, 0, 1] : Array Rat)) 1).isNone
#guard (deflate? (DensePoly.ofCoeffs (#[-2, 3] : Array Rat)) (2 / 3)).map
  (fun d => d.quotient) == some (DensePoly.C 3)
#guard (deflate? (DensePoly.ofCoeffs (#[1, -2, 1] : Array Rat)) 1).map
  (fun d => d.quotient.eval 1) == some 0

/-- Exact removal uses represented coefficient zero, including cancellation
between structurally different nonzero coefficients in a selected-root field. -/
private def packedDeflation : Option Bool := do
  let d ← Root.validate 7 raw
  let h := d.handle
  let alpha : Root.Handle.Value h := Root.Handle.Value.ofPoly h x
  let p : DensePoly (Root.Handle.Value h) := DensePoly.ofCoeffs #[-2, 0, 1]
  let removed ← deflate? p alpha
  let q := removed.quotient
  return q.natDegree == 1 && (q.coeff 0 - alpha).value == 0 &&
    q.coeff 1 == 1 && (q.eval alpha).value == (2 * alpha).value

#guard packedDeflation == some true

end Hex.RealClosure.Tests
