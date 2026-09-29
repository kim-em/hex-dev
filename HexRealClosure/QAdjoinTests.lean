/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.QAdjoin
public meta import HexRealClosure.QAdjoin

public section

namespace Hex.RealClosure.QAdjoinTests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def squareHead : DensePoly Rat :=
  (DensePoly.ofCoeffs #[-2, 0, 1]) * (x - DensePoly.C 3)
private def squareRaw : SignDet.RawDescriptor Rat Nat :=
  { context := 7, head := squareHead, lower := .finite 1, upper := .finite 2,
    indices := [], signs := [] }

/-- Fixed-field and packed multiplication agree at the selected √2 even
when their stored polynomials differ. The independent field conversion checks
that the generator has the same selected embedding. -/
private def squarePack : Option (Int × Int × Bool × Bool × Bool × Bool × Bool) := do
  let d ← Root.validate 7 squareRaw
  let h := d.handle
  let generator := h.canonical.toAlgebraic.toQAdjoin
  let c := 1 + generator
  let packed := h.packQAdjoin c
  let fieldSquare := h.packQAdjoin (c * c)
  let packedSquare := h.mul packed packed
  let fieldValue := Hex.RealAlgebraicNumber.ofAlgebraic?
    (c * c).toAlgebraicNumber
  let negative := (-h.canonical).toAlgebraic.toQAdjoin
  return (h.sign (h.packQAdjoin generator),
    h.sign (h.packQAdjoin (generator - 2)),
    h.equal fieldSquare packedSquare, fieldSquare == packedSquare,
    fieldValue == some (h.value fieldSquare),
    (h.packQAdjoin? generator).isSome,
    (h.packQAdjoin? negative).isNone)

#guard squarePack == some (1, -1, true, false, true, true, true)

private def cubicPoly : ZPoly := DensePoly.ofList [-2, 0, 0, 1]
private def cubicSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 5411319705 32, 0, 32⟩
private def cubicRep : RefinedIsolation cubicPoly :=
  ⟨⟨cubicSquare, .ofWitness (by decide)⟩, by decide⟩

/-- Construct the cubic generator from its own isolation, independently of
the real-closure descriptor. -/
private def cubicGenerator? : Option AlgebraicNumber :=
  if hirred : ZPoly.isIrreducible cubicPoly = true then
    if hsimple : HasOnlySimpleRoots cubicPoly then
      AlgebraicNumber.ofNormalized? cubicPoly (by rfl) (by decide)
        (by decide) ⟨hirred, by decide⟩ hsimple cubicRep
    else none
  else none

private def cubicHead : DensePoly Rat := DensePoly.ofList [-2, 0, 0, 1]
private def cubicRaw : SignDet.RawDescriptor Rat Nat :=
  { context := 12, head := cubicHead, lower := .finite 1, upper := .finite 2,
    indices := [], signs := [] }

/-- An independently constructed cubic field generator packs at the same
selected root. Its exact fixed-field division and multiplication preserve
value, and the cubic equation holds after packing. -/
private def cubicPack : Option (Bool × Bool × Int × Int) := do
  let d ← Root.validate 12 cubicRaw
  let h := d.handle
  let a ← cubicGenerator?
  let generator := a.toQAdjoin
  let coordinate := (generator * generator + 1) / 2
  let packed ← h.packQAdjoin? coordinate
  let packedGenerator ← h.packQAdjoin? generator
  let fieldValue := Hex.RealAlgebraicNumber.ofAlgebraic?
    coordinate.toAlgebraicNumber
  return (fieldValue == some (h.value packed),
    h.equal (h.mul packedGenerator
      (h.mul packedGenerator packedGenerator)) (h.pack 2),
    h.sign packedGenerator,
    h.sign (h.sub packedGenerator (h.pack 1)))

#guard cubicPack == some (true, true, 1, 1)

end Hex.RealClosure.QAdjoinTests
