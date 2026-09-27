/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Roots
public import HexNumberField.IntegerRoots
public section

/-! Convert canonical numbers to one chosen or computed common number field. -/
namespace Hex.QAdjoin

/-- Consecutive powers used by coordinate recovery. Certification cannot fail. -/
@[expose] def powerTable (a : AlgebraicNumber) : Array AlgebraicNumber :=
  (AlgebraicPoly.Common.powers? a (2 * a.p.natDegree - 2)).getD
    (Hex.panicWith #[] "QAdjoin: power table certification failed")

/-- Express `b` in the power basis of `a`, or return `none` when `b ∉ ℚ(a)`.
This does not enlarge the chosen field. A real generator rejects nonreal
values before coordinate recovery. -/
@[expose] def ofAlgebraic? (a b : AlgebraicNumber) : Option (QAdjoin a) :=
  if a.isReal && !b.isReal then none
  else AlgebraicPoly.Common.coordinates? a b (powerTable a)

/-- Convert a collection to one chosen field, sharing its power table.
The output preserves input order and records nonmembership separately for each entry. -/
@[expose] def ofAlgebraics? (a : AlgebraicNumber) (bs : Array AlgebraicNumber) :
    Array (Option (QAdjoin a)) :=
  let powers := powerTable a
  bs.map fun b => if a.isReal && !b.isReal then none
    else AlgebraicPoly.Common.coordinates? a b powers

/-- One primitive generator and the input values in its rational power basis.
The public `entries` name describes arbitrary input collections independently of
`AlgebraicPoly.Common.Presentation`, whose `coefficients` field serves polynomial construction. -/
structure Presentation where
  generator : AlgebraicNumber
  entries : Array (QAdjoin generator)

/-- Check proposed coordinates against both selected canonical values. -/
@[expose] def checkPair? (theta alpha gamma : AlgebraicNumber)
    (coordinates : QAdjoin gamma × QAdjoin gamma) :
    Option (QAdjoin gamma × QAdjoin gamma) := do
  let thetaRecovered ← @PolyQuot.toAlgebraicNumber? gamma.p gamma.x gamma.checked
    coordinates.1 gamma.rep gamma.rep_mk
  let alphaRecovered ← @PolyQuot.toAlgebraicNumber? gamma.p gamma.x gamma.checked
    coordinates.2 gamma.rep gamma.rep_mk
  if thetaRecovered == theta && alphaRecovered == alpha then
    some coordinates
  else none

/-- Recover both inputs in a primitive presentation arising from a nonzero
integer shift. The polynomial gcd gives candidate coordinates; canonical
algebraic equality checks the chosen embeddings. -/
@[expose] def recoverShift? (theta alpha gamma : AlgebraicNumber) (shift : Int) :
    Option (QAdjoin gamma × QAdjoin gamma) := do
  if shift = 0 then none else
  letI : ZPoly.CheckedIrreducible gamma.p := gamma.checked
  let generator : QAdjoin gamma := gamma.toQAdjoin
  let affine : DensePoly (QAdjoin gamma) :=
    DensePoly.ofList [generator, (-(shift : Rat)) • (1 : QAdjoin gamma)]
  let thetaRelation := DensePoly.composeImpl
    (DensePoly.ofCoeffs <| theta.p.toArray.map fun (c : Int) =>
      (c : Rat) • (1 : QAdjoin gamma)) affine
  let alphaRelation : DensePoly (QAdjoin gamma) :=
    DensePoly.ofCoeffs <| alpha.p.toArray.map fun (c : Int) =>
      (c : Rat) • (1 : QAdjoin gamma)
  let common := DensePoly.gcd thetaRelation alphaRelation
  if common.natDegree = 1 && common.leadingCoeff != 0 then do
    let alphaCoordinate := -(common.coeff 0) / common.leadingCoeff
    let thetaCoordinate := generator - (shift : Rat) • alphaCoordinate
    checkPair? theta alpha gamma (thetaCoordinate, alphaCoordinate)
  else none

/-- Package a checked pair of coordinates at one proposed generator. -/
@[expose] def presentShift? (theta alpha gamma : AlgebraicNumber) (shift : Int) :
    Option Presentation := do
  let coordinates ← recoverShift? theta alpha gamma shift
  some ⟨gamma, #[coordinates.1, coordinates.2]⟩

/-- Try the first nonzero shift before the existing bounded primitive search. -/
@[expose] def fastCandidate? (theta alpha : AlgebraicNumber) :
    Option (Int × AlgebraicNumber) :=
  let target := theta.p.natDegree * alpha.p.natDegree
  let first := do
    let gamma ← AlgebraicPoly.Common.shift? theta alpha 1
    if gamma.p.natDegree != target then none else
      some (1, gamma)
  match first with
  | some candidate => some candidate
  | none =>
      match AlgebraicPoly.Common.extendShift? theta alpha with
      | some shifted => some (shifted.shift, shifted.value)
      | none => none

/-- Convert a pair through a primitive-element candidate and an exact gcd,
checking that both coordinates recover the selected algebraic values. -/
@[expose] def fastPair? (theta alpha : AlgebraicNumber) : Option Presentation := do
  let (shift, gamma) ← fastCandidate? theta alpha
  presentShift? theta alpha gamma shift

/-- General trace-pairing presentation when the fast pair conversion does not apply. -/
@[expose] def commonFallback (bs : Array AlgebraicNumber) : Presentation :=
  match AlgebraicPoly.Common.presentation? bs with
  | some p => ⟨p.generator, p.coefficients⟩
  | none => Hex.panicWith ⟨0, #[]⟩ "QAdjoin.common: certification failed"

/-- Find one number field containing every input, preserving order and duplicates.
Empty and all-zero collections use `ℚ(0) = ℚ`. The primitive-element search can
be expensive; subsequent arithmetic in the resulting `QAdjoin` uses rational
coordinates without further root isolation. -/
@[expose] def common (bs : Array AlgebraicNumber) : Presentation :=
  if bs.all (fun b => b.isZero) then
    ⟨0, bs.map fun _ => 0⟩
  else if bs.size = 2 then
    match fastPair? bs[0]! bs[1]! with
    | some p => p
    | none => commonFallback bs
  else commonFallback bs

end Hex.QAdjoin
