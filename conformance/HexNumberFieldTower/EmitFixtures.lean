/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexNumberFieldTower

/-!
JSONL emit driver for the `hex-number-field-tower` PARI oracle.

Each case emits its absolute generator polynomials under
`case/generator/i`, an optional integer-coefficient polynomial input under
`case/input`, and one result. The companion oracle independently builds the
requested relative-degree compositum with PARI, compares the actual monic
factor coefficients and multiplicities, uses `nfsplitting` for rational-input
splitting-field degrees, and checks the direct bounded primitive-element search
and linear coordinate-recovery fast path used by these fixtures.

The JSONL profile intentionally represents only integer-coefficient inputs.
Genuinely relative inputs such as `X² - sqrt(2)` remain in the core profile
above; they are not silently reinterpreted over the rationals here.
-/

namespace Hex.NumberTowerEmit

open Hex
open Hex.Conformance.Emit
open Hex.NumberTower

private def lib : String := "HexNumberFieldTower"

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

private def sqrtTwo? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some (ofQAdjoin (x := sqrtTwoRoot) hsimple sqrtTwoRep rfl)
    else
      none
  else
    none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtThree? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep
        rep := sqrtThreeRep
        rep_mk := rfl }
  else
    none

private def fourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def fourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def fourthRootTwoRep : RefinedIsolation fourthRootTwoPoly :=
  ⟨⟨fourthRootTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def fourthRootTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots fourthRootTwoPoly then
    some
      { p := fourthRootTwoPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk fourthRootTwoRep
        rep := fourthRootTwoRep
        rep_mk := rfl }
  else
    none

private structure TwoLevel where
  base : Extension rat
  extension : Extension base.tower

private def twoLevel? : Option TwoLevel := do
  let base ← sqrtTwo?
  let root ← sqrtThree?
  let extension ← adjoin? base.tower root
  some ⟨base, extension⟩

private def rationalPoly (coefficients : List Rat) : Poly rat :=
  DensePoly.ofCoeffs (coefficients.toArray.map (ofRat rat))

private def emitGenerators (case : String)
    (generators : List (ZPoly × DyadicSquare)) : IO Unit := do
  let mut i := 0
  for (polynomial, square) in generators do
    emitPolyFixture lib (case ++ "/generator/" ++ toString i)
      polynomial.toArray.toList
    let re := square.re.toRat
    let im := square.im.toRat
    emitMatrixFixture lib (case ++ "/embedding/" ++ toString i)
      [[re.num, Int.ofNat re.den], [im.num, Int.ofNat im.den],
        [square.prec]]
    i := i + 1

private def emitInput (case : String) (polynomial : ZPoly) : IO Unit :=
  emitPolyFixture lib (case ++ "/input") polynomial.toArray.toList

private def jsonNat (n : Nat) : String := toString n

private def jsonInt (n : Int) : String := toString n

private def ratValue (q : Rat) : String :=
  "[" ++ jsonInt q.num ++ "," ++ jsonNat q.den ++ "]"

private def ratArrayValue (values : Array Rat) : String := Id.run do
  let mut out := "["
  let mut first := true
  for value in values do
    if first then first := false else out := out.push ','
    out := out ++ ratValue value
  out.push ']'

private def elemArrayValue {T : NumberTower}
    (values : Array (Elem T)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for value in values do
    if first then first := false else out := out.push ','
    out := out ++ ratArrayValue (coeffs value)
  out.push ']'

private def natArrayValue (values : List Nat) : String :=
  intListValue (values.map Int.ofNat)

private def factorValue {T : NumberTower} {f : Poly T}
    (degrees : List Nat) (result : Hex.NumberTower.Factorization T f) : String :=
  let factors := Id.run do
    let mut out := "["
    let mut first := true
    for entry in result.factors do
      if first then first := false else out := out.push ','
      out := out ++ "{\"coefficients\":" ++ elemArrayValue entry.1.toArray ++
        ",\"multiplicity\":" ++ jsonNat entry.2 ++ "}"
    out.push ']'
  "{\"dimension\":" ++ jsonNat T.dim ++
    ",\"degrees\":" ++ natArrayValue degrees ++
    ",\"scalar\":" ++ ratArrayValue (coeffs result.scalar) ++
    ",\"factors\":" ++ factors ++ "}"

private def flattenValue (degrees : List Nat) (polynomial : ZPoly) : String :=
  "{\"degrees\":" ++ natArrayValue degrees ++
    ",\"minpoly\":" ++ polyValue polynomial.toArray.toList ++ "}"

private def splitValue {T : NumberTower} {f : Poly T}
    (result : Splitting T f) : Option String :=
  match result.roots with
  | .all => none
  | .finite roots =>
      let multiplicities := (roots.map (Int.ofNat ∘ Prod.snd)).qsort (· ≤ ·)
      some <| intListValue <|
        [Int.ofNat result.extension.tower.dim, Int.ofNat roots.size] ++
          multiplicities.toList

private def emitFactorRat : IO Unit := do
  let case := "factor/rat-repeated"
  let inputPoly : ZPoly := DensePoly.ofList [4, 0, -4, 0, 1]
  emitGenerators case []
  emitInput case inputPoly
  match factor? rat (rationalPoly [4, 0, -4, 0, 1]) with
  | some result => emitResult lib case "factorization" (factorValue [] result)
  | none => throw <| IO.userError (case ++ ": factor? failed")

private def emitFactorContent : IO Unit := do
  let case := "factor/rat-content"
  let inputPoly : ZPoly := DensePoly.ofList [-12, 0, 6]
  emitGenerators case []
  emitInput case inputPoly
  match factor? rat (rationalPoly [-12, 0, 6]) with
  | some result => emitResult lib case "factorization" (factorValue [] result)
  | none => throw <| IO.userError (case ++ ": factor? failed")

private def emitFactorSqrtTwo : IO Unit := do
  let case := "factor/sqrt2-linear"
  emitGenerators case [(sqrtTwoPoly, sqrtTwoSquare)]
  emitInput case sqrtTwoPoly
  match sqrtTwo? with
  | some base =>
      let input : Poly base.tower := DensePoly.ofCoeffs
        #[ofRat base.tower (-2), 0, 1]
      match factor? base.tower input with
      | some result =>
          emitResult lib case "factorization" (factorValue [2] result)
      | none => throw <| IO.userError (case ++ ": factor? failed")
  | none => throw <| IO.userError (case ++ ": base construction failed")

private def emitFactorTwoLevel : IO Unit := do
  let case := "factor/intermediate-sqrt3"
  emitGenerators case
    [(sqrtTwoPoly, sqrtTwoSquare), (sqrtThreePoly, sqrtThreeSquare)]
  emitInput case sqrtThreePoly
  match twoLevel? with
  | some tower =>
      let T := tower.extension.tower
      let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
      match factor? T input with
      | some result =>
          emitResult lib case "factorization" (factorValue [2, 2] result)
      | none => throw <| IO.userError (case ++ ": factor? failed")
  | none => throw <| IO.userError (case ++ ": tower construction failed")

private def emitSplit (case : String) (coefficients : List Int) : IO Unit := do
  let inputPoly : ZPoly := DensePoly.ofList coefficients
  emitGenerators case []
  emitInput case inputPoly
  let input := rationalPoly (coefficients.map Rat.ofInt)
  match split? rat input with
  | some result =>
      match splitValue result with
      | some value => emitResult lib case "split" value
      | none => throw <| IO.userError (case ++ ": unexpected Roots.all")
  | none => throw <| IO.userError (case ++ ": split? failed")

private def emitFlattenTwoLevel : IO Unit := do
  let case := "flatten/sqrt2-sqrt3"
  emitGenerators case
    [(sqrtTwoPoly, sqrtTwoSquare), (sqrtThreePoly, sqrtThreeSquare)]
  match twoLevel? with
  | some tower =>
      match flatten? tower.extension.tower with
      | some result =>
          emitResult lib case "flatten_minpoly"
            (flattenValue [2, 2] result.root.p)
      | none => throw <| IO.userError (case ++ ": flatten? failed")
  | none => throw <| IO.userError (case ++ ": tower construction failed")

private def emitFlattenFourthRoot : IO Unit := do
  let case := "flatten/sqrt2-fourth-root"
  emitGenerators case
    [(sqrtTwoPoly, sqrtTwoSquare),
      (fourthRootTwoPoly, fourthRootTwoSquare)]
  match sqrtTwo?, fourthRootTwo? with
  | some base, some root =>
      match adjoin? base.tower root with
      | some extension =>
          match flatten? extension.tower with
          | some result =>
              emitResult lib case "flatten_minpoly"
                (flattenValue [2, 2] result.root.p)
          | none => throw <| IO.userError (case ++ ": flatten? failed")
      | none => throw <| IO.userError (case ++ ": adjoin? failed")
  | _, _ => throw <| IO.userError (case ++ ": fixture construction failed")

end Hex.NumberTowerEmit

def main : IO Unit := do
  Hex.NumberTowerEmit.emitFactorRat
  Hex.NumberTowerEmit.emitFactorContent
  Hex.NumberTowerEmit.emitFactorSqrtTwo
  Hex.NumberTowerEmit.emitFactorTwoLevel
  Hex.NumberTowerEmit.emitSplit "split/quadratic" [-2, 0, 1]
  Hex.NumberTowerEmit.emitSplit "split/repeated" [4, 0, -4, 0, 1]
  Hex.NumberTowerEmit.emitSplit "split/quartic" [6, 0, -5, 0, 1]
  Hex.NumberTowerEmit.emitFlattenTwoLevel
  Hex.NumberTowerEmit.emitFlattenFourthRoot
