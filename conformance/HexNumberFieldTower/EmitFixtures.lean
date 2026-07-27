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
`case/generator/i`, an optional polynomial input under `case/input`, and one
result. The companion `scripts/oracle/number_field_tower_pari.py` independently
builds the compositum with PARI, uses `nfinit`/`nffactor` for relative
factor-degree buckets, `nfsplitting` for splitting-field degrees, and bounded
resultants for the first full-degree primitive element.
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
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

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
  ⟨⟨sqrtThreeSquare, by decide⟩, by decide⟩

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

private def emitGenerators (case : String) (polynomials : List ZPoly) : IO Unit := do
  let mut i := 0
  for polynomial in polynomials do
    emitPolyFixture lib (case ++ "/generator/" ++ toString i)
      polynomial.toArray.toList
    i := i + 1

private def emitInput (case : String) (polynomial : ZPoly) : IO Unit :=
  emitPolyFixture lib (case ++ "/input") polynomial.toArray.toList

private def factorValue {T : NumberTower} {f : Poly T}
    (result : Hex.NumberTower.Factorization T f) : String :=
  intMatrixValue <| result.factors.toList.map fun entry =>
    [(entry.1.degree?.getD 0 : Nat), entry.2].map Int.ofNat

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
  | some result => emitResult lib case "factor_degrees" (factorValue result)
  | none => throw <| IO.userError (case ++ ": factor? failed")

private def emitFactorSqrtTwo : IO Unit := do
  let case := "factor/sqrt2-linear"
  emitGenerators case [sqrtTwoPoly]
  emitInput case sqrtTwoPoly
  match sqrtTwo? with
  | some base =>
      let input : Poly base.tower := DensePoly.ofCoeffs
        #[ofRat base.tower (-2), 0, 1]
      match factor? base.tower input with
      | some result => emitResult lib case "factor_degrees" (factorValue result)
      | none => throw <| IO.userError (case ++ ": factor? failed")
  | none => throw <| IO.userError (case ++ ": base construction failed")

private def emitFactorTwoLevel : IO Unit := do
  let case := "factor/intermediate-sqrt3"
  emitGenerators case [sqrtTwoPoly, sqrtThreePoly]
  emitInput case sqrtThreePoly
  match twoLevel? with
  | some tower =>
      let T := tower.extension.tower
      let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
      match factor? T input with
      | some result => emitResult lib case "factor_degrees" (factorValue result)
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

private def emitFlattenRat : IO Unit := do
  let case := "flatten/rat"
  emitGenerators case []
  match flatten? rat with
  | some result =>
      emitResult lib case "flatten_minpoly" (polyValue result.root.p.toArray.toList)
  | none => throw <| IO.userError (case ++ ": flatten? failed")

private def emitFlattenSqrtTwo : IO Unit := do
  let case := "flatten/sqrt2"
  emitGenerators case [sqrtTwoPoly]
  match sqrtTwo? with
  | some base =>
      match flatten? base.tower with
      | some result =>
          emitResult lib case "flatten_minpoly"
            (polyValue result.root.p.toArray.toList)
      | none => throw <| IO.userError (case ++ ": flatten? failed")
  | none => throw <| IO.userError (case ++ ": base construction failed")

private def emitFlattenTwoLevel : IO Unit := do
  let case := "flatten/sqrt2-sqrt3"
  emitGenerators case [sqrtTwoPoly, sqrtThreePoly]
  match twoLevel? with
  | some tower =>
      match flatten? tower.extension.tower with
      | some result =>
          emitResult lib case "flatten_minpoly"
            (polyValue result.root.p.toArray.toList)
      | none => throw <| IO.userError (case ++ ": flatten? failed")
  | none => throw <| IO.userError (case ++ ": tower construction failed")

end Hex.NumberTowerEmit

def main : IO Unit := do
  Hex.NumberTowerEmit.emitFactorRat
  Hex.NumberTowerEmit.emitFactorSqrtTwo
  Hex.NumberTowerEmit.emitFactorTwoLevel
  Hex.NumberTowerEmit.emitSplit "split/quadratic" [-2, 0, 1]
  Hex.NumberTowerEmit.emitSplit "split/repeated" [4, 0, -4, 0, 1]
  Hex.NumberTowerEmit.emitSplit "split/quartic" [6, 0, -5, 0, 1]
  Hex.NumberTowerEmit.emitFlattenRat
  Hex.NumberTowerEmit.emitFlattenSqrtTwo
  Hex.NumberTowerEmit.emitFlattenTwoLevel
