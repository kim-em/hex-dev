/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.Field
import HexRCF.RealCoefficients.CommonPresentation
import HexRCF.RealCoefficients.SquareTwo

open Hex Hex.RCF.RealCoefficients

namespace Hex.RCF.LiteralSignConformance

private def cubePoly : ZPoly := DensePoly.ofList [-2, 0, 0, 1]
private def cubeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 5411319705 32, 0, 32⟩
private theorem cubeWitness : atomWitness cubePoly cubeSquare := by decide +kernel
private theorem cubePrecision :
    (mahlerPrec cubePoly : Int) ≤ cubeSquare.prec := by decide +kernel
private theorem cubeIrred :
    ZPoly.checkIrredWitness cubePoly (.eisenstein 2 0) = true := by decide +kernel
private theorem cubeDegree : 0 < cubePoly.natDegree := by decide +kernel
private theorem cubeReal : cubeSquare.meetsRealAxis = true := by decide +kernel

private abbrev CubeField := PolyQuot cubePoly
  (SimpleRoot.ofSquare cubePoly cubeSquare cubeWitness cubePrecision)

private def root : CubeField :=
  PolyQuot.ofSquare cubePoly cubeSquare (DensePoly.ofList [0, 1])
    cubeWitness cubePrecision

private def negative : CubeField := root - 2
private def vanishing : CubeField := root * root * root - 2

private def table? : Option (LiteralSign.Table CubeField) :=
  LiteralSign.Table.build (ZPoly.toRatPoly cubePoly)
    (cubeSquare.re - cubeSquare.radiusHi).toRat
    (cubeSquare.re + cubeSquare.radiusHi).toRat
    [root, root * root, negative, vanishing,
      CommonPresentation.discSlack cubeSquare root] PolyQuot.coeffs

#guard match table? with
  | none => false
  | some table =>
      Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision table &&
      table.entries.map (·.value) == [1, 1, -1, 0, 1] &&
      table.lookup? root == some 1 &&
      table.lookup? (root * root) == some 1 &&
      table.lookup? negative == some (-1) &&
      table.lookup? vanishing == some 0 &&
      CommonPresentation.checkEntry cubeWitness cubePrecision table
        (ZPoly.toRatPoly cubePoly) cubeSquare root &&
      CommonPresentation.checkPresentation cubeWitness cubePrecision table
        (fun _ : Fin 1 => ZPoly.toRatPoly cubePoly)
        (fun _ => cubeSquare) (fun _ => root) &&
      !CommonPresentation.checkEntry cubeWitness cubePrecision table
        (DensePoly.ofList [-3, 0, 1]) cubeSquare root &&
      !CommonPresentation.checkEntry cubeWitness cubePrecision table
        (ZPoly.toRatPoly cubePoly) { cubeSquare with re := cubeSquare.re + 1 } root &&
      (table.lookup? (root + 1)).isNone &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with head := table.head + 1 } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with lower := table.lower + 1 } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with upper := table.upper + 1 } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with count := { table.count with value := 2 } } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with entries := table.entries.map fun entry =>
            { entry with evidence := { entry.evidence with queryPoly := 1 } } } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with entries := table.entries.map fun entry =>
            { entry with value := entry.value + 1 } }

private abbrev SquareField := PolyQuot SquareTwo.polynomial
  (SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square
    (by decide +kernel) (by decide +kernel))

private def squareRoot : SquareField :=
  PolyQuot.ofSquare SquareTwo.polynomial SquareTwo.square
    (DensePoly.ofList [0, 1]) (by decide +kernel) (by decide +kernel)

private def squareTable? : Option (LiteralSign.Table SquareField) :=
  LiteralSign.Table.build (ZPoly.toRatPoly SquareTwo.polynomial)
    (SquareTwo.square.re - SquareTwo.square.radiusHi).toRat
    (SquareTwo.square.re + SquareTwo.square.radiusHi).toRat
    [CommonPresentation.discSlack SquareTwo.square squareRoot,
      CommonPresentation.discSlack SquareTwo.square (-squareRoot)]
    PolyQuot.coeffs

/- The opposite conjugate satisfies the same source equation, but the
recorded enclosure sign rejects it. -/
#guard match squareTable? with
  | none => false
  | some table =>
      CommonPresentation.checkEquation (ZPoly.toRatPoly SquareTwo.polynomial)
        (-squareRoot) &&
      CommonPresentation.checkEntry (by decide +kernel) (by decide +kernel)
        table (ZPoly.toRatPoly SquareTwo.polynomial) SquareTwo.square squareRoot &&
      !CommonPresentation.checkEntry (by decide +kernel) (by decide +kernel)
        table (ZPoly.toRatPoly SquareTwo.polynomial) SquareTwo.square (-squareRoot)

/-- The selected embedding reflects zero using a short irreducibility witness. -/
theorem cubeZero (a : CubeField) :
    Field.value (Field.literalRep cubePoly cubeSquare cubeWitness cubePrecision) a = 0 ↔
      a = 0 := by
  letI : ZPoly.CheckedIrreducible cubePoly :=
    Field.checkedIrreducible cubePoly (.eisenstein 2 0) cubeIrred cubeDegree
  exact Field.value_eq_zero
    (Field.literalRep cubePoly cubeSquare cubeWitness cubePrecision)
    (Field.literalRep_mk cubePoly cubeSquare cubeWitness cubePrecision)
    (Field.literalRep_real cubePoly cubeSquare cubeWitness cubePrecision cubeReal) a

/-- info: 'Hex.RCF.LiteralSignConformance.cubeZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeZero

/-- info: 'Hex.RCF.RealCoefficients.Field.checkSignTable_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Field.checkSignTable_spec

/-- info: 'Hex.RCF.RealCoefficients.CommonPresentation.checkPresentation_sound' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CommonPresentation.checkPresentation_sound

end Hex.RCF.LiteralSignConformance
