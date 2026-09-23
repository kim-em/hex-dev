/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.Field

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

private def table? : Option (LiteralSign.Table CubeField) :=
  LiteralSign.Table.build (ZPoly.toRatPoly cubePoly)
    (cubeSquare.re - cubeSquare.radiusHi).toRat
    (cubeSquare.re + cubeSquare.radiusHi).toRat
    [root, root * root] PolyQuot.coeffs

#guard match table? with
  | none => false
  | some table =>
      Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision table &&
      table.entries.map (·.value) == [1, 1] &&
      table.lookup? root == some 1 &&
      table.lookup? (root * root) == some 1 &&
      (table.lookup? (root * root * root)).isNone &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with head := table.head + 1 } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with lower := table.lower + 1 } &&
      !Field.checkSignTable cubePoly cubeSquare cubeWitness cubePrecision
        { table with entries := table.entries.map fun entry =>
            { entry with value := entry.value + 1 } }

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

end Hex.RCF.LiteralSignConformance
