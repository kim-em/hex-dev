/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.FieldSpecialize
import HexRCF.RealCoefficients.SignInputs
import HexRCF.RealCoefficients.FieldCarrier

open Hex Hex.RCF.RealCoefficients Hex.RealFormula

namespace Hex.RCF.FieldSpecializeConformance

private def cubePoly : ZPoly := DensePoly.ofList [-2, 0, 0, 1]
private def cubeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 5411319705 32, 0, 32⟩
private theorem cubeWitness : atomWitness cubePoly cubeSquare := by decide +kernel
private theorem cubePrecision :
    (mahlerPrec cubePoly : Int) ≤ cubeSquare.prec := by decide +kernel
private theorem cubeReal : cubeSquare.meetsRealAxis = true := by decide +kernel
private theorem cubeIrred :
    ZPoly.checkIrredWitness cubePoly (.eisenstein 2 0) = true := by decide +kernel
private theorem cubeDegree : 0 < cubePoly.natDegree := by decide +kernel

private abbrev CubeField := PolyQuot cubePoly
  (SimpleRoot.ofSquare cubePoly cubeSquare cubeWitness cubePrecision)

private def root : CubeField :=
  PolyQuot.ofSquare cubePoly cubeSquare (DensePoly.ofList [0, 1])
    cubeWitness cubePrecision

private def atom : RealFormula.Poly 2 := MvPoly.X 1 - MvPoly.X 0

private def specialized : DensePoly CubeField :=
  FieldSpecialize.literalPolynomial (fun _ : Fin 1 => root) atom

-- The executable substitution uses only the reduced rational coordinates.
#guard specialized.natDegree = 1
#guard specialized.coeff 0 = -root
#guard specialized.coeff 1 = 1

private def formula : RealFormula.QF 2 := .atom ⟨atom, .eq⟩
private def carrier : DensePoly CubeField :=
  FieldCarrier.product (fun _ : Fin 1 => root) formula
#guard carrier = specialized

private instance : ZPoly.CheckedIrreducible cubePoly :=
  Field.checkedIrreducible cubePoly (.eisenstein 2 0) cubeIrred cubeDegree
private noncomputable instance : Field CubeField :=
  Hex.PolyQuot.field cubePoly
    (SimpleRoot.ofSquare cubePoly cubeSquare cubeWitness cubePrecision)

/-- The compiled polynomial denotes the source atom at the selected real root. -/
theorem atom_real (x : ℝ) :
    FieldSpecialize.evaluate
      (FieldSpecialize.realHom
        (Field.literalRep cubePoly cubeSquare cubeWitness cubePrecision)
        (Field.literalRep_mk cubePoly cubeSquare cubeWitness cubePrecision)
        (Field.literalRep_real cubePoly cubeSquare cubeWitness cubePrecision cubeReal))
      x specialized =
    atom.eval (append
      (fun _ : Fin 1 => Field.value
        (Field.literalRep cubePoly cubeSquare cubeWitness cubePrecision) root) x) := by
  exact FieldSpecialize.literalPolynomial_real
    (Field.literalRep cubePoly cubeSquare cubeWitness cubePrecision)
    (Field.literalRep_mk cubePoly cubeSquare cubeWitness cubePrecision)
    (Field.literalRep_real cubePoly cubeSquare cubeWitness cubePrecision cubeReal)
    (fun _ : Fin 1 => root) atom x

/-- info: 'Hex.RCF.FieldSpecializeConformance.atom_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atom_real

/-- info: 'Hex.RCF.RealCoefficients.FieldCarrier.atom_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FieldCarrier.atom_roots

/-- info: 'Hex.RCF.RealCoefficients.FieldCarrier.product_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FieldCarrier.product_ne_zero

private def ratHead : DensePoly Rat := DensePoly.ofList [-2, 0, 0, 1]
private def ratQuery : DensePoly Rat := DensePoly.ofList [0, 1]
private def ratDomain? : Option (Sturm.PreparedDomain Rat) :=
  Sturm.prepare Sturm.orderSign ratHead (.finite 1) (.finite 2)

-- Replayed signs are exactly those collected from literal Tarski evidence.
#guard match ratDomain? with
  | none => false
  | some domain =>
      let cert : TarskiCertificate Rat Rat Unit :=
        Sturm.certifyPrepared () domain ratQuery
      let keys := SignInputs.certificate ratHead (.finite 1) (.finite 2) cert
      let recorded : Rat → Int := fun a =>
        if keys.contains a then Sturm.orderSign a else 2
      Sturm.check recorded () ratHead ratQuery (.finite 1) (.finite 2)
        cert.value cert

end Hex.RCF.FieldSpecializeConformance
