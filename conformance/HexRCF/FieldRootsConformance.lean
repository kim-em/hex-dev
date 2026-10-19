/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.FieldRootsTests
open RealCoefficients

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
private abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
private abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
private theorem real : SquareTwo.square.meetsRealAxis = true := by decide
private def values : Fin 1 → PolyQuot SquareTwo.polynomial root := fun _ =>
  SquareTwo.coordinate SquareTwo.square hw hp
private abbrev rep := Field.literalRep SquareTwo.polynomial SquareTwo.square hw hp
private abbrev hrep := Field.literalRep_mk SquareTwo.polynomial SquareTwo.square hw hp

private def close : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 - MvPoly.X 0, .eq⟩)
    (.atom ⟨5444517870735015415413993718908291383296 *
      (MvPoly.X 1 - MvPoly.X 0) - 1, .lt⟩)

-- The complete API must also avoid reconstructing the already selected field.
private def complete := FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp
  real values close () (depth := 0)
#guard complete.val.isolation.isolations.intervals.size == 2
theorem complete_checked : complete.val.checkEvidence values close () = true :=
  complete.property.1
#guard Field.checkSignTable SquareTwo.polynomial SquareTwo.square hw hp complete.val.signs
#guard complete.val.radical.check () (FieldCarrier.product values close)
#guard complete.val.isolation.check complete.val.finiteSign FieldDecision.point ()
  complete.val.radical.core
#guard complete.val.rootSigns.check complete.val.finiteSign FieldDecision.point ()
  complete.val.radical.core (FieldReplay.intervals complete.val.isolation)
  (FieldSpecialize.literalPolynomial values) close
#guard complete.val.anyValue values close == some true
#guard complete.val.allValue values close == some false
#guard match FieldBuild.build SquareTwo.polynomial SquareTwo.square hw hp values close () 256 with
  | some data => data.anyValue values close == some true && data.allValue values close == some false
  | none => false

-- Finite extraction distinguishes universal zero roots from empty constant roots.
#guard (FieldBuild.roots? rep hrep (0 : DensePoly (PolyQuot SquareTwo.polynomial root))).isNone
#guard (FieldBuild.roots? rep hrep (1 : DensePoly (PolyQuot SquareTwo.polynomial root))).map
  Array.size == some 0
#guard (FieldBuild.proposeRoots rep hrep
  (1 : DensePoly (PolyQuot SquareTwo.polynomial root)) 1).map
  (fun cert => cert.intervals.size) == some 0

end Hex.RCF.FieldRootsTests

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.polynomial_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.polynomial_complex
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.roots_meaning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.roots_meaning
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.roots_sorted
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.roots_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.roots_finite
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.roots_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.roots_binding
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_progress
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_spec
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.proposeRoots_accepted

/-- info: '_private.HexRCF.FieldRootsConformance.0.Hex.RCF.FieldRootsTests.complete_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.FieldRootsTests.complete_checked

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith_checked

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith_build
