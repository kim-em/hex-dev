/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
namespace Hex.RCF.RadicalProgressTests
open RealCoefficients
attribute [local instance 2000] Field.toGrindField
-- The raw derivative gcd is not monic: X³ is reduced to X/3.
private def repeated : DensePoly Rat := DensePoly.ofCoeffs #[0,0,0,1]
#guard ((RadicalCert.build () repeated).map (fun cert => cert.core.toArray)) == some #[0,1/3]
#guard ((RadicalCert.build () repeated).map (fun cert => cert.check () repeated)) == some true
#guard ((RadicalCert.build true repeated).map (fun cert => cert.check false repeated)) == some false
#guard ((RadicalCert.build () (DensePoly.C (3 : Rat))).map
  (fun cert => cert.core.natDegree)) == some 0
#guard (RadicalCert.build () (0 : DensePoly Rat)).isNone
private def accepted := RadicalCert.reduce () repeated
  (RadicalCert.build_success_real (fun a : Rat => (a : ℝ))
    (fun a => by simp) (by simp) (fun a b => by simp)
    (fun a b => by simp) (fun a b => by simp) (fun a b => by simp)
    (fun n => by simp) () repeated (by decide))
#guard accepted.val.core.toArray == #[0,1/3]
#guard accepted.val.check () repeated
private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev rep := Field.literalRep SquareTwo.polynomial SquareTwo.square (by decide) (by decide)
private abbrev root := SimpleRoot.mk rep
private def coefficient : PolyQuot SquareTwo.polynomial root :=
  SquareTwo.coordinate SquareTwo.square (by decide) (by decide)
private def common : DensePoly (PolyQuot SquareTwo.polynomial root) :=
  DensePoly.natPow (DensePoly.ofCoeffs #[-coefficient,1]) 2 *
    DensePoly.natPow (DensePoly.ofCoeffs #[coefficient,1]) 3
#guard ((RadicalCert.build () common).map (fun cert => cert.core.natDegree)) == some 2
#guard ((RadicalCert.build () common).map (fun cert => cert.quotient.natDegree)) == some 3
#guard ((RadicalCert.build () common).map (fun cert => cert.check () common)) == some true

#guard ((RadicalCert.build () common).map (fun cert =>
  (FieldBuild.isolateAt rep rfl () cert.core 8).map
    (fun isolated => isolated.isolations.intervals.size))) == some (some 2)
private theorem repReal : rep.root.im = 0 :=
  Field.literalRep_real SquareTwo.polynomial SquareTwo.square (by decide) (by decide) (by decide)
open scoped Hex.PolyQuot.QAdjoinField in
private theorem commonNe : common ≠ 0 := by
  have linearNe (a : PolyQuot SquareTwo.polynomial root) : DensePoly.ofCoeffs #[a,1] ≠ 0 := by
    intro zero
    have identity := congrArg (fun poly : DensePoly (PolyQuot SquareTwo.polynomial root) => poly.coeff 1) zero
    simp only [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
      DensePoly.coeff_zero] at identity
    exact one_ne_zero identity
  have powerNe (poly : DensePoly (PolyQuot SquareTwo.polynomial root)) (nonzero : poly ≠ 0)
      (n : Nat) : DensePoly.natPow poly n ≠ 0 := by
    induction n with
    | zero => rw [DensePoly.natPow_zero]; exact DensePoly.monic_ne_zero DensePoly.monic_one
    | succ n ih => rw [DensePoly.natPow_succ]; exact DensePoly.mul_ne_zero ih nonzero
  exact DensePoly.mul_ne_zero (powerNe _ (linearNe _) 2) (powerNe _ (linearNe _) 3)
private def reduced := RadicalCert.reduce () common
  (RadicalCert.build_success_real (Field.value rep) (Field.value_eq_zero rep rfl repReal)
    (Field.value_one rep rfl repReal) (Field.value_add rep rfl repReal)
    (Field.value_sub rep rfl repReal) (Field.value_mul rep rfl repReal)
    (Field.value_div rep rfl repReal) (Field.value_natCast rep rfl repReal)
    () common commonNe)
#guard reduced.val.core.natDegree == 2
private def isolated := FieldBuild.isolate rep rfl repReal () reduced.val.core
  (RadicalCert.core_ne_zero () common reduced.val reduced.property.2)
  (RadicalCert.build_squarefree (Field.value rep) (Field.value_eq_zero rep rfl repReal)
    (Field.value_sub rep rfl repReal) (Field.value_mul rep rfl repReal)
    (Field.value_div rep rfl repReal) (Field.value_natCast rep rfl repReal)
    () common reduced.val reduced.property.1)
#guard isolated.val.isolations.intervals.size == 2

private def formula : RealFormula.QF 2 :=
  .and (.atom ⟨(MvPoly.X 1 - MvPoly.X 0) ^ 2, .eq⟩)
    (.and (.atom ⟨(MvPoly.X 1 + MvPoly.X 0) ^ 3, .eq⟩)
      (.and (.atom ⟨(MvPoly.X 1 - MvPoly.X 0) ^ 2, .le⟩)
        (.atom ⟨MvPoly.X 1 - MvPoly.X 1, .eq⟩)))
private def values : Fin 1 → PolyQuot SquareTwo.polynomial root := fun _ => coefficient
private def envelope := FieldBuild.isolateFormula rep rfl repReal () values formula
#guard envelope.fst.val.core.natDegree == 2
#guard envelope.snd.val.isolations.intervals.size == 2
#guard envelope.fst.val.check () (FieldCarrier.product values formula)
#guard envelope.snd.val.check (FieldBuild.proposalSign rep rfl) FieldDecision.point
  () envelope.fst.val.core

-- Domain guard atoms stay in the carrier, including their exact endpoint roots.
private def guarded : RealFormula.QF 2 :=
  .and (.atom ⟨-MvPoly.X 1 - 2, .lt⟩)
    (.and (.atom ⟨MvPoly.X 1 - 2, .le⟩) formula)
#guard (FieldBuild.isolateFormula rep rfl repReal () values guarded).snd.val.isolations.intervals.size == 4
#guard (FieldBuild.isolateFormula rep rfl repReal () values (.tt : RealFormula.QF 2)).snd.val.isolations.intervals.isEmpty
#guard (FieldBuild.isolateFormula rep rfl repReal () values
  (.atom ⟨0, .eq⟩ : RealFormula.QF 2)).snd.val.isolations.intervals.isEmpty

-- The total envelope is consumed by the actual repeated-atom query builder.
#guard (FieldRootSigns.Table.build (FieldBuild.proposalSign rep rfl) FieldDecision.point
  () envelope.fst.val.core envelope.snd.val
  (FieldSpecialize.literalPolynomial values) formula).isSome

-- The following kernel proofs use the producer's checked acceptance law.
-- They do not reduce the search or replace literal certificate quotation.
theorem formula_radical_checked : envelope.fst.val.check () (FieldCarrier.product values formula) = true :=
  envelope.fst.property.2
theorem formula_isolation_checked : envelope.snd.val.check (FieldBuild.proposalSign rep rfl)
    FieldDecision.point () envelope.fst.val.core = true := envelope.snd.property.1

end Hex.RCF.RadicalProgressTests
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_core
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_nonzero
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_fromIdentities' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_fromIdentities
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_success
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_success_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_success_real
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.build_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.build_squarefree
/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RadicalCert.reduce

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateFormula
/-- info: '_private.HexRCF.RadicalProgress.0.Hex.RCF.RadicalProgressTests.formula_radical_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RadicalProgressTests.formula_radical_checked
/-- info: '_private.HexRCF.RadicalProgress.0.Hex.RCF.RadicalProgressTests.formula_isolation_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RadicalProgressTests.formula_isolation_checked
