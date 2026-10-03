/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.ProductionProgressTests

open RealCoefficients

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
private abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
private abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
private abbrev Certificate := FieldBuild.Result SquareTwo.polynomial SquareTwo.square hw hp Unit 2
private theorem real : SquareTwo.square.meetsRealAxis = true := by decide
private def values : Fin 1 → PolyQuot SquareTwo.polynomial root := fun _ =>
  SquareTwo.coordinate SquareTwo.square hw hp

private def nonnegative : RealFormula.QF 2 :=
  .atom ⟨-(MvPoly.X 1 - MvPoly.X 0) ^ 2, .le⟩
private def further : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))
private def repeated : RealFormula.QF 2 :=
  .and (.atom ⟨(MvPoly.X 1 - MvPoly.X 0) ^ 2, .eq⟩)
    (.and (.atom ⟨(MvPoly.X 1 + MvPoly.X 0) ^ 3, .eq⟩)
      (.and (.atom ⟨(MvPoly.X 1 - MvPoly.X 0) ^ 2, .le⟩)
        (.atom ⟨MvPoly.X 1 - MvPoly.X 1, .eq⟩)))

private def allValue (data : Certificate) (formula : RealFormula.QF 2) : Option Bool :=
  data.allValue values formula
private def anyValue (data : Certificate) (formula : RealFormula.QF 2) : Option Bool :=
  data.anyValue values formula

private def positive := FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp
  real values nonnegative ()
#guard positive.val.isolation.isolations.intervals.size == 1
#guard allValue positive.val nonnegative == some true
#guard (FieldBuild.signKeys values nonnegative positive.val.radical.core
  positive.val.isolation positive.val.rootSigns).all fun key => (positive.val.signs.lookup? key).isSome

private def fourthRoot := FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp
  real values further ()
#guard fourthRoot.val.isolation.isolations.intervals.size == 4
#guard anyValue fourthRoot.val further == some true
#guard allValue fourthRoot.val further == some false

-- Incompatible common-root conditions are a false verdict, not failed production.
private def incompatible := FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp
  real values repeated ()
#guard incompatible.val.isolation.isolations.intervals.size == 2
#guard anyValue incompatible.val repeated == some false
#guard allValue incompatible.val repeated == some false

-- Constant/zero atoms and an empty atom list still get the checked count-one
-- coefficient environment; their carrier has no root sections.
#guard (FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp real values
  (.tt : RealFormula.QF 2) ()).val.isolation.isolations.intervals.isEmpty
#guard (FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp real values
  (.atom ⟨0, .eq⟩ : RealFormula.QF 2) ()).val.isolation.isolations.intervals.isEmpty

-- Original caller guards are literal finite hits even when not needed by atoms.
private def guardKey : PolyQuot SquareTwo.polynomial root := values 0 - 4
private def guarded := FieldBuild.produce SquareTwo.polynomial SquareTwo.square hw hp
  real values nonnegative () [guardKey, guardKey]
#guard (guarded.val.signs.lookup? guardKey).isSome

-- The following ordinary kernel proofs use production laws. They do not
-- reduce the search or replace quotation of literal source-goal certificates.
theorem positive_checked : positive.val.checkEvidence values nonnegative () = true := positive.property.1
theorem positive_keys (key : PolyQuot SquareTwo.polynomial root)
    (requested : key ∈ FieldBuild.signKeys values nonnegative positive.val.radical.core
      positive.val.isolation positive.val.rootSigns) :
    (positive.val.signs.lookup? key).isSome = true := positive.property.2 key requested

theorem universal_decision : ∃ verdict, positive.val.allValue values nonnegative = some verdict ∧
    (verdict = true ↔ ∀ x, nonnegative.toProp (RealFormula.append
      (fun j => Field.value (Field.literalRep SquareTwo.polynomial SquareTwo.square hw hp) (values j)) x)) :=
  positive.val.forall_decision values nonnegative () positive.property.1 positive.property.2

theorem existential_decision : ∃ verdict, fourthRoot.val.anyValue values further = some verdict ∧
    (verdict = true ↔ ∃ x, further.toProp (RealFormula.append
      (fun j => Field.value (Field.literalRep SquareTwo.polynomial SquareTwo.square hw hp) (values j)) x)) :=
  fourthRoot.val.exists_decision values further () fourthRoot.property.1 fourthRoot.property.2

#guard positive.val.signs.entries.length ==
  (FieldBuild.signKeys values nonnegative positive.val.radical.core
    positive.val.isolation positive.val.rootSigns).dedup.length

end Hex.RCF.ProductionProgressTests

/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.build_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.LiteralSign.Table.build_bindings
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.build_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.LiteralSign.Table.build_lookup
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.build_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.LiteralSign.Table.build_success
/-- info: 'Hex.RCF.RealCoefficients.Field.literal_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.literal_domain
/-- info: 'Hex.RCF.RealCoefficients.Field.literalSign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.literalSign_spec
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.buildTable_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.buildTable_build
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.buildTable_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.buildTable_lookup
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.buildTable_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.buildTable_success
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.build_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.build_progress
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateUsing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateUsing
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.isolateFormulaUsing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.isolateFormulaUsing
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.produce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.produce
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.Result.forall_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.Result.forall_decision
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.Result.exists_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.FieldBuild.Result.exists_decision
/-- info: 'Hex.RCF.RealCoefficients.doubling_cofinal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.doubling_cofinal
/-- info: 'Hex.RealFormula.QF.evalSigns_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealFormula.QF.evalSigns_congr
/-- info: 'Hex.RCF.RealCoefficients.forall_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.forall_decision
/-- info: 'Hex.RCF.RealCoefficients.exists_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.exists_decision
/-- info: '_private.HexRCF.ProductionProgress.0.Hex.RCF.ProductionProgressTests.positive_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.ProductionProgressTests.positive_checked
/-- info: '_private.HexRCF.ProductionProgress.0.Hex.RCF.ProductionProgressTests.positive_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.ProductionProgressTests.positive_keys
/-- info: '_private.HexRCF.ProductionProgress.0.Hex.RCF.ProductionProgressTests.universal_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.ProductionProgressTests.universal_decision
/-- info: '_private.HexRCF.ProductionProgress.0.Hex.RCF.ProductionProgressTests.existential_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.ProductionProgressTests.existential_decision
