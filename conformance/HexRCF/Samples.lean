/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public meta import HexRCF.RealCoefficients.Samples
public import HexRCF.TowerSamples
public meta import HexRCF.TowerSamples
public meta import HexRealClosure.TowerContext

public section

/-! Native production and ordinary-real semantics. Raw row probes check length
mismatches; they are not tests of literal certificate or nested-evidence checking. -/

namespace Hex.RCF.RealCoefficients.SamplesTests
open Hex.RCF.RealCoefficients.Samples
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients.TowerSamples

def decisions : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some positive := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | return false
  let some negative := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite (-(1 + 1)), upper := .finite (-1), indices := [], signs := [] }
    | return false
  let positiveValues := fun _ : Fin 1 => (extension positive).generator
  let negativeValues := fun _ : Fin 1 => (extension negative).generator
  let vx : RealFormula.Poly 2 := MvPoly.X 1
  let square := RealFormula.QF.atom ⟨(vx - MvPoly.X 0) ^ 2, .ge⟩
  let positiveConstant := RealFormula.QF.atom ⟨vx ^ 2 + MvPoly.X 0, .gt⟩
  let mixedValues := fun _ : Fin 2 => (extension positive).generator
  let g := (extension positive).generator
  let distinctValues : Fin 2 → (extension positive).context.Value :=
    fun i => if i.val = 0 then g else g * g - 1
  let swappedValues : Fin 2 → (extension positive).context.Value :=
    fun i => if i.val = 0 then g * g - 1 else g
  let coordinateOrder := RealFormula.QF.atom
    ⟨MvPoly.X 2 ^ 2 + MvPoly.X 0 - MvPoly.X 1, .gt⟩
  return run positiveValues schema .existsReal == some true &&
    run positiveValues schema .forallReal == some false &&
    run negativeValues schema .existsReal == some false &&
    run negativeValues square .forallReal == some true &&
    run positiveValues positiveConstant .forallReal == some true &&
    run negativeValues positiveConstant .forallReal == some false &&
    run distinctValues coordinateOrder .forallReal == some true &&
    run swappedValues coordinateOrder .forallReal == some false &&
    run mixedValues mixed .existsReal == some true &&
    run mixedValues mixed .forallReal == some false

#guard decisions

end Hex.RCF.RealCoefficients.SamplesTests

/-- info: 'Hex.RCF.RealCoefficients.Samples.Row.eval_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.Row.eval_true
/-- info: 'Hex.RCF.RealCoefficients.Samples.Row.eval_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.Row.eval_total
/-- info: 'Hex.RCF.RealCoefficients.Samples.section_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.section_formula
/-- info: 'Hex.RCF.RealCoefficients.Samples.sector_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.sector_formula
/-- info: 'Hex.RCF.RealCoefficients.Samples.cell_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.cell_formula
/-- info: 'Hex.RCF.RealCoefficients.Samples.cell_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.cell_real

#guard Hex.RCF.RealCoefficients.Samples.Row.eval
  (Hex.RealFormula.QF.tt : Hex.RealFormula.QF 1) [] == some true
#guard Hex.RCF.RealCoefficients.Samples.Row.eval
  (Hex.RealFormula.QF.tt : Hex.RealFormula.QF 1) [0] == none
#guard Hex.RCF.RealCoefficients.Samples.Row.eval
  (.and .ff (.atom ⟨Hex.MvPoly.X 0, .eq⟩) : Hex.RealFormula.QF 1) [] == none
#guard Hex.RCF.RealCoefficients.Samples.Row.eval
  (.or .tt (.atom ⟨Hex.MvPoly.X 0, .eq⟩) : Hex.RealFormula.QF 1) [] == none

namespace Hex.RCF.RealCoefficients.SamplesTests
open Hex.RCF.RealCoefficients.Samples
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients.TowerSamples

def rationalDecisions : Bool := Id.run do
  let values : Fin 0 → base.Value := Fin.elim0
  let x : RealFormula.Poly 1 := MvPoly.X 0
  let domain := fun a b : RealFormula.Poly 1 =>
    RealFormula.QF.and (.atom ⟨a - x, .lt⟩) (.atom ⟨x - b, .le⟩)
  let zero := RealFormula.QF.atom ⟨x, .eq⟩
  let excluded := RealFormula.QF.and zero (domain 0 1)
  let included := RealFormula.QF.and zero (domain (-1) 0)
  let comparisons := [RealFormula.Cmp.eq, .ne, .lt, .le, .gt, .ge]
  let constants := fun (coefficient : RealFormula.Poly 1) (expected : List Bool) =>
    (comparisons.zip expected).all fun (comparison, wanted) =>
      let formula := RealFormula.QF.atom ⟨coefficient, comparison⟩
      run values formula .forallReal == some wanted &&
        run values formula .existsReal == some wanted
  let squares := fun (quantifier : RealFormula.Quantifier) (expected : List Bool) =>
    (comparisons.zip expected).all fun (comparison, wanted) =>
      run values (.atom ⟨x ^ 2, comparison⟩) quantifier == some wanted
  return run values (domain 1 2) .existsReal == some true &&
    run values (domain 1 1) .existsReal == some false &&
    run values (domain 2 1) .existsReal == some false &&
    run values excluded .existsReal == some false &&
    run values included .existsReal == some true &&
    run values .tt .forallReal == some true &&
    run values .ff .existsReal == some false &&
    run values (.atom ⟨0, .eq⟩) .forallReal == some true &&
    constants (-1) [false, true, true, true, false, false] &&
    constants 0 [true, false, false, true, false, true] &&
    constants 1 [false, true, false, false, true, true] &&
    squares .forallReal [false, false, false, false, false, true] &&
    squares .existsReal [true, true, false, true, true, true] &&
    comparisons.all (fun comparison =>
      let atom := RealFormula.QF.atom ⟨x, comparison⟩
      run values (.or atom (.not atom)) .forallReal == some true)

#guard rationalDecisions

end Hex.RCF.RealCoefficients.SamplesTests

/-- info: 'Hex.RCF.RealCoefficients.Samples.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.run_spec
/-- info: 'Hex.RCF.RealCoefficients.Samples.run_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Samples.run_true

namespace Hex.RCF.RealCoefficients.SamplesTests
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients

example {registry : BaseContext.Registry}
    {parent : Context registry}
    (original : Model parent ℝ)
    (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1))
    (quantifier : RealFormula.Quantifier) :
    ∃ result, Samples.run values formula quantifier =
        some result ∧
      (result = true ↔
        (RealFormula.Prenex.quant quantifier
          (.matrix formula)).toProp
          (fun i => original.value (values i))) := by
  exact Samples.run_spec original values formula quantifier

example (d : TowerSamples.Selection) :
    ∃ result,
      Samples.run
        (fun _ : Fin 1 =>
          (TowerSamples.extension d).generator)
        TowerSamples.schema .existsReal = some result ∧
      (result = true ↔ ∃ x : ℝ,
        TowerSamples.schema.toProp
          (RealFormula.append
            (fun _ : Fin 1 => (TowerSamples.model d).value
              (TowerSamples.extension d).generator) x)) := by
  exact Samples.run_spec (TowerSamples.model d)
    (fun _ : Fin 1 => (TowerSamples.extension d).generator)
    TowerSamples.schema .existsReal

end Hex.RCF.RealCoefficients.SamplesTests
