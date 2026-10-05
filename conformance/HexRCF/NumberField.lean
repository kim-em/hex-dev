/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.NumberField
import all HexRCF.RealCoefficients.NumberField
public meta import HexRCF.RealCoefficients.NumberField
public meta import HexRCF.Tactic
public meta import HexRCF.ProofEvidence
public import HexRealClosure.RootFrame
public meta import HexRealClosure.RootFrame

public section

open Hex Hex.RealClosure Hex.RCF.RealCoefficients
namespace Hex.RCF.NumberFieldTests
private def registry : BaseContext.Registry := fun _ => none
private def schema : RealFormula.QF 2 :=
  let x : RealFormula.Poly 2 := MvPoly.X 1
  let q := x^2 - MvPoly.X 0
  .and (.atom ⟨q, .eq⟩) (.and (.atom ⟨q^2, .ge⟩)
    (.and (.atom ⟨1-x, .lt⟩) (.atom ⟨x-2, .le⟩)))
private def selected (lower upper : Rat) : Option RealAlgebraicNumber := do
  let d ← Root.validate 7
    { context := 7, head := DensePoly.ofList [-2,0,1],
      lower := .finite lower, upper := .finite upper, indices := [], signs := [] }
  pure d.handle.canonical
private def decideSelected (lower upper : Rat) : Option Bool :=
  match selected lower upper with
  | none => none
  | some generator =>
    NumberField.run generator registry
      (fun _ : Fin 1 => generator.toAlgebraic.toQAdjoin) schema .existsReal
#guard decideSelected 1 2 = some true
#guard decideSelected (-2) (-1) = some false

private def cubic : Option RealAlgebraicNumber := do
  let d ← Root.validate 8
    { context := 8, head := DensePoly.ofList [-2,0,0,1],
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  pure d.handle.canonical
private def decideCubic : Option Bool :=
  match cubic with
  | none => none
  | some generator =>
    NumberField.run generator registry
      (fun _ : Fin 1 => generator.toAlgebraic.toQAdjoin) schema .existsReal
#guard decideCubic = some true

/-- Exercise the owner factory, original QAdjoin arithmetic and native cell
folds together. These are compiled diagnostics, not quoted source proofs. -/
private def controls : Bool := Id.run do
  let some generator := selected 1 2 | return false
  let g := generator.toAlgebraic.toQAdjoin
  let values := fun _ : Fin 1 => g
  let x : RealFormula.Poly 2 := MvPoly.X 1
  let a : RealFormula.Poly 2 := MvPoly.X 0
  let run := NumberField.run generator registry values
  let domain := fun lower upper : RealFormula.Poly 2 =>
    RealFormula.QF.and (.atom ⟨lower-x, .lt⟩) (.atom ⟨x-upper, .le⟩)
  let zero := RealFormula.QF.atom ⟨x, .eq⟩
  let comparisons := [RealFormula.Cmp.eq, .ne, .lt, .le, .gt, .ge]
  let signs := [false, true, false, false, true, true]
  let constants := (comparisons.zip signs).all fun (cmp, expected) =>
    run (.atom ⟨a, cmp⟩) .forallReal == some expected &&
      run (.atom ⟨a, cmp⟩) .existsReal == some expected
  let computed : Fin 2 → QAdjoin generator.toAlgebraic :=
    fun i => if i.val = 0 then g else g*g-1
  let ordered := RealFormula.QF.atom
    ⟨MvPoly.X 2 ^ 2 + MvPoly.X 0 - MvPoly.X 1, .gt⟩
  let swapped : Fin 2 → QAdjoin generator.toAlgebraic :=
    fun i => if i.val = 0 then g*g-1 else g
  let cancelled := RealFormula.QF.atom ⟨(a*a-2)*x^3+x, .eq⟩
  return constants &&
    run schema .forallReal == some false &&
    run (.atom ⟨a-a, .eq⟩) .forallReal == some true &&
    run cancelled .existsReal == some true &&
    run cancelled .forallReal == some false &&
    run (.and zero (domain 0 1)) .existsReal == some false &&
    run (.and zero (domain (-1) 0)) .existsReal == some true &&
    run (domain 1 1) .existsReal == some false &&
    run (domain 2 1) .existsReal == some false &&
    run (.imp (domain 2 1) .ff) .forallReal == some true &&
    run (.or (.not .ff) .ff) .forallReal == some true &&
    NumberField.run generator registry computed ordered .forallReal == some true &&
    NumberField.run generator registry swapped ordered .forallReal == some false

#guard controls
/-- Fresh-module ordinary-kernel composition at the original selected values.
No concrete compiled diagnostic is used as a proof of a real sentence. -/
theorem original (generator : RealAlgebraicNumber)
    (registry : BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, NumberField.run generator registry values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => Hex.RealClosure.NumberField.value generator (values i))) :=
  NumberField.run_spec generator registry values formula quantifier

end Hex.RCF.NumberFieldTests

/-- info: 'Hex.RCF.RealCoefficients.NumberField.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.NumberField.run_spec
run_meta do
  Hex.RCF.checkAxioms ``Hex.RCF.RealCoefficients.NumberField.run_spec
    (Lean.mkConst ``Hex.RCF.RealCoefficients.NumberField.run_spec)
  Hex.RCF.checkAxioms ``Hex.RCF.RealCoefficients.NumberField.run_total
    (Lean.mkConst ``Hex.RCF.RealCoefficients.NumberField.run_total)
  Hex.RCF.checkAxioms ``Hex.RCF.RealCoefficients.NumberField.run_true
    (Lean.mkConst ``Hex.RCF.RealCoefficients.NumberField.run_true)

/-- info: 'Hex.RCF.NumberFieldTests.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.NumberFieldTests.original
run_meta do
  Hex.RCF.checkAxioms ``Hex.RCF.NumberFieldTests.original
    (Lean.mkConst ``Hex.RCF.NumberFieldTests.original)
  unless ← Hex.RCF.ProofEvidence.contains ``Hex.RCF.NumberFieldTests.original
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.NumberField.run_spec) do
    throwError "original-field proof must use the public formula law"
  let info ← Lean.getConstInfo ``Hex.RCF.RealCoefficients.NumberField.run_spec
  let some body := info.value? (allowOpaque := true)
    | throwError "missing original-field correctness proof"
  unless body.find? (fun e => e.isConstOf
      ``Hex.RealClosure.NumberField.present?_success) |>.isSome do
    throwError "original-field law must consume the owner's actual factory theorem"
  unless body.find? (fun e => e.isConstOf
      ``Hex.RealClosure.NumberField.Presentation.pack_value) |>.isSome do
    throwError "original-field law must preserve the owner's selected embedding"
