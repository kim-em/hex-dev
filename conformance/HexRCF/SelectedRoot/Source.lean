/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Row
import HexRealFormulaMathlib.Semantics

open Hex Hex.RealClosure Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.SelectedRootTests.Source
open Hex.RCF.SelectedRootTests

theorem schema_real (x : ℝ) :
    schema.toProp (Samples.valuation original values x) ↔
      x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  have two : HexMvPolyMathlib.toMvPolynomial (2 : RealFormula.Poly 2) = 2 := by
    change HexMvPolyMathlib.toMvPolynomial (MvPoly.C (2 : Int)) = 2
    simp
  simp only [schema, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp, RealFormula.Poly.eval,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [Samples.valuation, RealFormula.append, values, two, alpha_value, sub_eq_zero,
    sub_pos, sub_neg]

theorem source (facts : List (Algebraic.SignFact native))
    (accepted : Row.rowResult facts = .ok true) :
    ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  unfold Row.rowResult at accepted
  cases packet : Row.packetRead facts with
  | error message => simp only [packet] at accepted; contradiction
  | ok evidence =>
    simp only [packet] at accepted
    erw [Row.evaluate_eq] at accepted
    obtain ⟨x, truth⟩ := SelectedFormula.row_sound original values [] schema context evidence accepted
    exact ⟨x, (schema_real x).mp truth⟩

/-- info: 'Hex.RCF.SelectedRootTests.Source.schema_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schema_real
/-- info: 'Hex.RCF.SelectedRootTests.Source.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
end Hex.RCF.SelectedRootTests.Source
