/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeFormula
public meta import HexRCF.RealCoefficients.NativeFormula
public meta import HexRCF.ProofEvidence
-- These private bodies are used only to reconstruct this concrete native fixture.
import all HexRealClosure.BaseContext
import all HexRealClosure.TowerSuffix
public section
namespace Hex.RCF.RealCoefficients.NativeFormulaConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open scoped HexMvPolyMathlib
private def registry : BaseContext.Registry := fun _ => none
private abbrev base := BaseContext.rational registry
private noncomputable def history : base.chain.Realization registry := by
  change (BaseContext.Chain.real (.base (registry := registry))).Realization registry
  exact .real .base (BaseContext.RealChain.interpretBase registry) .base
private abbrev staged := base.infinitesimal
private abbrev context := Context.base staged
private noncomputable def following : context.origin.base.Realization := by
  rw [Context.origin_base]
  change staged.chain.Realization registry
  rw [BaseContext.Context.infinitesimal_chain]
  exact .infinitesimal _ history
private def parameter : context.Value :=
  Context.baseValue (BaseContext.PackedContext.pack staged) RationalFn.X
private def formula : RealFormula.QF 1 :=
  .and (.atom ⟨MvPoly.X 0, .gt⟩) (.atom ⟨MvPoly.X 0 - 1, .lt⟩)
private def values : Fin 0 → context.Value := Fin.elim0
private def original : Fin 0 → ℝ := Fin.elim0
private theorem truth : Samples.Row.eval formula
    (NativeFormula.row context (Fin.snoc values parameter) formula) = some true := by
  decide +kernel
private def coefficient : context.Value := Context.baseValue
  (BaseContext.PackedContext.pack staged) (RationalFn.C (2 : Rat))
private theorem coefficient_real : context.origin.RealValue following coefficient 2 := by
  change ∃ b : BaseContext.Element staged, coefficient = b ∧
    BaseContext.Chain.Realization.RealValue _ b.stored 2
  refine ⟨coefficient, rfl, ?_⟩
  change ∃ b : Rat, RationalFn.C 2 = RationalFn.C b ∧ history.RealValue b 2
  refine ⟨2, rfl, ?_⟩
  change (BaseContext.RealChain.interpretBase registry).hom (2 : Rat) = 2
  norm_num [BaseContext.RealChain.interpretBase, BaseContext.RealContext.Interpretation.rational]
private def affine : RealFormula.QF 2 :=
  let c : RealFormula.Poly 2 := MvPoly.X 0
  let x : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨x, .gt⟩) (.and (.atom ⟨x - 1, .lt⟩)
    (.and (.atom ⟨c + x - 2, .gt⟩) (.atom ⟨c + x - 3, .lt⟩)))
private theorem affine_truth : Samples.Row.eval affine
    (NativeFormula.row context (Fin.snoc (fun _ : Fin 1 => coefficient) parameter) affine) =
    some true := by decide +kernel

/-- The fixed coefficient identity and every atom hold at one ordinary point. -/
theorem affine_real : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ 2 < 2 + x ∧ 2 + x < 3 := by
  have real := NativeFormula.exists_real context following (fun _ : Fin 1 => coefficient)
    (fun _ => 2) (fun _ => coefficient_real) parameter affine affine_truth
  obtain ⟨x, hx⟩ := real
  refine ⟨x, ?_⟩
  dsimp only [affine, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at hx
  unfold RealFormula.Poly.eval at hx
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at hx
  simpa [HexMvPolyMathlib.toMvPolynomial_X,
    HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_add,
    HexMvPolyMathlib.toMvPolynomial_one, RealFormula.append, sub_lt_zero,
    sub_pos, show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    show (3 : RealFormula.Poly 2) = MvPoly.C 3 from rfl] using hx
/-- info: 'Hex.RCF.RealCoefficients.NativeFormulaConformance.affine_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_real

private def zero : RealFormula.QF 1 := .atom ⟨MvPoly.X 0, .eq⟩
private theorem false_row : Samples.Row.eval zero
    (NativeFormula.row context (Fin.snoc values parameter) zero) = some false := by
  decide +kernel

/-- A positive native sample gives a real counterexample to a false universal. -/
theorem not_zero : ¬ ∀ x : ℝ, x = 0 := by
  have real := NativeFormula.not_forall context following values original
    (fun i => Fin.elim0 i) parameter zero false_row
  intro all
  apply real
  intro x
  dsimp only [zero, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simpa [HexMvPolyMathlib.toMvPolynomial_X, RealFormula.append] using all x
/-- info: 'Hex.RCF.RealCoefficients.NativeFormulaConformance.not_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_zero

/-- One ordinary point satisfies both native infinitesimal signs jointly. -/
theorem between : ∃ x : ℝ, 0 < x ∧ x < 1 := by
  have real := NativeFormula.exists_real context following values original
    (fun i => Fin.elim0 i) parameter formula truth
  dsimp only [formula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at real
  obtain ⟨x, hx⟩ := real
  refine ⟨x, ?_⟩
  unfold RealFormula.Poly.eval at hx
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial] at hx
  simpa [RealFormula.append, HexMvPolyMathlib.toMvPolynomial_X,
    HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_one, sub_lt_zero] using hx
/-- info: 'Hex.RCF.RealCoefficients.NativeFormulaConformance.between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms between

run_meta do
  for name in #[``affine_real, ``between] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``NativeFormula.exists_real) do
      Lean.throwError "real witness did not consume the native joint formula law"
  for (name, rowProof) in #[(``affine_real, ``affine_truth), (``between, ``truth)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf rowProof) do
      Lean.throwError "real witness did not consume the computed native row"
  unless ← Hex.RCF.ProofEvidence.contains ``not_zero
      (fun e => e.isConstOf ``NativeFormula.not_forall) do
    Lean.throwError "counterexample did not consume the native joint formula law"
/-- info: 'Hex.RCF.RealCoefficients.NativeFormula.polynomial_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.NativeFormula.polynomial_read

/-- info: 'Hex.RCF.RealCoefficients.NativeFormula.row_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.NativeFormula.row_real

/-- info: 'Hex.RCF.RealCoefficients.NativeFormula.exists_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.NativeFormula.exists_real

/-- info: 'Hex.RCF.RealCoefficients.NativeFormula.not_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.NativeFormula.not_forall

-- One reader must retain the nonlinear relation through two actual native levels.
private noncomputable def firstHistory : staged.chain.Realization registry := by
  rw [BaseContext.Context.infinitesimal_chain]
  exact .infinitesimal _ history
private abbrev second := staged.infinitesimal
private abbrev later := Context.base second
private noncomputable def laterHistory : later.origin.base.Realization := by
  rw [Context.origin_base]
  change second.chain.Realization registry
  rw [BaseContext.Context.infinitesimal_chain]
  exact .infinitesimal _ firstHistory
private def larger : later.Value := Context.baseValue
  (BaseContext.PackedContext.pack second) (RationalFn.C RationalFn.X)
private def smaller : later.Value := Context.baseValue
  (BaseContext.PackedContext.pack second) RationalFn.X
private def laterValues : Fin 2 → later.Value := ![larger, smaller]
private def laterFormula : RealFormula.QF 2 :=
  let a : RealFormula.Poly 2 := MvPoly.X 0
  let b : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨b, .gt⟩) (.and (.atom ⟨b - a ^ 2, .lt⟩)
    (.and (.atom ⟨a, .gt⟩) (.atom ⟨a - 1, .lt⟩)))
private theorem laterTruth : Samples.Row.eval laterFormula
    (NativeFormula.row later laterValues laterFormula) = some true := by decide +kernel

/-- Two successive native levels retain the nonlinear relation at one real reader. -/
theorem successive_real : ∃ a b : ℝ, 0 < b ∧ b < a ^ 2 ∧ 0 < a ∧ a < 1 := by
  obtain ⟨read, domain, closed, members, signs, fixed⟩ :=
    NativeFormula.row_real later laterHistory laterValues laterFormula
  have meaning := (Samples.Row.eval_true laterFormula _ _ signs).mp laterTruth
  refine ⟨read larger, read smaller, ?_⟩
  dsimp only [laterFormula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    laterValues, Function.comp_def, sub_lt_zero] using meaning

/-- info: 'Hex.RCF.RealCoefficients.NativeFormulaConformance.successive_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms successive_real
run_meta do
  unless ← Hex.RCF.ProofEvidence.contains ``successive_real
      (fun e => e.isConstOf ``NativeFormula.row_real) do
    Lean.throwError "successive values did not use one joint formula reader"
  unless ← Hex.RCF.ProofEvidence.contains ``successive_real
      (fun e => e.isConstOf ``laterTruth) do
    Lean.throwError "successive values did not consume the computed native row"
end Hex.RCF.RealCoefficients.NativeFormulaConformance
