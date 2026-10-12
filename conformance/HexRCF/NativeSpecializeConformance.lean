/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeSpecialize
public meta import HexRCF.RealCoefficients.NativeSpecialize
public meta import HexRCF.ProofEvidence
-- These private bodies are used only to reconstruct this concrete native fixture.
import all HexRealClosure.BaseContext
import all HexRealClosure.TowerSuffix
public section
namespace Hex.RCF.RealCoefficients.NativeSpecializeConformance
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
    (NativeSpecialize.row context values parameter formula) = some true := by
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
    (NativeSpecialize.row context (fun _ : Fin 1 => coefficient) parameter affine) =
    some true := by decide +kernel

private def divisor : context.Value := coefficient - parameter
private theorem divisor_sign : context.sign divisor ≠ 0 := by decide +kernel

/-- Source atoms and the original divisor hold at the same ordinary point. -/
theorem affine_real : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ 2 < 2 + x ∧ 2 + x < 3 ∧ 2-x ≠ 0 := by
  obtain ⟨read, domain, closed, negative, present, sizes, hx, guards, real⟩ :=
    NativeSpecialize.true_real context following (fun _ : Fin 1 => coefficient)
      (fun _ => 2) (fun _ => coefficient_real) parameter affine [divisor]
      (fun a ha => by simpa only [List.mem_singleton.mp ha] using divisor_sign) affine_truth
  have coeff := real coefficient 2 coefficient_real
  have guard := (guards divisor (by simp)).2
  have mapped : read divisor = 2-read parameter := by
    change read (coefficient - parameter) = _
    rw [closed.read_sub _ _ coeff.1 present, coeff.2]
  rw [mapped] at guard
  refine ⟨read parameter, ?_⟩
  dsimp only [affine, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at hx
  unfold RealFormula.Poly.eval at hx
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at hx
  simpa [HexMvPolyMathlib.toMvPolynomial_X,
    HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_add,
    HexMvPolyMathlib.toMvPolynomial_one, RealFormula.append, sub_lt_zero,
    sub_pos, show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    show (3 : RealFormula.Poly 2) = MvPoly.C 3 from rfl, and_assoc] using And.intro hx guard
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecializeConformance.affine_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_real

private def degreeFormula : RealFormula.QF 2 :=
  let c : RealFormula.Poly 2 := MvPoly.X 0
  let x : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨2, .gt⟩) (.and (.atom ⟨0, .eq⟩)
    (.atom ⟨(c - 2) * x ^ 2 + x, .gt⟩))
private theorem native_sizes :
    (RepresentationSpecialize.prepare (fun _ : Fin 1 => coefficient) degreeFormula).map
      (fun p => p.size) = [1, 0, 2] := by decide +kernel
private theorem native_degrees :
    (RepresentationSpecialize.prepare (fun _ : Fin 1 => coefficient) degreeFormula).map
      (fun p => p.natDegree) = [0, 0, 1] := by decide +kernel

private theorem degree_truth : Samples.Row.eval degreeFormula
    (NativeSpecialize.row context (fun _ : Fin 1 => coefficient) parameter degreeFormula) =
      some true := by decide +kernel

/-- The true-row API retains sizes at the authenticated original coordinates,
including zero, a nonzero constant and cancellation of the quadratic term. -/
private theorem degree_real : ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
    Transport.Closed read domain ∧ read coefficient = 2 ∧
    degreeFormula.polys.map (fun q =>
      (RepresentationSpecialize.polynomial (fun _ : Fin 1 => (2 : ℝ)) q).size) = [1, 0, 2] ∧
    degreeFormula.polys.map (fun q =>
      (RepresentationSpecialize.polynomial (fun _ : Fin 1 => (2 : ℝ)) q).natDegree) = [0, 0, 1] := by
  obtain ⟨read, domain, closed, negative, present, sizes, truth, guards, fixed⟩ :=
    NativeSpecialize.true_real context following (fun _ : Fin 1 => coefficient)
      (fun _ => 2) (fun _ => coefficient_real) parameter degreeFormula [] (by simp) degree_truth
  refine ⟨read, domain, closed, (fixed _ _ coefficient_real).2, ?_, ?_⟩
  · exact (List.map_congr_left sizes).trans native_sizes
  · have degrees q (hq : q ∈ degreeFormula.polys) :
        (RepresentationSpecialize.polynomial (fun _ : Fin 1 => (2 : ℝ)) q).natDegree =
        (RepresentationSpecialize.polynomial (fun _ : Fin 1 => coefficient) q).natDegree := by
      rw [DensePoly.natDegree_eq_size_sub_one, DensePoly.natDegree_eq_size_sub_one, sizes q hq]
    exact (List.map_congr_left degrees).trans native_degrees

private def leadingFormula : RealFormula.QF 2 :=
  let c : RealFormula.Poly 2 := MvPoly.X 0
  let x : RealFormula.Poly 2 := MvPoly.X 1
  .atom ⟨c * x ^ 2 + x, .gt⟩
private theorem leading_size :
    (RepresentationSpecialize.prepare (fun _ : Fin 1 => parameter) leadingFormula).map
      (fun p => p.size) = [3] := by decide +kernel

private theorem parameter_sign : context.sign parameter = 1 := by decide +kernel

/-- One reader retains a positive infinitesimal coefficient, its negation, and
quadratic size, using the finite nonzero leading sign. -/
private theorem leading_real : ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
    Transport.Closed read domain ∧ domain parameter ∧ 0 < read parameter ∧
    domain (-parameter) ∧ read (-parameter) = -read parameter ∧
    leadingFormula.polys.map (fun q =>
      (RepresentationSpecialize.polynomial (read ∘ (fun _ : Fin 1 => parameter)) q).size) = [3] := by
  obtain ⟨read, domain, closed, negative, members, present, guards, sizes, signs, fixed⟩ :=
    NativeSpecialize.row_real context following (fun _ : Fin 1 => parameter)
      parameter leadingFormula [parameter]
  have integer : (SignType.sign (read parameter) : Int) = 1 :=
    (guards parameter (by simp)).2.trans parameter_sign
  have realSign : SignType.sign (read parameter) = 1 := by
    cases value : SignType.sign (read parameter) <;> simp_all
  obtain ⟨negMember, negRead⟩ := negative parameter present
  exact ⟨read, domain, closed, present, sign_eq_one_iff.mp realSign, negMember, negRead,
    (List.map_congr_left sizes).trans leading_size⟩
run_meta do
  for (name, law, computations) in #[(``degree_real, ``NativeSpecialize.true_real,
      #[``native_sizes, ``native_degrees, ``degree_truth]),
      (``leading_real, ``NativeSpecialize.row_real, #[``leading_size, ``parameter_sign])] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "specialization regression has an unexpected complete axiom inventory: {axioms}"
    Lean.logInfo "specialization regression: complete standard-three-axiom inventory"
    for marker in computations.push law do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf marker) do
        Lean.throwError "specialization regression omitted its computation or realization API"

private def zero : RealFormula.QF 1 := .atom ⟨MvPoly.X 0, .eq⟩
private theorem false_row : Samples.Row.eval zero
    (NativeSpecialize.row context values parameter zero) = some false := by
  decide +kernel

/-- A positive native sample gives a real counterexample to a false universal. -/
theorem not_zero : ¬ ∀ x : ℝ, x = 0 := by
  have real := NativeSpecialize.not_forall context following values original
    (fun i => Fin.elim0 i) parameter zero false_row
  intro all
  apply real
  intro x
  dsimp only [zero, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simpa [HexMvPolyMathlib.toMvPolynomial_X, RealFormula.append] using all x
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecializeConformance.not_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_zero

private def fixedZero : RealFormula.QF 2 :=
  .atom ⟨MvPoly.X 0 + MvPoly.X 1 - 2, .eq⟩
private theorem fixed_false : Samples.Row.eval fixedZero
    (NativeSpecialize.row context (fun _ : Fin 1 => coefficient) parameter fixedZero) =
      some false := by decide +kernel

/-- The false-row rewrite retains a fixed coefficient through the native level. -/
theorem not_fixed : ¬ ∀ x : ℝ, 2 + x = 2 := by
  have failure := NativeSpecialize.not_forall context following
    (fun _ : Fin 1 => coefficient) (fun _ => 2) (fun _ => coefficient_real)
    parameter fixedZero fixed_false
  intro all
  apply failure
  intro x
  dsimp only [fixedZero, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_add,
    HexMvPolyMathlib.toMvPolynomial_sub, RealFormula.append,
    show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl, sub_eq_zero] using all x
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecializeConformance.not_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_fixed

/-- One ordinary point satisfies both native infinitesimal signs jointly. -/
theorem between : ∃ x : ℝ, 0 < x ∧ x < 1 := by
  obtain ⟨read, domain, closed, negative, present, sizes, hx, guards, fixed⟩ :=
    NativeSpecialize.true_real context following values original
      (fun i => Fin.elim0 i) parameter formula [] (by simp) truth
  have real : ∃ x : ℝ, formula.toProp (RealFormula.append original x) :=
    ⟨read parameter, hx⟩
  dsimp only [formula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at real
  obtain ⟨x, hx⟩ := real
  refine ⟨x, ?_⟩
  unfold RealFormula.Poly.eval at hx
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial] at hx
  simpa [RealFormula.append, HexMvPolyMathlib.toMvPolynomial_X,
    HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_one, sub_lt_zero] using hx
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecializeConformance.between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms between

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
private def laterFormula : RealFormula.QF 2 :=
  let a : RealFormula.Poly 2 := MvPoly.X 0
  let b : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨b, .gt⟩) (.and (.atom ⟨b - a ^ 2, .lt⟩)
    (.and (.atom ⟨a, .gt⟩) (.atom ⟨a - 1, .lt⟩)))
private theorem laterTruth : Samples.Row.eval laterFormula
    (NativeSpecialize.row later (fun _ : Fin 1 => larger) smaller laterFormula) = some true := by decide +kernel

/-- Two successive native levels retain the nonlinear relation at one real reader. -/
theorem successive_real : ∃ a b : ℝ, 0 < b ∧ b < a ^ 2 ∧ 0 < a ∧ a < 1 := by
  obtain ⟨read, domain, closed, negative, members, present, guards, sizes, signs, fixed⟩ :=
    NativeSpecialize.row_real later laterHistory (fun _ : Fin 1 => larger) smaller laterFormula
  have meaning := (Samples.Row.eval_true laterFormula _ _ signs).mp laterTruth
  refine ⟨read larger, read smaller, ?_⟩
  dsimp only [laterFormula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, Function.comp_def, sub_lt_zero] using meaning

/-- info: 'Hex.RCF.RealCoefficients.NativeSpecializeConformance.successive_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms successive_real
run_meta do
  unless ← Hex.RCF.ProofEvidence.contains ``successive_real
      (fun e => e.isConstOf ``NativeSpecialize.row_real) do
    Lean.throwError "successive values did not use one joint formula reader"
  unless ← Hex.RCF.ProofEvidence.contains ``successive_real
      (fun e => e.isConstOf ``laterTruth) do
    Lean.throwError "successive values did not consume the computed native row"
run_meta do
  for (name, rowProof, law) in #[(``affine_real, ``affine_truth, ``NativeSpecialize.true_real),
      (``between, ``truth, ``NativeSpecialize.true_real),
      (``not_zero, ``false_row, ``NativeSpecialize.not_forall),
      (``not_fixed, ``fixed_false, ``NativeSpecialize.not_forall)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf rowProof) do
      Lean.throwError "consumer omitted the computed specialized row"
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      Lean.throwError "consumer omitted the specialized realization law"
end Hex.RCF.RealCoefficients.NativeSpecializeConformance

/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.polynomial_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSpecialize.polynomial_read
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.eval_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSpecialize.eval_read
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.row_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSpecialize.row_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.true_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSpecialize.true_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.not_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSpecialize.not_forall
