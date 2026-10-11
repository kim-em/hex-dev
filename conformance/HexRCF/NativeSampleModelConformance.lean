/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeSamples
public meta import HexRCF.ProofEvidence
public meta import HexRCF.Tactic
-- Private data bodies reconstruct this concrete infinitesimal-parent fixture.
import all HexRealClosure.BaseContext
import all HexRealClosure.TowerSuffix
import all HexRealClosure.Sample
import all HexRealClosure.TowerTransport

/-! Oracle: actual native signs and the owner’s staged ordered real-closed model;
mode: always. The guard is the same unfixed native value as the sample, rather
than an inherited rational coordinate. Ordinary-kernel proofs and complete
axiom/consumption checks validate the conversion and joint real conclusion. -/
public section
namespace Hex.RCF.RealCoefficients.NativeSampleModelConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
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
private noncomputable def reference : (BaseContext.PackedContext.pack staged).Reference := by
  exact (show (BaseContext.PackedContext.pack staged).Realization from following).reference
private def parameter : context.Value :=
  Context.baseValue (BaseContext.PackedContext.pack staged) RationalFn.X
private def sample : Tower.Sample context := Tower.Sample.ofRoot (.point parameter)
private noncomputable def original : Model context reference.Carrier := reference.model
private noncomputable def conversion : Conversion.Model sample.input original :=
  Conversion.Model.identity original
private noncomputable def targetHistory : sample.input.context.origin.base.Realization := following
private def values : Fin 0 → context.Value := Fin.elim0
private def source : Fin 0 → ℝ := Fin.elim0
private def formula : RealFormula.QF 1 :=
  .and (.atom ⟨MvPoly.X 0, .gt⟩) (.atom ⟨MvPoly.X 0 - 1, .lt⟩)
private theorem native_truth : Samples.Row.eval formula
    (Hex.RCF.RealCoefficients.NativeSpecialize.row sample.input.context
      (sample.input.value ∘ values) sample.value formula) = some true := by decide +kernel
private theorem truth : Samples.Row.eval formula
    (sample.signs (Hex.RCF.RealCoefficients.RepresentationSpecialize.prepare values formula)) = some true := by
  rw [Hex.RCF.RealCoefficients.NativeSamples.row_converted original sample conversion]
  exact native_truth
private theorem nonzero : context.sign parameter ≠ 0 := by decide +kernel

/-- An actual sample over an infinitesimal parent retains its unfixed original
guard at the same finite reader as the strict interval conditions. -/
theorem guarded_real : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x ≠ 0 := by
  obtain ⟨read, domain, closed, negative, present, sizes, meaning, guards, fixed⟩ :=
    Hex.RCF.RealCoefficients.NativeSamples.true_real original sample conversion targetHistory values source
      (fun i => Fin.elim0 i) formula [parameter]
      (fun a ha => by simpa only [List.mem_singleton.mp ha] using nonzero) truth
  have guard := (guards parameter (by simp)).2
  have same : sample.input.value parameter = sample.value := by rfl
  rw [same] at guard
  refine ⟨read sample.value, ?_⟩
  dsimp only [formula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_one, RealFormula.append, sub_lt_zero, and_assoc] using And.intro meaning guard

/-- info: '_private.HexRCF.NativeSampleModelConformance.0.Hex.RCF.RealCoefficients.NativeSampleModelConformance.truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truth
/-- info: 'Hex.RCF.RealCoefficients.NativeSampleModelConformance.guarded_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded_real

run_meta do
  for (name, laws) in #[(``truth, #[``NativeSamples.row_converted,
        ``BaseContext.PackedContext.Realization.reference]),
      (``guarded_real, #[``NativeSamples.true_real, ``truth, ``nonzero])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "infinitesimal sample consumer omitted a conversion, model or original guard"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "infinitesimal sample consumer has an unexpected complete axiom inventory"
end Hex.RCF.RealCoefficients.NativeSampleModelConformance
