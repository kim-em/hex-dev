/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NativeSamples
import HexRCF.NativeSampleModelLiterals
import HexRealClosure.RootReplay
import HexRCF.ProofEvidence
import HexRCF.Tactic
import HexRealClosure.BaseContext
import HexRealClosure.TowerSuffix
import HexRealClosure.Sample
import HexRealClosure.TowerTransport
import HexRealClosure.TowerContext
import HexRationalFn.Field
import HexRealClosure.BaseJson

/-! Oracle: checked frozen descriptor for the positive root of X²−ε in (0,1),
the actual staged ordered real-closed reference model, and native signs;
mode: always. The original ε guard crosses the section’s extension embedding.
One finite reader preserves the guard and the strict sample conditions. -/
namespace Hex.RCF.RealCoefficients.NativeSampleModelConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
open scoped HexMvPolyTheory
def registry : BaseContext.Registry := fun _ => none
abbrev base := BaseContext.rational registry
private noncomputable def history : base.chain.Realization registry := by
  change (BaseContext.Chain.real (.base (registry := registry))).Realization registry
  exact .real .base (BaseContext.RealChain.interpretBase registry) .base
abbrev staged := base.infinitesimal
abbrev context := Context.base staged
private noncomputable def following : context.origin.base.Realization := by
  rw [Context.origin_base]
  change staged.chain.Realization registry
  rw [BaseContext.Context.infinitesimal_chain]
  exact .infinitesimal _ history
private noncomputable def reference : (BaseContext.PackedContext.pack staged).Reference := by
  exact (show (BaseContext.PackedContext.pack staged).Realization from following).reference
def parameter : context.Value :=
  Context.baseValue (BaseContext.PackedContext.pack staged) RationalFn.X
private def root? := Hex.RealClosure.Algebraic.RootReplay.readDescriptor context.codec
  (contextCodec context.signature) context.sign context.signature
  Hex.RCF.RealCoefficients.NativeSampleModelLiterals.subject Hex.RCF.RealCoefficients.NativeSampleModelLiterals.graph
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 32768 in
private theorem accepted : root?.toOption.isSome = true := by decide +kernel
private def descriptor := root?.toOption.get accepted
set_option maxRecDepth 32768 in
private theorem subject : descriptor.raw =
    ⟨context.signature, DensePoly.ofCoeffs #[-parameter, 0, 1], .finite 0, .finite 1,
      [1, 2], [1, 1]⟩ := by decide +kernel

def sample : Tower.Sample context := Tower.Sample.section context descriptor
private noncomputable def original : Model context reference.Carrier := reference.model
private noncomputable def conversion : Conversion.Model sample.input original :=
  Classical.choose (Tower.Sample.section_correct descriptor original)
private noncomputable def targetHistory : sample.input.context.origin.base.Realization := by
  change (context.adjoin descriptor).context.origin.base.Realization
  rw [Context.origin_adjoin, Origin.snoc_base]
  exact following
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

private theorem native_square :
    sample.value * sample.value - sample.input.value parameter = 0 := by decide +kernel

/-- The selected-root sample and the original parent guard have one ordinary
reader; that reader is closed on the returned finite domain. -/
theorem guarded_reader : ∃ read : sample.input.context.Value → ℝ,
    ∃ domain : sample.input.context.Value → Prop,
      Transport.Closed read domain ∧ domain sample.value ∧
      0 < read sample.value ∧ read sample.value < 1 ∧
      read sample.value * read sample.value = read (sample.input.value parameter) ∧
      domain (sample.input.value parameter) ∧ read (sample.input.value parameter) ≠ 0 := by
  obtain ⟨read, domain, closed, negative, present, sizes, meaning, guards, fixed⟩ :=
    Hex.RCF.RealCoefficients.NativeSamples.true_real original sample conversion targetHistory values source
      (fun i => Fin.elim0 i) formula [parameter]
      (fun a ha => by simpa only [List.mem_singleton.mp ha] using nonzero) truth
  have guard := guards parameter (by simp)
  have square := congrArg read native_square
  rw [closed.read_sub _ _ (closed.mul _ _ present present) guard.1,
    closed.read_mul _ _ present present, closed.read_zero] at square
  have equation := sub_eq_zero.mp square
  refine ⟨read, domain, closed, present, ?_⟩
  dsimp only [formula, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_one, RealFormula.append, sub_lt_zero, and_assoc] using And.intro meaning (And.intro equation guard)

/-- info: 'Hex.RCF.RealCoefficients.NativeSampleModelConformance.guarded_reader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded_reader
/-- info: '_private.HexRCF.NativeSampleModelConformance.0.Hex.RCF.RealCoefficients.NativeSampleModelConformance.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subject
/-- info: '_private.HexRCF.NativeSampleModelConformance.0.Hex.RCF.RealCoefficients.NativeSampleModelConformance.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted
/-- info: '_private.HexRCF.NativeSampleModelConformance.0.Hex.RCF.RealCoefficients.NativeSampleModelConformance.truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truth

#guard root?.toOption.isSome
#guard Samples.Row.eval formula (sample.signs (RepresentationSpecialize.prepare values formula)) == some true

run_meta do
  for (name, laws) in #[(``truth, #[``NativeSamples.row_converted,
        ``BaseContext.PackedContext.Realization.reference]),
      (``guarded_reader, #[``NativeSamples.true_real, ``truth,
        ``Tower.Sample.section_correct, ``nonzero, ``native_square])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "sample model consumer omitted a native premise or conversion model"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "sample model consumer has an unexpected complete axiom inventory"
end Hex.RCF.RealCoefficients.NativeSampleModelConformance
