/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.PolynomialIsolation
import HexRCF.ProofEvidence
import Lean

set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Hex.RCF.PolynomialIsolation
open RealCoefficients Hex.RealClosure HexPolyTheory.Interpret

private noncomputable def evaluation : E →+* ℝ :=
  HexMvPolyTheory.eval₂Hom (Rat.castHom ℝ) (fun _ => Real.pi)

private theorem parameter_value : evaluation parameter = Real.pi := by
  change MvPoly.eval₂ (Rat.castHom ℝ) (fun _ : Fin 1 => Real.pi) parameter = Real.pi
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp [parameter]

private theorem constant_value (q : Rat) : evaluation (MvPoly.C q) = (q : ℝ) := by
  change MvPoly.eval₂ (Rat.castHom ℝ) (fun _ : Fin 1 => Real.pi) (MvPoly.C q) = (q : ℝ)
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp

theorem point_spec (d : Dyadic) :
    read (point d) = HexRealRootsTheory.Dyadic.toReal d := by
  unfold read PolynomialBounds.value point
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp [HexRealRootsTheory.toReal_eq_cast_toRat]

theorem head_eval (x : ℝ) :
    (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial read head)).eval x =
        (x ^ 2 - Real.pi) * (x - 1) * (x - 2) := by
  have identity (p : DensePoly ℝ) :
      interpret (fun y : ℝ => y) (fun _ => Iff.rfl) p = HexPolyTheory.toPolynomial p := by
    ext i
    simp only [coeff_interpret, HexPolyTheory.coeff_toPolynomial]
  rw [identity]
  change (HexPolyTheory.toPolynomial
    (Transport.polynomial (fun q => evaluation q) head)).eval x = _
  have two : evaluation (2 : E) = 2 := by
    change evaluation (MvPoly.C (2 : Rat)) = 2
    simpa using constant_value 2
  have three : evaluation (3 : E) = 3 := by
    change evaluation (MvPoly.C (3 : Rat)) = 3
    simpa using constant_value 3
  simp [head, DensePoly.ofList,
    Transport.polynomial_ofCoeffs (fun q => evaluation q) evaluation.map_zero,
    HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, parameter_value, two, three]
  ring

/-- The source existential follows from the complete checked geometry and the
caller's containment proof, without an independence or convergence hypothesis. -/
theorem original : ∃ x : ℝ, x ^ 2 = Real.pi ∧ 1 < x ∧ x < 2 := by
  obtain ⟨roots, located, _, _, _⟩ := IsolationTransport.roots lookup read read_closed
    lookup_spec point point_spec () head frozen accepted
  let i : Fin frozen.isolations.intervals.size := ⟨2, by decide +kernel⟩
  have lower : frozen.isolations.intervals[i].lower.toRat = (95 / 64 : Rat) := by
    decide +kernel
  have upper : frozen.isolations.intervals[i].upper.toRat = (1835 / 1024 : Rat) := by
    decide +kernel
  have lowerReal : (1 : ℝ) ≤
      HexRealRootsTheory.Dyadic.toReal frozen.isolations.intervals[i].lower := by
    rw [HexRealRootsTheory.toReal_eq_cast_toRat, lower]
    norm_num
  have upperReal : HexRealRootsTheory.Dyadic.toReal
      frozen.isolations.intervals[i].upper ≤ (2 : ℝ) := by
    rw [HexRealRootsTheory.toReal_eq_cast_toRat, upper]
    norm_num
  have above : 1 < roots i := lowerReal.trans_lt (located i).2.1
  have below : roots i < 2 := (located i).2.2.trans_le upperReal
  have equation : (roots i ^ 2 - Real.pi) * (roots i - 1) * (roots i - 2) = 0 := by
    rw [← head_eval]
    exact (located i).1
  have last : roots i - 2 ≠ 0 := ne_of_lt (sub_neg.mpr below)
  have first : roots i - 1 ≠ 0 := ne_of_gt (sub_pos.mpr above)
  have root := (mul_eq_zero.mp ((mul_eq_zero.mp equation).resolve_right last)).resolve_right first
  exact ⟨roots i, sub_eq_zero.mp root, above, below⟩

end Hex.RCF.PolynomialIsolation

open Lean Meta Hex Hex.RCF.RealCoefficients

run_meta withoutExporting do
  let laws := #[``QueryReplay.leading_spec, ``QueryReplay.transport, ``QueryReplay.checked,
    ``IsolationTransport.checked, ``IsolationTransport.roots, ``PolynomialBounds.closed,
    ``PolynomialBounds.enclose_sound, ``PolynomialBounds.sign_spec,
    ``Hex.RCF.PolynomialIsolation.read_closed, ``Hex.RCF.PolynomialIsolation.lookup_spec,
    ``Hex.RCF.PolynomialIsolation.point_spec, ``Hex.RCF.PolynomialIsolation.head_eval]
  let definitions := #[``IsolationTransport.check, ``IsolationTransport.keys,
    ``IsolationTransport.map, ``PolynomialBounds.enclose, ``PolynomialBounds.sign?,
    ``PolynomialBounds.value]
  let source := ``Hex.RCF.PolynomialIsolation.original
  let accepted := ``Hex.RCF.PolynomialIsolation.accepted
  let .thmInfo outer ← getConstInfo accepted | throwError "expected checked isolation theorem"
  let some retained := outer.value.getAppFn.constName? |
    throwError "expected retained ordinary-kernel isolation proof"
  let bodies := laws ++ definitions ++ #[source, accepted, retained]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies bodies
  for forbidden in #[``ZPoly.CheckedIrreducible, ``Field.value_eq_zero, ``Field.value_inv,
      ``Field.value_div, ``Field.prepareSign, ``FieldBuild.buildTable,
      ``FieldRootSigns.Table.build, ``RadicalCert.build, ``IsolationReplay.build,
      ``FieldIsolate.propose?, ``FieldIsolate.proposeWith?, ``FieldIsolate.fromQuery?,
      ``TarskiCertificate.certify, ``TarskiCertificate.fromChains,
      ``SignedRemainderChain.build, ``Sturm.prepare, ``Sturm.certifyPrepared,
      ``Sturm.queryPrepared, ``QAdjoin.common] do
    if dependencies.contains forbidden then
      throwError "source pi proof depends on a producer or source field law: {forbidden}"
  let mut traces : Nat := 0
  for name in bodies do
    let axioms ← collectAxioms name
    unless axioms.all (fun name => [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "unexpected pi source proof axioms: {name}: {axioms}"
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__piBody})
      | .defnInfo info =>
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__piData})
      | _ => throwError "expected actual pi replay theorem or definition body: {name}"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let nonempty := !(Kernel.getDiagnostics checked).unfoldCounter.isEmpty
    if nonempty then traces := traces + 1
    if name == source && !nonempty then throwError "source proof recheck has no conversion trace"
  unless bodies.size == 21 do throwError "missing actual pi proof or replay body"
  let actualAxioms ← collectAxioms source
  unless actualAxioms.toList.mergeSort Name.quickLt ==
      [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
    throwError "unexpected complete original pi proof axioms: {actualAxioms}"
  logInfo m!"FRESH_POLYNOMIAL_PI: bodies={bodies.size}; traces={traces}; dependencies={dependencies.size}; original existential checked; no producer, source field law or nonstandard axiom"
