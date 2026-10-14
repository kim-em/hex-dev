/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Data
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Refusals
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
private def missingUnit := Packings.facts.filter
  (fun entry => entry.original != DensePoly.C (1 : Rat))
elab "#finite_matrix_refusals" : command => liftTermElabM do
  let cases ← `(term| [
    (Read.selected false Inputs.facts .null Packings.facts Signs.facts).isNone,
    (Read.selected true Inputs.facts Literals.canonical Packings.facts Signs.facts).isNone,
    (Read.selected false [] Literals.canonical Packings.facts Signs.facts).isNone])
  let goal ← Term.elabType (← `(($cases).all id = true))
  Term.synthesizeSyntheticMVarsNoPostponing
  let goal ← instantiateMVars goal
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked
    `Hex.RCF.RealCoefficients.FiniteMatrixTests.Refusals.checked goal (← mkDecideProof goal)
    #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
    #[``Read.selected]
#finite_matrix_refusals

/-- The owner's replay dictionaries are a kernel assembly boundary. Their
compiled implementation can compute a missing record; the kernel must refuse
that unrecorded reduction, with a typed mismatch rather than a resource error. -/
elab "#finite_matrix_missing" : command => liftTermElabM do
  let goals ← `(term| [
    (Read.selected false Inputs.facts Literals.canonical missingUnit Signs.facts).isSome,
    (Read.selected false Inputs.facts Literals.canonical Packings.facts []).isSome])
  for i in [:2] do
    let statement ← Term.elabType (← `(($goals)[$(quote i)]! = true))
    Term.synthesizeSyntheticMVarsNoPostponing
    let statement ← instantiateMVars statement
    let decision ← mkDecide statement
    let statement ← mkEq decision (mkConst ``Bool.true)
    let reduced ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) decision)
    if reduced.isConstOf ``Bool.true || reduced.isConstOf ``Bool.false then
      throwError "missing-record decision reduced to a Boolean instead of stopping"
    let proof ← mkEqRefl (mkConst ``Bool.true)
    let options ← getOptions
    let result := (← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
      (maxRecDepth.get options).toUSize (.thmDecl {
        name := Name.num `Hex.RCF.RealCoefficients.FiniteMatrixTests.Refusals.missing i,
        levelParams := [], type := statement, value := proof}) none (doCheck := true)
    match result with
    | .error (.declTypeMismatch ..) => pure ()
    | .error error => throwKernelException error
    | .ok _ => throwError "kernel accepted an unrecorded operation"
#finite_matrix_missing
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Refusals
