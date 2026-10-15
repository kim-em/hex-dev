/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RealModel
import HexRCF.SelectedRoot.Data
open Hex Lean Meta Qq Hex.RCF.RealCoefficients
namespace Hex.RCF.RealModelConformance
run_meta do
  let base ← mkAppM ``RealClosure.NumberField.rationalModel #[mkConst ``SelectedRootTests.Data.registry]
  let context ← mkAppM ``RealClosure.Tower.Context.pack #[← mkAppM ``RealClosure.Tower.Chain.base
    #[← mkAppM ``RealClosure.BaseContext.rational #[mkConst ``SelectedRootTests.Data.registry]]]
  let rational ← RealModel.build context base
  unless ← withTransparency .all (isDefEq rational base) do
    throwError "ordinary-real base model changed"
  let before := (← getMCtx).decls.toList.length
  let model ← RealModel.build (mkConst ``SelectedRootTests.Data.parent) base
  unless (← getMCtx).decls.toList.length == before do
    throwError "real model construction leaked metavariables"
  let value ← mkAppM ``RealClosure.Tower.Model.value #[model,mkConst ``SelectedRootTests.Data.alpha]
  let proof ← Hex.RCF.checkProof `nativeRealCoefficient (← mkEq value q(Real.sqrt 2))
    (mkConst ``SelectedRootTests.Data.alpha_value)
  let name := `Hex.RCF.RealModelConformance.selectedCoefficient
  addDecl (.thmDecl {name,levelParams:=[],type:= ← inferType proof,value:=proof})
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "constructed real-model coefficient has a forbidden axiom"
  for action in [RealModel.build context model,
      RealModel.build (mkConst ``SelectedRootTests.Data.parent) base 1] do
    let before := (← getMCtx).decls.toList.length
    let declined ← try (do let _ ← action; pure false) catch _ => pure true
    unless declined do throwError "mismatched base or exhausted model depth accepted"
    unless (← getMCtx).decls.toList.length == before do
      throwError "failed real model construction leaked metavariables"
  logInfo "retained rational and selected-root ordinary-real models checked; original coefficient, wrong base and depth refusal audited"
end Hex.RCF.RealModelConformance
