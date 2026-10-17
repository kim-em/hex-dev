/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NumberField
public meta import HexRCF.Tactic
public meta section
namespace Hex.RCF.RealCoefficients.RealModel
open Hex Lean Meta

/-- Construct only the ordinary-real interpretation of the retained tower.
Each root uses the actual descriptor, frame and encoding proof. The supplied
base model must match the actual base; no new root or source identity is chosen. -/
private def buildCore (context baseModel : Expr) (fuel : Nat := 256) : MetaM Expr := do
  let packed ← withTransparency .all (whnf context)
  unless packed.getAppFn.isConstOf ``RealClosure.Tower.Context.pack do
    throwError "expected a retained packed tower"
  let model ← go fuel packed.getAppArgs.back!
  let expected ← mkAppOptM ``RealClosure.Tower.Model #[none, some context, some (mkConst ``Real), none, none]
  let binding ← mkAppOptM ``Eq.refl #[some expected, some model]
  let _ ← Hex.RCF.checkProof `nativeRealModel (← inferType binding) binding
  return model
where
  go (fuel : Nat) (chain : Expr) : MetaM Expr := do
    let fuel+1 := fuel | throwError "real tower model exhausted its depth bound"
    Core.checkSystem "rcf real tower model"
    let constructor ← withTransparency .all (whnf chain)
    let result ← if constructor.getAppFn.isConstOf ``RealClosure.Tower.Chain.base then
      pure baseModel
    else if constructor.getAppFn.isConstOf ``RealClosure.Tower.Chain.root then do
      let arguments := constructor.getAppArgs
      unless arguments.size ≥ 4 do throwError "invalid retained root constructor"
      let parent := arguments[arguments.size-4]!
      let before ← go fuel parent
      mkAppM ``RealClosure.Tower.Model.root #[parent,before,arguments[arguments.size-3]!,
        arguments[arguments.size-2]!,arguments.back!]
    else throwError "real tower model requires base/root constructors"
    let prefixContext ← mkAppM ``RealClosure.Tower.Context.pack #[chain]
    let expected ← mkAppOptM ``RealClosure.Tower.Model #[none,some prefixContext,some (mkConst ``Real),none,none]
    unless ← withTransparency .all (isDefEq (← inferType result) expected) do
      throwError "base or root model has a different retained context"
    return result


/-- Interpret a closed retained base/root tower in the ordinary reals using
its actual descriptors, frames and encoding proofs. The caller supplies the
real base model. Each prefix must have the original context type. This builds
an interpretation, not a source identity, certificate or real sample witness.
Failures restore state; successful auxiliary proof declarations remain private. -/
def build (context baseModel : Expr) (fuel : Nat := 256) : MetaM Expr := do
  let saved ← saveState
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `RealModel)
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <|
      withOptions (fun options => debug.skipKernelTC.set (Elab.async.set options false) false) do
    let context ← instantiateMVars context
    let baseModel ← instantiateMVars baseModel
    for expression in [context,baseModel] do
      unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do
        throwError "rcf: real tower model requires closed retained inputs"
    let context ← Hex.RCF.checkExpr `RealModel.context context
    let baseModel ← Hex.RCF.checkExpr `RealModel.base baseModel
    let model ← instantiateMVars (← buildCore context baseModel fuel)
    Hex.RCF.checkExpr `RealModel.result model) fun outcome => do
      match outcome with
      | some _ => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | none => saved.restore
  return result
end Hex.RCF.RealCoefficients.RealModel
