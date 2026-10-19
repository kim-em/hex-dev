/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardJoint
public import KernelReplay.FramePublic
import all KernelReplay.GuardJoint
meta import Lean.Meta.Closure

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJointExport
open Lean Meta Elab Command

private def evaluation (context read point : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``Element #[context]
  withLocalDeclD `value carrier fun value => do
    let polynomial ← mkAppM ``Element.polynomial #[value]
    mkLambdaFVars #[value] (← mkAppM ``Packing.eval #[read, point, polynomial])

private def withWitnesses (count : Nat) (type : Expr)
    (action : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  match count with
  | 0 => action #[] type
  | count + 1 =>
    unless type.getAppFn.isConstOf ``Exists do throwError "public joint witness shape changed"
    let .lam name domain body _ := type.getAppArgs[1]! |
      throwError "public joint witness predicate is not explicit"
    withLocalDeclD name domain fun value => do
      let body ← withWitnesses count (body.instantiate1 value) fun later predicate =>
        action (#[value] ++ later) predicate
      mkAppM ``Exists #[← mkLambdaFVars #[value] body]

private abbrev ExportM := MonadCacheT ExprStructEq Expr MetaM

/-- Preserve the expected proposition when sharing a proof argument. Inferring
the proof's type can instead retain a `Bool.Reflects` reduction that requires
private computational bodies in an importing module. -/
private partial def shareProofs (e : Expr) : ExportM Expr := do
  checkSystem "share public joint proof arguments"
  if e.isAtomic then return e
  checkCache { val := e : ExprStructEq } fun _ => do
    let binders (xs : Array Expr) (k : ExportM Expr) : ExportM Expr := do
      let instances ← getLocalInstances
      let mut lctx ← getLCtx
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let decl := decl.setType (← shareProofs decl.type)
        let decl ← match decl.value? (allowNondep := true) with
          | some value => pure <| decl.setValue (← shareProofs value)
          | none => pure decl
        lctx := lctx.modifyLocalDecl x.fvarId! fun _ => decl
      withLCtx lctx instances k
    match e with
    | .lam .. | .letE .. => lambdaLetTelescope e fun xs body => binders xs do
        mkLambdaFVars xs (← shareProofs body) (usedLetOnly := false)
          (generalizeNondepLet := false)
    | .forallE .. => forallTelescope e fun xs body => binders xs do
        mkForallFVars xs (← shareProofs body)
    | .mdata _ body => return e.updateMData! (← shareProofs body)
    | .proj _ _ body => return e.updateProj! (← shareProofs body)
    | .app .. => e.withApp fun f args => do
        let f ← shareProofs f
        let mut signature ← inferType f
        let mut shared := #[]
        for arg in args do
          let .forallE _ expected body _ ← withTransparency .all (whnf signature)
            | throwError "joint export application lost its function type"
          let arg ← if ← isProp expected then
              withExporting (isExporting := true) do
                mkAuxTheorem expected arg (zetaDelta := true)
            else shareProofs arg
          shared := shared.push arg
          signature := body.instantiate1 arg
        return mkAppN f shared
    | _ => return e

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
set_option Elab.async false in
set_option debug.skipKernelTC false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let original := (← getConstInfo ``GuardJoint.Statement).value!
  let setup ← GuardDescriptorInputs.prepare
  let second ← FiniteData.Prefix.ofData (mkConst ``GuardSecondData.data)
    (mkConst ``GuardDescriptorPoint.zero) (mkConst ``GuardDescriptorPoint.unit)
  let original ← withWitnesses 3 original fun witnesses predicate => do
    let base ← mkAppM ``BaseContext.Context.partialRead
      #[mkConst ``FiniteBaseProbe.base, witnesses[0]!]
    let firstRead ← evaluation setup.first.context base witnesses[1]!
    let secondRead ← evaluation second.context firstRead witnesses[2]!
    let firstNamed ← mkAppM ``FramePublic.firstReader #[witnesses[0]!, witnesses[1]!]
    let secondNamed ← mkAppM ``FramePublic.secondReader witnesses
    unless predicate.find? (· == firstRead) |>.isSome do
      throwError "public joint first reader was not found"
    unless predicate.find? (· == secondRead) |>.isSome do
      throwError "public joint second reader was not found"
    return predicate.replace fun term =>
      if term == secondRead then some secondNamed
      else if term == firstRead then some firstNamed
      else none
  for (context, name) in #[(setup.first.context, ``FrameOwners.first),
      (second.context, ``FrameOwners.second)] do
    unless ← withTransparency .all (isDefEq context (mkConst name)) do
      throwError "public joint owner differs from the original native context"
  let original := original.replace fun term =>
    if term == second.context then some (mkConst ``FrameOwners.second)
    else if term == setup.first.context then some (mkConst ``FrameOwners.first)
    else none
  let type ← withDeclNameForAuxNaming
      `Hex.RealClosure.Algebraic.KernelReplay.GuardJointExport.Statement do
    (shareProofs original).run
  let declaration := Declaration.defnDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.GuardJointExport.Statement,
    levelParams := [], type := mkSort 0, value := type, hints := .abbrev, safety := .safe }
  addDecl declaration (forceExpose := true)
  addDecl <| .thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.GuardJointExport.exists_points,
    levelParams := [], type, value := mkConst ``GuardJoint.exists_points }
  logInfo m!"joint export checked: aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardJointExport
