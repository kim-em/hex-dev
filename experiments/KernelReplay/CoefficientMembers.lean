/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.FiniteBase

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.CoefficientMembers
open Lean Meta Elab Command FiniteData

private def statement (domain coefficient polynomial : Expr) (bound? : Option Expr := none) :
    MetaM Expr := do
  let size ← match bound? with
    | some bound => pure bound
    | none => mkAppM ``DensePoly.size #[polynomial]
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    withLocalDeclD `bound (← mkAppM ``Nat.lt #[i, size]) fun bound => do
      mkForallFVars #[i, bound] (mkApp domain (mkApp coefficient i))

private def check (agreement type : Expr) : MetaM Unit := do
  let some proof ← agreementSupplier agreement none type |
    throwError "whole retained coefficient list was not supplied"
  unless proof.getAppFn.isConstOf ``Transport.Inventory.Agreement.members do
    throwError "test did not exercise the whole-list theorem"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let type ← mkForallFVars locals type
  let proof ← mkLambdaFVars locals proof
  let _ ← auditProof proof type
  let levels := collectLevelParams (collectLevelParams {} type) proof |>.params.toList
  let options := (← getOptions).setBool `debug.skipKernelTC false
  ofExceptKernelException <| ((← getEnv).toKernelEnv.addDecl options
    (.thmDecl {
      name := `__wholeCoefficientMembers, levelParams := levels,
      type, value := proof })).map (fun _ => ())

private def refused (label : String) (agreement type : Expr) : MetaM Unit := do
  if (← agreementSupplier agreement none type).isSome then
    throwError "whole-list supplier accepted {label}"

syntax (name := coefficientMembers) "#coefficient_members" : command
@[command_elab coefficientMembers]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let base ← Base.ofClosed (mkConst ``FiniteBaseProbe.closed)
  let left := mkConst ``FiniteBaseProbe.left
  let right := mkConst ``FiniteBaseProbe.right
  let coefficient := (← mkAppM ``DensePoly.coeff #[left, toExpr (0 : Nat)]).appFn!
  let other := (← mkAppM ``DensePoly.coeff #[right, toExpr (0 : Nat)]).appFn!
  let lefts ← mkAppM ``Transport.Inventory.coefficients #[left]
  let rights ← mkAppM ``Transport.Inventory.coefficients #[right]
  let empty ← mkListLit (← inferType (mkApp coefficient (toExpr (0 : Nat)))) []
  let appended ← mkAppM ``List.append #[rights, lefts]
  let nested ← mkAppM ``List.append #[appended, empty]
  let consed ← mkAppM ``List.cons #[mkConst ``FiniteBaseProbe.epsilon, lefts]
  let supportName := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientSupport)
  let supportType ← inferType nested
  addDecl (.defnDecl {
    name := supportName, levelParams := [], type := supportType,
    value := nested, hints := .regular 0, safety := .safe })
  let chainName := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientAlias)
  addDecl (.defnDecl {
    name := chainName, levelParams := [], type := supportType,
    value := mkConst supportName, hints := .regular 0, safety := .safe })
  setReducibilityStatus chainName .irreducible
  let underAppend ← mkAppM ``List.append #[empty, mkConst chainName]
  let underCons ← mkAppM ``List.cons #[mkConst ``FiniteBaseProbe.epsilon, mkConst chainName]
  let duplicate ← mkAppM ``List.append #[lefts, lefts]
  let originalType ← inferType (mkConst ``FiniteBaseProbe.agreement)
  let parameters := originalType.getAppArgs
  let target ← statement base.domain coefficient left
  for inventory in #[lefts, appended, nested, consed, mkConst supportName,
      mkConst chainName, underAppend, underCons, duplicate] do
    let agreementType := mkAppN originalType.getAppFn
      (parameters.set! (parameters.size - 1) inventory)
    withLocalDeclD `agreement agreementType fun agreement => do
      check agreement target
      let assigned ← mkFreshExprMVar (some (← inferType left))
      assigned.mvarId!.assign left
      let args := coefficient.getAppArgs
      let aliased := mkAppN coefficient.getAppFn (args.set! (args.size - 1) assigned)
      check agreement (← statement base.domain aliased assigned)
      refused "different bound" agreement (← statement base.domain coefficient left (some (toExpr (1 : Nat))))
      let wrappedSize ← mkAppM ``Nat.add #[← mkAppM ``DensePoly.size #[left], toExpr (0 : Nat)]
      refused "nonstructural size bound" agreement
        (← statement base.domain coefficient left (some wrappedSize))
      let unknownBound ← mkFreshExprMVar (some (mkConst ``Nat))
      refused "bound metavariable" agreement (← statement base.domain coefficient left (some unknownBound))
      if ← unknownBound.mvarId!.isAssigned then throwError "supplier assigned caller bound"
      withLocalDeclD `foreign (← inferType base.domain) fun foreign => do
        refused "foreign domain" agreement (← statement foreign coefficient left)
      let unknown ← mkFreshExprMVar (some (← inferType base.domain))
      refused "domain metavariable" agreement (← statement unknown coefficient left)
      if ← unknown.mvarId!.isAssigned then throwError "supplier assigned caller domain"
      let unknown ← mkFreshExprMVar (some (← inferType left))
      let args := coefficient.getAppArgs
      let incomplete := mkAppN coefficient.getAppFn (args.set! (args.size - 1) unknown)
      refused "polynomial metavariable" agreement (← statement base.domain incomplete unknown)
      if ← unknown.mvarId!.isAssigned then throwError "supplier assigned caller polynomial"
      let args := coefficient.getAppArgs
      withLocalDeclD `zero (← inferType args[1]!) fun zero => do
        let changed := mkAppN coefficient.getAppFn (args.set! 1 zero)
        refused "coefficient dictionary" agreement (← statement base.domain changed left)
  let original := mkConst ``FiniteBaseProbe.agreement
  refused "notation inventory shape" original target
  let fallback ← build target (agreementSupplier original none)
  let _ ← auditProof fallback target
  kernelCheck `__coefficientMemberFallback target fallback
  let element ← inferType (mkApp coefficient (toExpr (0 : Nat)))
  let zeroPoly ← mkAppM ``DensePoly.ofCoeffs #[← mkArrayLit element []]
  let zeroFunction := (← mkAppM ``DensePoly.coeff #[zeroPoly, toExpr (0 : Nat)]).appFn!
  let noCoefficients ← mkAppM ``Transport.Inventory.coefficients #[zeroPoly]
  let agreementType := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) noCoefficients)
  withLocalDeclD `agreement agreementType fun agreement => do
    check agreement (← statement base.domain zeroFunction zeroPoly)
  let agreementType := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) lefts)
  withLocalDeclD `agreement agreementType fun agreement => do
    refused "absent polynomial" agreement (← statement base.domain other right)
  withLocalDeclD `inventory (← inferType lefts) fun inventory => do
    let agreementType := mkAppN originalType.getAppFn
      (parameters.set! (parameters.size - 1) inventory)
    withLocalDeclD `agreement agreementType fun agreement => refused "open inventory" agreement target
  -- A closed support alias must preserve its named universe when unfolded.
  let lifted := mkAppN (mkConst ``ULift.up [Level.param `u, Level.zero])
    #[mkConst ``Nat, toExpr (1 : Nat)]
  let liftedType ← inferType lifted
  let polynomial ← mkAppM ``DensePoly.C #[lifted]
  let function := (← mkAppM ``DensePoly.coeff #[polynomial, toExpr (0 : Nat)]).appFn!
  let inventory ← mkAppM ``Transport.Inventory.coefficients #[polynomial]
  let aliasName := mkPrivateName (← getEnv) (← mkFreshUserName `__polymorphicSupport)
  let aliasType ← inferType inventory
  addDecl (.defnDecl {
    name := aliasName, levelParams := [`u], type := aliasType, value := inventory,
    hints := .regular 0, safety := .safe })
  setReducibilityStatus aliasName .irreducible
  let inventory := mkConst aliasName [Level.param `u]
  let sign ← withLocalDeclD `value liftedType fun value =>
    mkLambdaFVars #[value] (toExpr (0 : Int))
  let targetSign ← withLocalDeclD `value (mkConst ``Real) fun value =>
    mkLambdaFVars #[value] (toExpr (0 : Int))
  withLocalDeclD `read (← mkArrow liftedType (mkConst ``Real)) fun read => do
    withLocalDeclD `domain (← mkArrow liftedType (mkSort .zero)) fun domain => do
      let agreementType ← mkAppM ``Transport.Inventory.Agreement
        #[read, domain, sign, targetSign, inventory]
      withLocalDeclD `agreement agreementType fun agreement => do
        check agreement (← statement domain function polynomial)
  logInfo "whole coefficient agreements preserve guarded bounds and dictionaries; foreign and incomplete requests refused"

end Hex.RealClosure.Algebraic.KernelReplay.CoefficientMembers

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: whole coefficient agreements preserve guarded bounds and dictionaries; foreign and incomplete requests refused -/
#guard_msgs in
#coefficient_members
