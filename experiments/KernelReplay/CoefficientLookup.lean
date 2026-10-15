/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.FiniteBase

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.CoefficientLookup
open Lean Meta Elab Command FiniteData

syntax (name := coefficientLookup) "#coefficient_lookup" : command
@[command_elab coefficientLookup]
def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let base ← Base.ofClosed (mkConst ``FiniteBaseProbe.closed)
    let wanted ← mkAppM ``DensePoly.coeff #[mkConst ``FiniteBaseProbe.left, toExpr (0 : Nat)]
    let other ← mkAppM ``DensePoly.coeff #[mkConst ``FiniteBaseProbe.right, toExpr (0 : Nat)]
    let inventory ← mkListLit (← inferType wanted) (List.replicate 256 other ++ [wanted])
    let repeated ← mkAppM ``List.replicate #[toExpr (256 : Nat), other]
    let coefficients ← mkAppM ``Transport.Inventory.coefficients #[mkConst ``FiniteBaseProbe.left]
    let appended ← mkAppM ``List.append #[repeated, coefficients]
    let cases : Array (Expr × Nat) := #[(inventory, 1), (appended, 2)]
    let cache ← IO.mkRef (none : Option CoefficientWalk)
    for (inventory, missingIndex) in cases do
      let agreementType ← inferType (mkConst ``FiniteBaseProbe.agreement)
      let parameters := agreementType.getAppArgs
      let agreementType := mkAppN agreementType.getAppFn
        (parameters.set! (parameters.size - 1) inventory)
      -- The requested index has a different expression but the same natural value.
      let index ← mkAppM ``Nat.add #[toExpr (0 : Nat), toExpr (0 : Nat)]
      let requestedValue := mkApp wanted.appFn! index
      let requested := mkApp base.domain requestedValue
      withLocalDeclD `agreement agreementType fun agreement => do
        for supply in #[lookupCoefficientCached agreement cache, agreementSupplier agreement (some cache),
            lookupCoefficient agreement, agreementSupplier agreement] do
          let some proof ← supply requested
            | throwError "retained coefficient was not found through the original function and index"
          unless proof.hasFVar do throwError "coefficient lookup discarded its agreement hypothesis"
          let statement ← mkForallFVars #[agreement] requested
          let proof ← mkLambdaFVars #[agreement] proof
          let _ ← auditProof proof statement
          kernelCheck `__coefficientMembership statement proof
        let supply := lookupCoefficientCached agreement cache
        withLocalDeclD `foreignDomain (← inferType base.domain) fun other => do
          if (← supply (mkApp other requestedValue)).isSome then
            throwError "coefficient lookup supplied a foreign guarded domain"
        for (target, label) in #[(base.domain, "domain"), (requestedValue, "coefficient"),
            (index, "index")] do
          let unknown ← mkFreshExprMVar (some (← inferType target))
          let request := requested.replace fun value =>
            if value == target then some unknown else none
          if (← supply request).isSome then
            throwError "coefficient lookup chose the caller's {label}"
          if ← unknown.mvarId!.isAssigned then
            throwError "coefficient lookup assigned the caller's {label} metavariable"
        let missing := mkApp wanted.appFn! (toExpr missingIndex)
        if (← supply (mkApp base.domain missing)).isSome then
          throwError "coefficient lookup supplied an unretained index"
        let function := wanted.appFn!
        let arguments := function.getAppArgs
        withLocalDeclD `zero (← inferType arguments[1]!) fun zero => do
          let changed := mkApp (mkAppN function.getAppFn (arguments.set! 1 zero)) wanted.appArg!
          if (← supply (mkApp base.domain changed)).isSome then
            throwError "coefficient lookup replaced a coefficient dictionary"
      -- An open inventory is outside the literal-list lookup contract.
      withLocalDeclD `inventory (← inferType inventory) fun inventory => do
        let parameters := agreementType.getAppArgs
        let type := mkAppN agreementType.getAppFn
          (parameters.set! (parameters.size - 1) inventory)
        withLocalDeclD `agreement type fun agreement => do
          if (← lookupCoefficientCached agreement cache requested).isSome then
            throwError "coefficient lookup supplied an open inventory"
    logInfo "coefficient lookup retains the full guard and hypothesis; foreign, incomplete and missing keys refused"

end Hex.RealClosure.Algebraic.KernelReplay.CoefficientLookup

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: coefficient lookup retains the full guard and hypothesis; foreign, incomplete and missing keys refused -/
#guard_msgs in
#coefficient_lookup
