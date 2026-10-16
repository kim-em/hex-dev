/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.FiniteBase
import all HexRealClosureTheory.FiniteBase

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.CoefficientEntry
open Lean Meta Elab Command FiniteData

private def check (agreement target : Expr) : MetaM Unit := do
  let some proof ← agreementSupplier agreement target |
    throwError "retained coefficient index was not supplied"
  unless (proof.find? (·.isConstOf ``Transport.Inventory.Agreement.members)).isSome do
    throwError "indexed request did not use its retained coefficient block"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let target ← mkForallFVars locals (← instantiateMVars target)
  let proof ← mkLambdaFVars locals proof
  let _ ← auditProof proof target
  let levels := collectLevelParams (collectLevelParams {} target) proof |>.params.toList
  let options := (← getOptions).setBool `debug.skipKernelTC false
  ofExceptKernelException <| ((← getEnv).toKernelEnv.addDecl options
    (.thmDecl {
      name := `__coefficientEntry, levelParams := levels, type := target, value := proof })).map (fun _ => ())

private def refused (agreement target : Expr) : MetaM Unit := do
  if (← agreementCoefficient agreement target).isSome then
    throwError "indexed block projection accepted an unsupported request"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let base ← Base.ofClosed (mkConst ``FiniteBaseProbe.closed)
  let left := mkConst ``FiniteBaseProbe.left
  let right := mkConst ``FiniteBaseProbe.right
  let function := (← mkAppM ``DensePoly.coeff #[left, toExpr (0 : Nat)]).appFn!
  let other := (← mkAppM ``DensePoly.coeff #[right, toExpr (0 : Nat)]).appFn!
  let lefts ← mkAppM ``Transport.Inventory.coefficients #[left]
  let rights ← mkAppM ``Transport.Inventory.coefficients #[right]
  let empty ← mkListLit (← inferType (mkApp function (toExpr (0 : Nat)))) []
  let appended ← mkAppM ``List.append #[rights, lefts]
  let nested ← mkAppM ``List.append #[appended, empty]
  let consed ← mkAppM ``List.cons #[mkConst ``FiniteBaseProbe.epsilon, lefts]
  let duplicate ← mkAppM ``List.append #[lefts, lefts]
  let supportName ← mkFreshUserName `coefficientBlock
  addDecl (.defnDecl {
    name := supportName, levelParams := [], type := ← inferType nested,
    value := nested, hints := .regular 0, safety := .safe })
  setReducibilityStatus supportName .irreducible
  let originalType ← inferType (mkConst ``FiniteBaseProbe.agreement)
  let parameters := originalType.getAppArgs
  for inventory in #[lefts, appended, nested, consed, duplicate, mkConst supportName] do
    let agreementType := mkAppN originalType.getAppFn
      (parameters.set! (parameters.size - 1) inventory)
    withLocalDeclD `agreement agreementType fun agreement => do
      for index in #[toExpr (0 : Nat), toExpr (1 : Nat),
          ← mkAppM ``Nat.add #[toExpr (0 : Nat), toExpr (1 : Nat)]] do
        check agreement (mkApp base.domain (mkApp function index))
      let assigned ← mkFreshExprMVar (some (mkConst ``Nat))
      assigned.mvarId!.assign (toExpr (1 : Nat))
      check agreement (mkApp base.domain (mkApp function assigned))
      for index in #[toExpr (2 : Nat), toExpr (1000 : Nat)] do
        refused agreement (mkApp base.domain (mkApp function index))
      let unknown ← mkFreshExprMVar (some (mkConst ``Nat))
      refused agreement (mkApp base.domain (mkApp function unknown))
      if ← unknown.mvarId!.isAssigned then throwError "supplier assigned caller index"
      withLocalDeclD `index (mkConst ``Nat) fun index => do
        refused agreement (mkApp base.domain (mkApp function index))
      withLocalDeclD `foreign (← inferType base.domain) fun foreign => do
        refused agreement (mkApp foreign (mkApp function (toExpr (0 : Nat))))
      let unknownDomain ← mkFreshExprMVar (some (← inferType base.domain))
      refused agreement (mkApp unknownDomain (mkApp function (toExpr (0 : Nat))))
      if ← unknownDomain.mvarId!.isAssigned then throwError "supplier assigned caller domain"
      let unknown ← mkFreshExprMVar (some (← inferType left))
      let args := function.getAppArgs
      let incomplete := mkAppN function.getAppFn (args.set! (args.size - 1) unknown)
      refused agreement (mkApp base.domain (mkApp incomplete (toExpr (0 : Nat))))
      if ← unknown.mvarId!.isAssigned then throwError "supplier assigned caller polynomial"
      for index in #[1, 2] do
        withLocalDeclD `dictionary (← inferType args[index]!) fun dictionary => do
          let changed := mkAppN function.getAppFn (args.set! index dictionary)
          refused agreement (mkApp base.domain (mkApp changed (toExpr (0 : Nat))))
  -- The requested block follows 8192 unrelated coefficients. Its proof must
  -- use the outer append projection instead of a global list position.
  let mut earlierSupport := rights
  for _ in [:12] do earlierSupport ← mkAppM ``List.append #[earlierSupport, earlierSupport]
  let late ← mkAppM ``List.append #[earlierSupport, lefts]
  let lateAgreement := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) late)
  withLocalDeclD `agreement lateAgreement fun agreement => do
    check agreement (mkApp base.domain (mkApp function (toExpr (1 : Nat))))
  let onlyLeft := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) lefts)
  withLocalDeclD `agreement onlyLeft fun agreement => do
    refused agreement (mkApp base.domain (mkApp other (toExpr (0 : Nat))))
  withLocalDeclD `inventory (← inferType lefts) fun inventory => do
    let agreementType := mkAppN originalType.getAppFn
      (parameters.set! (parameters.size - 1) inventory)
    withLocalDeclD `agreement agreementType fun agreement => do
      refused agreement (mkApp base.domain (mkApp function (toExpr (0 : Nat))))
  let element ← inferType (mkApp function (toExpr (0 : Nat)))
  let zero ← mkAppM ``DensePoly.ofCoeffs #[← mkArrayLit element []]
  let zeroFunction := (← mkAppM ``DensePoly.coeff #[zero, toExpr (0 : Nat)]).appFn!
  let zeroInventory ← mkAppM ``Transport.Inventory.coefficients #[zero]
  let zeroAgreement := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) zeroInventory)
  withLocalDeclD `agreement zeroAgreement fun agreement => do
    refused agreement (mkApp base.domain (mkApp zeroFunction (toExpr (0 : Nat))))
  -- A literal list deliberately lacks the polynomial-block structure. Its
  -- individual coefficient remains available through the original fallback.
  let literal ← mkListLit element [mkApp function (toExpr (0 : Nat))]
  let literalAgreement := mkAppN originalType.getAppFn
    (parameters.set! (parameters.size - 1) literal)
  withLocalDeclD `agreement literalAgreement fun agreement => do
    let target := mkApp base.domain (mkApp function (toExpr (0 : Nat)))
    refused agreement target
    let some fallback ← agreementSupplier agreement target |
      throwError "existing individual coefficient fallback was lost"
    let locals := (← getLCtx).getFVarIds.map mkFVar
    kernelCheck `__coefficientEntryFallback (← mkForallFVars locals target)
      (← mkLambdaFVars locals fallback)
  -- These dictionaries are ordinary parameters, unavailable to instance
  -- search. An unsupported inventory must refuse the well-typed request.
  withLocalDeclD `E (mkSort (.succ .zero)) fun carrier => do
    withLocalDeclD `zero (← mkAppM ``Zero #[carrier]) fun zero => do
      withLocalDeclD `decidable (← mkAppM ``DecidableEq #[carrier]) fun decidable => do
        let polynomialType := mkAppN (mkConst ``DensePoly [.zero]) #[carrier, zero, decidable]
        withLocalDeclD `polynomial polynomialType fun polynomial => do
          let realZero ← mkAppOptM ``OfNat.ofNat
            #[some (mkConst ``Real), some (toExpr (0 : Nat)), none]
          let read ← withLocalDeclD `x carrier fun x => mkLambdaFVars #[x] realZero
          let domain ← withLocalDeclD `x carrier fun x =>
            mkLambdaFVars #[x] (mkConst ``True)
          let source ← withLocalDeclD `x carrier fun x =>
            mkLambdaFVars #[x] (toExpr (0 : Int))
          let mut args := parameters
          for i in [:parameters.size - 5] do
            if args[i]! == element then args := args.set! i carrier
            else if (← inferType args[i]!) == (← mkAppM ``Zero #[element]) then
              args := args.set! i zero
            else if (← inferType args[i]!) == (← mkAppM ``DecidableEq #[element]) then
              args := args.set! i decidable
          args := args.set! (args.size - 5) read |>.set! (args.size - 4) domain
            |>.set! (args.size - 3) source |>.set! (args.size - 1) (← mkListLit carrier [])
          let agreementType := mkAppN originalType.getAppFn args
          withLocalDeclD `agreement agreementType fun agreement => do
            withLCtx (← getLCtx) #[] do
              let coefficient := mkAppN (mkConst ``DensePoly.coeff [.zero])
                #[carrier, zero, decidable, polynomial, toExpr (0 : Nat)]
              let target := mkApp domain coefficient
              let locals := (← getLCtx).getFVarIds.map mkFVar
              let proof ← mkEqRefl target
              kernelCheck `__coefficientRequestType (← mkForallFVars locals (← inferType proof))
                (← mkLambdaFVars locals proof)
              if (← agreementSupplier agreement target).isSome then
                throwError "empty inventory supplied a coefficient with unavailable instances"
  let lifted := mkAppN (mkConst ``ULift.up [Level.param `u, Level.zero])
    #[mkConst ``Nat, toExpr (1 : Nat)]
  let liftedType ← inferType lifted
  let polynomial ← mkAppM ``DensePoly.C #[lifted]
  let function := (← mkAppM ``DensePoly.coeff #[polynomial, toExpr (0 : Nat)]).appFn!
  let inventory ← mkAppM ``Transport.Inventory.coefficients #[polynomial]
  let supportName ← mkFreshUserName `polymorphicCoefficientBlock
  let aliasType ← inferType inventory
  addDecl (.defnDecl {
    name := supportName, levelParams := [`v],
    type := aliasType.instantiateLevelParams [`u] [Level.param `v],
    value := inventory.instantiateLevelParams [`u] [Level.param `v],
    hints := .regular 0, safety := .safe })
  setReducibilityStatus supportName .irreducible
  let sourceSign ← withLocalDeclD `value liftedType fun value =>
    mkLambdaFVars #[value] (toExpr (0 : Int))
  let targetSign ← withLocalDeclD `value (mkConst ``Real) fun value =>
    mkLambdaFVars #[value] (toExpr (0 : Int))
  withLocalDeclD `read (← mkArrow liftedType (mkConst ``Real)) fun read => do
    withLocalDeclD `domain (← mkArrow liftedType (mkSort .zero)) fun domain => do
      let agreementType ← mkAppM ``Transport.Inventory.Agreement
        #[read, domain, sourceSign, targetSign, mkConst supportName [Level.param `u]]
      withLocalDeclD `agreement agreementType fun agreement => do
        check agreement (mkApp domain (mkApp function (toExpr (0 : Nat))))
        refused agreement (mkApp domain (mkApp function (toExpr (1 : Nat))))

end Hex.RealClosure.Algebraic.KernelReplay.CoefficientEntry
