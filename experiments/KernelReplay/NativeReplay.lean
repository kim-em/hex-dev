/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.NativeReplay
import all HexRealClosure.TowerContext
import all HexRealClosure.Algebraic
import all HexRealClosure.InverseReplay

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeReplayProbe
open Lean Meta Elab Command Hex.SignDet FiniteData

private def withRoot (parent : Expr) (action : Expr → MetaM Unit) : MetaM Unit := do
  let args := (← inferType parent).getAppArgs
  let type ← mkAppM ``Descriptor #[args[1]!, mkConst ``Tower.Signature,
    args[args.size - 4]!, args.back!]
  withLocalDeclD `descriptor type fun descriptor => do
    withLocalDeclD `frame (mkConst ``Tower.Literal) fun frame => do
      let encoded ← mkEq (← mkAppM ``Tower.Literal.ofJson
        #[← mkAppM ``Tower.rootData #[args[args.size - 2]!, descriptor]])
        (← mkAppM ``Option.some #[frame])
      withLocalDeclD `encoded encoded fun encoded => do
        action (← mkAppM ``Tower.Chain.root #[parent, descriptor, frame, encoded])

private def withInventories (owner : Expr) (action : Expr → Expr → Expr → MetaM Unit) :
    MetaM Unit := do
  let types ← #[``Packing, ``ValueSign, ``InverseFact].mapM fun name => do
    mkAppM ``List #[← mkAppM name #[owner]]
  withLocalDeclD `entries types[0]! fun entries =>
    withLocalDeclD `signs types[1]! fun signs =>
      withLocalDeclD `inverses types[2]! fun inverses => action entries signs inverses

private def verify (term : Expr) : MetaM Unit := do
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let proof ← mkLambdaFVars locals (← mkEqRefl term) (usedOnly := true)
  let type ← inferType proof
  let _ ← auditProof proof type
  kernelCheck `__nativeReplayFixture type proof

syntax (name := nativeReplayProbe) "#native_replay_probe" : command
@[command_elab nativeReplayProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let base := mkConst ``FiniteBaseProbe.base
  let parent ← mkAppM ``Tower.Chain.base #[base]
  let baseArgs := (← inferType parent).getAppArgs
  let nativeBase ← NativeOperations.native baseArgs[1]! baseArgs[baseArgs.size - 4]!
  let historyType ← mkAppM ``BaseContext.PackedContext.Realization
    #[← mkAppM ``BaseContext.PackedContext.pack #[base]]
  withLocalDeclD `following historyType fun following => do
    withRoot parent fun first => withRoot first fun second => do
      let native ← NativeChain.ofContext (← mkAppM ``Tower.Context.pack #[second])
      let models ← native.models following
      withInventories native.owners[0]! fun entries signs inverses => do
        let firstOperations ← nativeBase.extend native.owners[0]! entries signs inverses
        for equation in firstOperations.equations do verify equation
        verify firstOperations.signEquation
        let unit ← mkAppOptM ``One.one #[some firstOperations.carrier, none]
        let polynomial ← mkAppM ``DensePoly.C #[unit]
        withLocalDeclD `packet (mkConst ``Codec.Json) fun packet => do
          let firstArgs := (← inferType first).getAppArgs
          let reader ← models.replaySignReader 1 firstOperations native.owners[1]!
            firstArgs[firstArgs.size - 2]! (mkConst ``Tower.Signature.codec)
            polynomial (toExpr (1 : Int)) packet
          verify reader
          let forged := { firstOperations with equations := firstOperations.equations.reverse }
          let rejected ← try
            let _ ← models.replaySignReader 1 forged native.owners[1]!
              firstArgs[firstArgs.size - 2]! (mkConst ``Tower.Signature.codec)
              polynomial (toExpr (1 : Int)) packet
            pure false
          catch error =>
            unless (← error.toMessageData.toString) ==
                "native replay dictionary equation does not match its operation" do throw error
            pure true
          unless rejected do throwError "native replay reader accepted permuted dictionary equations"
        withInventories native.owners[1]! fun entries signs inverses => do
          let secondOperations ← firstOperations.extend native.owners[1]! entries signs inverses
          for equation in secondOperations.equations do verify equation
          verify secondOperations.signEquation
          let zero ← mkAppOptM ``Zero.zero #[some secondOperations.carrier, none]
          let inverted ← mkAppOptM ``Inv.inv
            #[some secondOperations.carrier, some secondOperations.operations[5]!, some zero]
          let proof ← mkEqRefl inverted
          let statement ← mkEq inverted zero
          let locals := (← getLCtx).getFVarIds.map mkFVar
          let statement ← mkForallFVars locals statement (usedOnly := true)
          let proof ← mkLambdaFVars locals proof (usedOnly := true)
          let _ ← auditProof proof statement
          kernelCheck `__nativeReplayZeroInverse statement proof
          let rejected ← try
            let _ ← nativeBase.extend native.owners[1]! entries signs inverses
            pure false
          catch error =>
            unless (← error.toMessageData.toString) ==
                "native replay extension has a different predecessor carrier" do throw error
            pure true
          unless rejected do throwError "native replay extension accepted a different predecessor"
  logInfo "native replay retained recursive dictionaries over two infinitesimals and two arbitrary root levels; wrong predecessor and permuted equations rejected"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#native_replay_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeReplayProbe
