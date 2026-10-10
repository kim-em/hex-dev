/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureMathlib.NativeModels
import all HexRealClosure.TowerContext

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeModelsProbe
open Lean Meta Elab Command Hex.SignDet FiniteData

private def withRoot (parent : Expr) (action : Expr → MetaM Unit) : MetaM Unit := do
  let args := (← inferType parent).getAppArgs
  let carrier := args[1]!
  let sign := args[args.size - 4]!
  let codec := args[args.size - 2]!
  let binding := args.back!
  let type ← mkAppM ``Descriptor #[carrier, mkConst ``Tower.Signature, sign, binding]
  withLocalDeclD `descriptor type fun descriptor => do
    withLocalDeclD `frame (mkConst ``Tower.Literal) fun frame => do
      let encoded ← mkEq (← mkAppM ``Tower.Literal.ofJson
        #[← mkAppM ``Tower.rootData #[codec, descriptor]]) (← mkAppM ``Option.some #[frame])
      withLocalDeclD `encoded encoded fun encoded => do
        action (← mkAppM ``Tower.Chain.root #[parent, descriptor, frame, encoded])

syntax (name := nativeModelsProbe) "#native_models_probe" : command
@[command_elab nativeModelsProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let base := mkConst ``FiniteBaseProbe.base
  let parent ← mkAppM ``Tower.Chain.base #[base]
  let original ← mkAppM ``Tower.Context.pack #[parent]
  let historyType ← mkAppM ``BaseContext.PackedContext.Realization
    #[← mkAppM ``BaseContext.PackedContext.pack #[base]]
  withLocalDeclD `following historyType fun following => do
    let empty ← NativeChain.ofContext original
    let models ← empty.models following
    unless models.models.size == 1 && models.prefixes == #[original] do
      throwError "native base model lost its actual prefix"
    withRoot parent fun first => withRoot first fun second => do
      let context ← mkAppM ``Tower.Context.pack #[second]
      let native ← NativeChain.ofContext context
      let models ← native.models following
      unless models.models.size == 3 && models.prefixes ==
          #[original, ← mkAppM ``Tower.Context.pack #[first], context] do
        throwError "native models lost their original prefix order"
      for model in models.models do
        let locals := (← getLCtx).getFVarIds.map mkFVar
        let type ← mkForallFVars locals (← mkEq model model) (usedOnly := true)
        let proof ← mkLambdaFVars locals (← mkEqRefl model) (usedOnly := true)
        let _ ← auditProof proof type
        kernelCheck `__closedNativePrefixModel type proof
      for i in [:2] do
        let predecessor := if i == 0 then parent else first
        let args := (← inferType predecessor).getAppArgs
        let unit ← mkAppOptM ``One.one #[some args[1]!, none]
        let polynomial ← mkAppM ``DensePoly.C #[unit]
        withLocalDeclD `packet (mkConst ``Codec.Json) fun packet => do
          let reader ← models.signReader i native.owners[i]! args[args.size - 2]!
            (mkConst ``Tower.Signature.codec) polynomial (toExpr (1 : Int)) packet
          let expected ← mkAppM ``Option #[← mkAppM ``SignFact #[native.owners[i]!]]
          unless ← withTransparency .all (isDefEq (← inferType reader) expected) do
            throwError "native scalar packet reader has a different owner"
          let locals := (← getLCtx).getFVarIds.map mkFVar
          let type ← mkForallFVars locals (← mkEq reader reader) (usedOnly := true)
          let proof ← mkLambdaFVars locals (← mkEqRefl reader) (usedOnly := true)
          let _ ← auditProof proof type
          kernelCheck `__nativeScalarPacketReader type proof
      let rejected ← try
        let _ ← native.models following 2
        pure false
      catch _ => pure true
      unless rejected do throwError "native models accepted insufficient depth"
      let forged := { native with owners := native.owners.reverse }
      let rejected ← try
        let _ ← forged.models following
        pure false
      catch _ => pure true
      unless rejected do throwError "native models accepted reordered owners"
  logInfo "native prefix models retained the two-infinitesimal base and two arbitrary validated root levels"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#native_models_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeModelsProbe
