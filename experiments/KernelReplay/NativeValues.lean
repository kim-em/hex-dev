/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTower
public meta import KernelReplay.FiniteTower
public meta import HexRealClosureTheory.NativePackets
public meta import HexRealClosureTheory.NativeValues
import all HexRealClosure.Algebraic

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeValuesProbe
open Lean Meta Elab Command Hex.SignDet FiniteTower

syntax (name := nativeValuesProbe) "#native_values_probe" : command
@[command_elab nativeValuesProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let owner := mkConst ``first
  let literal ← mkAppM ``HAdd.hAdd #[mkConst ``variablePoly,
    ← mkAppM ``RawDescriptor.head #[mkConst ``firstRaw]]
  let one := toExpr (1 : Int)
  let equation ← mkEq (← mkAppM ``Context.signPoly #[owner, literal]) one
  let nonzero ← mkAppM ``Ne #[one, toExpr (0 : Int)]
  withLocalDeclD `checked equation fun checked => do
    withLocalDeclD `nonzero nonzero fun nonzero => do
      let value ← mkAppM ``Element.restore #[literal, one, checked, nonzero]
      let type ← inferType value
      let prepared ← NativeValues.prepare #[owner] value
      if prepared.hasFVar then throwError "native value retained a local correctness proof"
      unless ← withTransparency .all (isDefEq (← inferType prepared) type) do
        throwError "native value preparation changed its original carrier"
      let preservation ← mkAppM ``NativeValues.restoreValue_eq #[owner, value]
      let locals := (← getLCtx).getFVarIds.map mkFVar
      let proof ← mkLambdaFVars locals preservation (usedOnly := true)
      let statement ← inferType proof
      let _ ← auditProof proof statement
      kernelCheck `__nativeValuePreservation statement proof
      let codec ← mkAppOptM ``Element.codec (type.getAppArgs.map some ++
        #[some (mkConst ``ValueCodec.rat)])
      let polynomial ← mkAppM ``DensePoly.C #[value]
      let packet ← NativePackets.polynomial codec polynomial #[owner]
      let rational ← NativePackets.polynomial (mkConst ``ValueCodec.rat) literal
      let expected : Codec.Json := .arr #[.arr #[rational, Codec.Json.of (1 : Int)]]
      unless packet == expected do
        throwError "native polynomial export changed the noncanonical literal or cached tag"
  let element ← mkAppM ``Element #[owner]
  let zero ← mkAppOptM ``Zero.zero #[some element, none]
  let prepared ← NativeValues.prepare #[owner] zero
  unless prepared == zero do throwError "native preparation changed a closed canonical zero"
  withLocalDeclD `runtime element fun runtime => do
    let rejected ← try
      let _ ← NativePackets.storedSign (mkConst ``ValueCodec.rat) (mkConst ``ValueCodec.nat) runtime
      pure false
    catch error =>
      unless (← error.toMessageData.toString) ==
          "native packet production requires complete closed input" do throw error
      pure true
    unless rejected do throwError "native producer accepted an opaque runtime value"
  logInfo "native packet export removed local correctness proofs and retained the original noncanonical stored literal; opaque runtime values rejected"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
#native_values_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeValuesProbe
