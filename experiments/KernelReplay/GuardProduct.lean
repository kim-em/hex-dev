/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardOperand
public meta import KernelReplay.GuardOperand
import all KernelReplay.GuardOperand
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardSecondData
import all KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardProduct
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

/-- Expand only finite checked operand data aliases before native evaluation.
The original requested guarded-domain proposition remains the kernel target. -/
private def expandValue (began : Nat) (value : Expr) : MetaM Expr := do
  let environment := (← getEnv).checked.get
  let mut names := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless names.size == 17 do throwError "missing finite scalar data aliases"
  names := names ++ #[``GuardOperand.polynomial, ``GuardOperand.beta]
  let mut bodies : NameMap Expr := {}
  for name in names do
    let .defnInfo info ← getConstInfo name | throwError "operand alias is not checked data"
    bodies := bodies.insert name info.value
  let mut value := value
  for _ in [:32] do
    let _ ← bounded began
    let next := value.replace fun expression => do
      let some name := expression.constName? | none
      bodies.find? name
    if next == value then return value
    value := next
  throwError "finite operand alias expansion bound exhausted"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let first := setup.first
  let second ← Prefix.ofData (mkConst ``GuardSecondData.data)
    (mkConst ``GuardDescriptorPoint.zero) (mkConst ``GuardDescriptorPoint.unit)
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let domains ← GuardCoefficientFence.prepare began origin (mkConst ``GuardInventoryReplay.agreement)
    (compileValue := expandValue began)
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let base := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let supplier := second.supplyFrom #[origin.read, first.reader]
    (first.supplyFrom #[origin.read] base)
  let .defnInfo request ← getConstInfo ``GuardCapture.request |
    throwError "original native product request is missing"
  let original := request.value
  unless original.getAppFn.isConstOf ``Transport.Product do
    throwError "original requested operation changed"
  let args := original.getAppArgs
  let left := args[args.size - 2]!
  let right := args.back!
  let polynomial := mkConst ``FrameOperand.requestPoly
  kernelCheck `__originalProductLeft (← mkEq left polynomial) (← mkEqRefl polynomial)
  kernelCheck `__originalProductRight (← mkEq right polynomial) (← mkEqRefl polynomial)
  let literal := mkConst ``GuardOperand.polynomial
  kernelCheck `__originalFiniteOperandLeft (← mkEq left literal) (← mkEqRefl literal)
  kernelCheck `__originalFiniteOperandRight (← mkEq right literal) (← mkEqRefl literal)
  let target ← mkAppM ``Transport.Product #[second.reader, literal, literal]
  let remaining ← bounded began
  let proof ← withOptions (maxHeartbeats.set · remaining) do build target supplier
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardProduct
  let product ← retain began (root ++ `product) (← typed target proof)
  let predicate ← withLocalDeclD `polynomial (← inferType literal) fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Transport.Product #[second.reader, p, p])
  let equality ← mkAppM ``congrArg #[predicate, mkConst ``GuardOperand.polynomialNative]
  let nativeType ← mkAppM ``Transport.Product #[second.reader,
    mkConst ``FrameOwners.requestPoly, mkConst ``FrameOwners.requestPoly]
  let native ← retain began (root ++ `nativeProduct)
    (← typed nativeType (← mkAppM ``Eq.mp #[equality, product]))
  logInfo m!"original requested native product module export: originalOperandBothSidesKernelChecked=true sameFirstPoint=true sameSecondPoint=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardProduct
