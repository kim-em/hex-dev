/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.KernelReplay
public import HexRealClosure.RecordPackets
public meta import HexRealClosure.RecordPackets
public import HexRealClosure.ChildPackets
public meta import HexRealClosure.ChildPackets
public meta import HexRealClosureMathlib.NativeRecords
public import HexRealClosure.InversePackets
public meta import HexRealClosure.InversePackets
public meta import Lean.Meta.Eval
public meta import HexRealClosureMathlib.NativeValues

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.NativePackets
open Lean Meta Hex.SignDet

private def complete (program : Expr) : MetaM Expr := do
  let program ← instantiateMVars program
  if program.hasMVar || program.hasFVar || program.hasSorry then
    throwError "native packet production requires complete closed input"
  -- Kernel reduction can expose recursive list helpers with no exported
  -- compiler signatures. Restore their public wrappers
  -- only after the ordinary kernel checks equality of the complete program.
  let restored ← Core.transform program (post := fun expression => do
    let .const name levels := expression.getAppFn | return .done expression
    let .str wrapper "_f" := name | return .done expression
    unless (← getEnv).contains wrapper do return .done expression
    let helper ← getConstInfo name
    let mut type := helper.type
    let mut index := 0
    let mut below? : Option Nat := none
    while let .forallE _ domain body _ := type do
      if let .const (.str _ "below") _ := domain.getAppFn then
        below? := some index
        break
      type := body
      index := index + 1
    let some below := below? | return .done expression
    let arguments := expression.getAppArgs
    if arguments.size ≤ below then return .done expression
    return .done (mkAppN (mkConst wrapper levels)
      (arguments.extract 0 below ++ arguments.extract (below + 1) arguments.size)))
  if restored != program then
    try
      let equation ← mkEq program restored
      let proof ← mkEqRefl program
      let _ ← auditProof proof equation
      kernelCheck `__nativePacketProgram equation proof
    catch error =>
      throwError "native recursive helper restoration failed its complete-program kernel check: {error.toMessageData}"
  return restored


/-- Evaluate only the executable packet producer. Coefficient and predecessor
types remain in the typed application; evaluation returns integer/JSON data,
never native proof objects. The caller must independently check that data. -/
unsafe def sign (value ctx owner polynomial : Expr) (owners : Array Expr := #[]) :
    MetaM (Int × Codec.Json) := do
  let polynomial ← NativeValues.prepare owners polynomial
  let program ← complete (← mkAppM ``Context.buildSignPacket #[owner, value, ctx, polynomial])
  let result ← evalExpr (Except BuildError (Int × Codec.Json)) (← inferType program) program
    (checkMeta := false)
  match result with
  | .ok packet => return packet
  | .error error => throwError "native scalar packet production failed: {reprStr error}"

/-- Export the original packing request's joint graph for any actual native
owner and its coefficient/context codecs. No coefficient type is cast to Rat. -/
unsafe def packing (value ctx owner reduce polynomial : Expr) (owners : Array Expr := #[]) :
    MetaM Codec.Json := do
  let polynomial ← NativeValues.prepare owners polynomial
  let program ← complete
    (← mkAppM ``Context.buildPackingPacket #[owner, value, ctx, reduce, polynomial])
  let result ← evalExpr (Except BuildError Codec.Json) (← inferType program) program
    (checkMeta := false)
  match result with
  | .ok packet => return packet
  | .error error => throwError "native packing packet production failed: {reprStr error}"

/-- Export literal signs of the stored operand, including its original
representative. The caller retains that operand when checking the packet. -/
unsafe def storedSign (codec ctx value : Expr) (owners : Array Expr := #[]) :
    MetaM Codec.Json := do
  let value ← NativeValues.prepare owners value
  let program ← complete (← mkAppM ``ValueSign.buildPacket #[codec, ctx, value])
  let result ← evalExpr (Except BuildError Codec.Json) (← inferType program) program
    (checkMeta := false)
  match result with
  | .ok packet => return packet
  | .error error => throwError "native stored-sign packet production failed: {reprStr error}"

/-- Export a typed literal polynomial as JSON, rebuilding only its native
coefficient data. The checked reader must retain the untouched original key. -/
unsafe def polynomial (codec input : Expr) (owners : Array Expr := #[]) : MetaM Codec.Json := do
  let input ← NativeValues.prepare owners input
  let program ← complete (← mkAppM ``Codec.poly #[codec, input])
  evalExpr Codec.Json (← inferType program) program (checkMeta := false)

/-- Export the original operand's inverse equation as literal graph data.
The independent reader must check the retained packing record and operand. -/
unsafe def inverse (codec ctx owner argument result : Expr) (owners : Array Expr := #[]) :
    MetaM Codec.Json := do
  let argument ← NativeValues.prepare owners argument
  let result ← NativeValues.prepare owners result
  let program ← complete
    (← mkAppM ``Context.buildInversePacket #[owner, codec, ctx, argument, result])
  let packet ← evalExpr (Except BuildError Codec.Json) (← inferType program) program
    (checkMeta := false)
  match packet with
  | .ok packet => return packet
  | .error error => throwError "native inverse packet production failed: {reprStr error}"

/-- Discover only literal child polynomial/tag data using the actual typed
native predecessor codec. The caller must independently prove these child
requests and then check the original graph with its strict coefficient reader. -/
unsafe def children (codec ctx owner packet : Expr) : MetaM Codec.Json := do
  let program ← complete (← mkAppM ``Context.childPackets #[owner, codec, ctx, packet])
  let children ← evalExpr (Except String Codec.Json) (← inferType program) program
    (checkMeta := false)
  match children with
  | .ok children => return children
  | .error error => throwError "native child packet discovery failed: {error}"

end Hex.RealClosure.Algebraic.KernelReplay.NativePackets
