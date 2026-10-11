/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.KernelReplay
public import HexRealClosure.RecordPackets
public meta import HexRealClosure.RecordPackets
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
  return program

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

end Hex.RealClosure.Algebraic.KernelReplay.NativePackets
