/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.NativePackets
public meta import HexRealClosureTheory.NativeRecords
public meta import HexRealClosureTheory.NativeModels

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta Hex.SignDet

/-- One actual immutable owner with its native codecs, original reduction and
independent scalar reader. The callback constructs a reader expression from
literal graph data; it does not supply a native proof object. -/
structure NativeOwner where
  context : Expr
  valueCodec : Expr
  contextCodec : Expr
  reduction : Expr
  reductionEquation : Expr
  scalarReader : Expr → Expr → Expr → MetaM Expr

/-- Use the actual retained predecessor model for scalar correspondence laws.
The caller supplies its native codecs and reduction, retaining their types. -/
def NativeModels.owner (models : NativeModels) (predecessor : Nat)
    (context valueCodec contextCodec reduction reductionEquation : Expr) : NativeOwner :=
  ⟨context, valueCodec, contextCodec, reduction, reductionEquation,
    fun polynomial claimed packet =>
      models.signReader predecessor context valueCodec contextCodec polynomial claimed packet⟩

/-- Native producers export only graph data. Every resulting record is rebuilt
by an independent reader and checked by the ordinary kernel at the original
owner and original request. Registered owners need not share a coefficient type. -/
structure NativeFactory where
  owners : Array NativeOwner

private def retained (factory : NativeFactory) : Array Expr :=
  factory.owners.map NativeOwner.context

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_RECORD_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- Cache only a complete closed reader and its exact original bindings. The
cache follows the environment, so rollback also rolls back retained records. -/
private initialize scalarCache : EnvExtension (PHashMap (Array Expr) Expr) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def checkScalar (owner polynomial claimed fact : Expr) : MetaM Unit := do
  -- The actual owner already retains every coefficient dictionary. Reuse
  -- those arguments rather than synthesizing them again from its carrier.
  let ownerType ← withTransparency .all (whnf (← inferType owner))
  let .const name levels := ownerType.getAppFn |
    throwError "native scalar owner has no context type"
  unless name == ``Context do throwError "native scalar owner is not algebraic"
  let expected := mkAppN (mkConst ``SignFact levels) (ownerType.getAppArgs.push owner)
  diagnostic "scalar: original owner type constructed"
  unless ← withTransparency .all (isDefEq (← inferType fact) expected) do
    throwError "native scalar reader changed its original owner"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let ownerBinding ← mkAppOptM ``Eq.refl #[some expected, some fact]
  let ownerBinding ← mkLambdaFVars locals ownerBinding (usedOnly := true)
  let ownerStatement ← inferType ownerBinding
  let _ ← auditProof ownerBinding ownerStatement
  kernelCheck `__nativeScalarOwner ownerStatement ownerBinding
  diagnostic "scalar: original owner checked"
  let locals := (← getLCtx).getFVarIds.map mkFVar
  for (index, original) in #[(0, polynomial), (1, claimed)] do
    let equation ← mkEq (Expr.proj ``SignFact index fact) original
    let proof ← mkLambdaFVars locals (← mkEqRefl original) (usedOnly := true)
    let statement ← mkForallFVars locals equation (usedOnly := true)
    let _ ← auditProof proof statement
    diagnostic s!"scalar: original binding {index} constructed"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let checked := (← getEnv).toKernelEnv.addDecl options
      (.thmDecl { name := `__nativeScalarBinding, levelParams := [], type := statement, value := proof })
    unless ← acceptKernel checked do
      throwError "native scalar reader changed its original request"
    diagnostic s!"scalar: original binding {index} kernel checked"

/-- Check a supplied scalar reader at the original owner, polynomial and
claimed sign before returning its fact. -/
def NativeFactory.readScalar (_factory : NativeFactory) (owner : NativeOwner)
    (polynomial claimed reader : Expr) : MetaM Expr := do
  let key := #[owner.context, polynomial, claimed, reader]
  let cacheable := !key.any (fun expression => expression.hasFVar || expression.hasMVar)
  if cacheable then
    if let some fact := scalarCache.getState (← getEnv) |>.find? key then
      diagnostic "scalar: exact checked reader reused"
      return fact
  let fact ← checkedRecord reader
  checkScalar owner.context polynomial claimed fact
  if cacheable && fact.isConst then
    modifyEnv fun environment => scalarCache.modifyState environment (·.insert key fact)
  return fact

/-- Supply one scalar fact from independently checked literal evidence. -/
unsafe def NativeFactory.scalar (factory : NativeFactory) (owner : NativeOwner)
    (polynomial : Expr) : MetaM Expr := do
  let (claimed, packet) ← NativePackets.sign owner.valueCodec owner.contextCodec
    owner.context polynomial (retained factory)
  factory.readScalar owner polynomial (toExpr claimed)
    (← owner.scalarReader polynomial (toExpr claimed) (jsonExpr packet))

/-- Supply the exact original packing request, including a zero difference
from the retained remainder. No polynomial is cast to a fixed base field. -/
unsafe def NativeFactory.packing (factory : NativeFactory) (owner : NativeOwner)
    (polynomial : Expr) : MetaM Expr := do
  let kept := mkApp owner.reduction polynomial
  let fact ← factory.scalar owner kept
  let facts ← mkListLit (← inferType fact) [fact]
  let packet ← NativePackets.packing owner.valueCodec owner.contextCodec owner.context
    owner.reduction polynomial (retained factory)
  checkedRecord (← mkAppM ``Packing.readPacket?
    #[owner.valueCodec, owner.contextCodec, owner.reduction, owner.reductionEquation,
      facts, polynomial, jsonExpr packet])

/-- Keep the actual stored operand when checking its cached sign. -/
unsafe def NativeFactory.valueSign (factory : NativeFactory) (owner : NativeOwner)
    (value : Expr) : MetaM Expr := do
  let packet ← NativePackets.storedSign owner.valueCodec owner.contextCodec value
    (retained factory)
  checkedRecord (← mkAppM ``ValueSign.readPacket?
    #[owner.valueCodec, owner.contextCodec, value, jsonExpr packet])

/-- Check both the native inverse candidate's packing and the inverse equation
for the literal original operand. A zero or mismatched operand rejects. -/
unsafe def NativeFactory.inverse (factory : NativeFactory) (owner : NativeOwner)
    (argument : Expr) : MetaM Expr := do
  let candidate ← mkAppM ``Element.inverseCandidate #[argument]
  let entry ← factory.packing owner candidate
  let result ← mkAppM ``Packing.value #[entry]
  let packet ← NativePackets.inverse owner.valueCodec owner.contextCodec owner.context
    argument result (retained factory)
  checkedRecord (← mkAppM ``InverseFact.readPacket?
    #[owner.valueCodec, owner.contextCodec, argument, entry, jsonExpr packet])

/-- Supplier for demanded packing, stored-sign and inverse requests. Missing
owners remain explicit; a retained owner is matched by its actual typed term. -/
unsafe def NativeFactory.supply (factory : NativeFactory) (request : Request)
    (_inventories : Array Inventory) : MetaM (Option Expr) := do
  for owner in factory.owners do
    if owner.context == request.context ||
        (← withTransparency .all (isDefEq owner.context request.context)) then
      match request.kind with
      | .coefficient => return some (← factory.packing owner request.polynomial)
      | .valueSign =>
        let some value := request.value | throwError "native stored-sign request lost its operand"
        return some (← factory.valueSign owner value)
      | .inverse =>
        let some value := request.value | throwError "native inverse request lost its operand"
        return some (← factory.inverse owner value)
  return none

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
