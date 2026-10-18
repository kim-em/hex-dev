/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardCoefficientControl
public meta import KernelReplay.GuardCoefficientControl
import all KernelReplay.GuardCoefficientControl
import all KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientReduce
open Lean Meta FiniteData GuardDescriptorInputs

private def head (began : Nat) (value : Expr) : MetaM Expr := do
  let _ ← bounded began
  withOptions (smartUnfolding.set · true) do withTransparency .all (whnf value)

private def string (began : Nat) (value : Expr) : MetaM String := do
  let some result := getStringValue? (← head began value) |
    throwError "coefficient codec did not produce a literal string"
  return result

private def integer (began : Nat) (value : Expr) : MetaM Int := do
  let value ← head began value
  let args := value.getAppArgs
  unless value.getAppFn.isConstOf ``Int.ofNat || value.getAppFn.isConstOf ``Int.negSucc do
    throwError "coefficient codec did not produce an integer constructor"
  let some n ← getNatValue? (← head began args.back!) |
    throwError "coefficient codec did not produce a natural literal"
  return if value.getAppFn.isConstOf ``Int.ofNat then Int.ofNat n else Int.negSucc n

mutual
/-- Evaluate only JSON constructor fields. Never reduce the full native owner
or compile the requested coefficient. The result is a lookup hint only. -/
private def json (began fuel : Nat) (value : Expr) : MetaM SignDet.Codec.Json := do
  let fuel + 1 := fuel | throwError "coefficient JSON depth bound exhausted"
  let value ← head began value
  let args := value.getAppArgs
  let name := value.getAppFn.constName?
  if name == some ``SignDet.Codec.Json.Value.null then return .null
  if name == some ``SignDet.Codec.Json.Value.bool then
    let value ← head began args.back!
    if value.isConstOf ``Bool.true then return .bool true
    if value.isConstOf ``Bool.false then return .bool false
    throwError "coefficient codec did not produce a Boolean constructor"
  if name == some ``SignDet.Codec.Json.Value.number then return .number (← integer began args.back!)
  if name == some ``SignDet.Codec.Json.Value.string then return .string (← string began args.back!)
  if name == some ``SignDet.Codec.Json.Value.array then return .array (← values began fuel args.back!)
  if name == some ``SignDet.Codec.Json.Value.object then return .object (← fields began fuel args.back!)
  throwError "coefficient codec did not produce a JSON constructor"

private def values (began fuel : Nat) (value : Expr) : MetaM SignDet.Codec.Json.Values := do
  let fuel + 1 := fuel | throwError "coefficient JSON array bound exhausted"
  let value ← head began value
  if value.getAppFn.isConstOf ``SignDet.Codec.Json.Values.nil then return .nil
  unless value.getAppFn.isConstOf ``SignDet.Codec.Json.Values.cons do
    throwError "coefficient codec did not produce an array constructor"
  let args := value.getAppArgs
  return .cons (← json began fuel args[0]!) (← values began fuel args[1]!)

private def fields (began fuel : Nat) (value : Expr) : MetaM SignDet.Codec.Json.Fields := do
  let fuel + 1 := fuel | throwError "coefficient JSON object bound exhausted"
  let value ← head began value
  if value.getAppFn.isConstOf ``SignDet.Codec.Json.Fields.nil then return .nil
  unless value.getAppFn.isConstOf ``SignDet.Codec.Json.Fields.cons do
    throwError "coefficient codec did not produce an object constructor"
  let args := value.getAppArgs
  return .cons (← string began args[0]!) (← json began fuel args[1]!) (← fields began fuel args[2]!)
end

private def current (began : Nat) (value : Expr) : MetaM Expr := do
  let type ← inferType value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientData)
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  return mkConst name

/-- Compile the same small inventory aliases as the established index. Decode
each requested coefficient's JSON by constructor reduction, and kernel-check
the original inventory position and original guarded-domain proposition. -/
unsafe def prepare (began : Nat) (agreement : Expr) : MetaM Supplier := do
  let arguments := (← inferType agreement).getAppArgs
  let inventory := arguments.back!
  let domain := arguments[arguments.size - 4]!
  let codec ← mkAppM ``BaseContext.Element.codec #[mkConst ``FiniteBaseProbe.base]
  let encoder ← mkAppM ``SignDet.ValueCodec.encode #[codec]
  let mut aliases : Array (Name × Expr) := #[]
  for name in #[``GuardInventoryReplay.first.entries, ``GuardInventoryReplay.first.records,
      ``GuardInventoryReplay.first.facts, ``GuardInventoryReplay.support] do
    let .defnInfo info ← getConstInfo name | throwError "missing coefficient inventory data"
    unless info.levelParams.isEmpty do throwError "polymorphic coefficient inventory data"
    let known := aliases
    let value := info.value.replace fun expression => do
      let some old := expression.constName? | none
      (known.find? (·.1 == old)).map (·.2)
    let replacement ← current began value
    kernelCheck `__reducedCoefficientDataBinding
      (← mkEq (mkConst name) replacement) (← mkEqRefl replacement)
    aliases := aliases.push (name, replacement)
  kernelCheck `__reducedCoefficientInventory
    (← mkEq inventory (mkConst ``GuardInventoryReplay.support))
    (← mkEqRefl (mkConst ``GuardInventoryReplay.support))
  let program ← mkAppM ``GuardCoefficientIndex.encodeInventory #[aliases.back!.2]
  let encoded ← evalExpr SignDet.Codec.Json (← inferType program) program (checkMeta := false)
  let .array literal := encoded | throwError "coefficient inventory encoding is not an array"
  let mut positions : PHashMap SignDet.Codec.Json Nat := {}
  for (value, index) in literal.toArray.zipIdx do
    unless (positions.find? value).isSome do positions := positions.insert value index
  let cache ← IO.mkRef ({} : PHashMap Expr Expr)
  return fun type => do
    if type.hasFVar || type.hasMVar || type.hasSorry then return none
    let .app _ wanted := type | return none
    unless type.getAppFn == domain.getAppFn do return none
    if let some proof := (← cache.get).find? type then return some proof
    let encoded ← json began 4096 (mkApp encoder wanted)
    let some position := positions.find? encoded |
      throwError "reduced coefficient has no position in the original inventory"
    let proof ← GuardCoefficientIndex.positionProof agreement type position
    let typed ← withTransparency .all do mkAppOptM ``id #[some type, some proof]
    let name ← mkFreshUserName `__reducedCoefficientDomain
    let proof ← retain began name typed
    cache.modify (·.insert type proof)
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"reduced coefficient original position kernel checked: index={position} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
        handle.flush
    return some proof

end Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientReduce
