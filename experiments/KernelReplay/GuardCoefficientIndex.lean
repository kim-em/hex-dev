/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorInputs
public meta import KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientIndex
open Lean Meta FiniteData GuardDescriptorInputs

@[noinline, nospecialize] def encodeInventory
    (values : List (BaseContext.Element FiniteBaseProbe.base)) : SignDet.Codec.Json :=
  SignDet.Codec.list (BaseContext.Element.codec FiniteBaseProbe.base).encode values

meta section

private def trace (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- Keep the compilation state when `evalExpr` would otherwise replace the
environment by its imported snapshot. Only small native data/function aliases
are retained; no algebraic owner or semantic model is reconstructed. -/
private def current (began : Nat) (value : Expr) : MetaM Expr := do
  let type ← inferType value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientInput)
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
  let _ ← bounded began
  return mkConst name

/-- Form a candidate from the original list position and original requested
coefficient. The caller must check this expression against `type` in the kernel. -/
def positionProof (agreement type : Expr) (position : Nat) : MetaM Expr := do
  let .app _ wanted := type | throwError "coefficient membership is not an application"
  let inventory := (← inferType agreement).getAppArgs.back!
  let membership ← mkAppOptM ``List.mem_of_getElem?
    #[none, some inventory, some (toExpr position), some wanted]
  let .forallE _ equation _ _ ← whnf (← inferType membership) |
    throwError "native coefficient position lost its equality premise"
  let member := mkApp membership (← mkEqRefl equation.getAppArgs.back!)
  mkAppM ``And.left #[mkApp2 agreement wanted member]

/-- A native coefficient encoding selects positions only. Every returned
membership proof checks the original list and coefficient in the kernel. -/
unsafe def prepare (began : Nat) (agreement : Expr) : MetaM Supplier := do
  let arguments := (← inferType agreement).getAppArgs
  let inventory := arguments.back!
  let domain := arguments[arguments.size - 4]!
  let codec ← mkAppM ``BaseContext.Element.codec #[mkConst ``FiniteBaseProbe.base]
  -- Retain only these four computational data bodies in dependency order.
  -- Imported checked-data declarations need not have registered runtime code.
  let mut aliases : Array (Name × Expr) := #[]
  for name in #[``GuardInventoryReplay.first.entries, ``GuardInventoryReplay.first.records,
      ``GuardInventoryReplay.first.facts, ``GuardInventoryReplay.support] do
    trace s!"native coefficient index compiles retained data: {name}"
    let .defnInfo info ← getConstInfo name | throwError "missing retained coefficient data"
    unless info.levelParams.isEmpty do throwError "unexpected polymorphic coefficient data"
    let known := aliases
    let value := info.value.replace fun expression => do
      let some old := expression.constName? | none
      (known.find? (·.1 == old)).map (·.2)
    let replacement ← current began value
    kernelCheck `__nativeCoefficientDataBinding
      (← mkEq (mkConst name) replacement) (← mkEqRefl replacement)
    aliases := aliases.push (name, replacement)
    let _ ← bounded began
  trace "native coefficient index encodes retained inventory"
  let namedInventory := mkConst ``GuardInventoryReplay.support
  kernelCheck `__coefficientIndexInventory
    (← mkEq inventory namedInventory) (← mkEqRefl namedInventory)
  let compiledInventory := aliases.back!.2
  let encoder ← current began (← mkAppM ``SignDet.ValueCodec.encode #[codec])
  let program ← mkAppM ``encodeInventory #[compiledInventory]
  let encoded ← evalExpr SignDet.Codec.Json (← inferType program) program (checkMeta := false)
  let .array values := encoded | throwError "native coefficient index did not return a full array"
  let values := values.toArray
  let mut positions : PHashMap String Nat := {}
  for (value, index) in values.zipIdx do
    let key := reprStr value
    unless (positions.find? key).isSome do positions := positions.insert key index
  let keys := positions
  let cache ← IO.mkRef ({} : PHashMap Expr Expr)
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"native coefficient index prepared: entries={values.size} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
      handle.flush
  return fun type => do
    if type.hasFVar || type.hasMVar || type.hasSorry then return none
    let .app predicate wanted := type | return none
    unless predicate == domain || (← withNewMCtxDepth do
        withTransparency .all (isDefEq predicate domain)) do return none
    if let some proof := (← cache.get).find? type then return some proof
    let _ ← bounded began
    let program := mkApp encoder wanted
    let encoded ← evalExpr SignDet.Codec.Json (← inferType program) program (checkMeta := false)
    let some position := keys.find? (reprStr encoded) | return none
    let proof ← positionProof agreement type position
    let tag ← mkFreshUserName `coefficient
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientIndex ++ tag
    let remaining ← bounded began
    let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true))
    let proof := mkConst name
    cache.modify (·.insert type proof)
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"native coefficient position kernel checked: index={position} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
        handle.flush
    return some proof

end

end Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientIndex
