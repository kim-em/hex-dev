/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureMathlib.NativeCodecs
public meta import HexRealClosureMathlib.NativeReaders

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta Hex.SignDet

initialize registerTraceClass `Hex.RealClosure.nativeAssembly

private def diagnostic (message : String) : MetaM Unit := do
  if (← isTracingEnabledFor `Hex.RealClosure.nativeAssembly) then
    trace[Hex.RealClosure.nativeAssembly] "{message}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn message
        handle.flush

/-- Original owners in predecessor order and their independent scalar reader.
The callback receives equal cached predecessor operations and a strict codec.
Fuel bounds discovery; exhausted or unregistered evidence remains an error. -/
structure NativeAssembly where
  factory : NativeFactory
  read : Nat → NativeOperations → Expr → Expr → Expr → Expr → MetaM Expr
  fuel : Nat := 500

private initialize recordCache : EnvExtension (PHashMap (Array Expr) Expr) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- Reuse only a closed, already checked record for the exact original owner,
kind and operand. Environment rollback also rolls back the cache. -/
private def cacheRecord (key : Array Expr) (produce : MetaM Expr) : MetaM Expr := do
  let cacheable := !key.any (fun expression => expression.hasFVar || expression.hasMVar)
  if cacheable then
    if let some record := recordCache.getState (← getEnv) |>.find? key then
      diagnostic "reused exact checked native record"
      return record
  let record ← produce
  if cacheable && !record.hasFVar && !record.hasMVar && !record.hasSorry then
    modifyEnv fun environment => recordCache.modifyState environment (·.insert key record)
  return record

private def owner (data : NativeAssembly) (index : Nat) : MetaM NativeOwner := do
  let some owner := data.factory.owners[index]? |
    throwError "native assembly has no original owner at depth {index}"
  return owner

private def values (json : Codec.Json) : MetaM (Array Codec.Json) :=
  match json.getArr? with
  | .ok values => pure values
  | .error error => throwError "native polynomial coefficient data: {error}"

/-- Retain checked closed data as one definition so subsequent requests and
native compilation reference it once. This does not replace a semantic proof:
the definition is checked before it enters the environment. -/
private def shareRecord (record : Expr) : MetaM Expr := do
  if record.isConst then return record
  if record.hasFVar || record.hasMVar || record.hasSorry then
    throwError "native assembly cannot retain an incomplete record"
  let type ← inferType record
  let _ ← auditProof record type
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__nativeAssemblyRecord)
  let levels := collectLevelParams (collectLevelParams {} type) record |>.params.toList
  let declaration := Declaration.defnDecl {
    name, levelParams := levels, type, value := record,
    hints := .regular 0, safety := .safe }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let environment ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv environment
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  return mkConst name (levels.map Level.param)

private def operations (data : NativeAssembly) (index : Nat)
    (inventories : Array Inventory) : MetaM NativeOperations := do
  unless inventories.size == 3 * index do throwError "native assembly lost an inventory"
  let first ← owner data 0
  let type ← withTransparency .all (whnf (← inferType first.context))
  unless type.getAppFn.isConstOf ``Context do throwError "native assembly lost its base owner"
  let mut result ← NativeOperations.native type.getAppArgs[0]!
    type.getAppArgs[type.getAppArgs.size - 2]!
  for i in [:index] do
    let current ← owner data i
    let some entries := inventories[3 * i]? | throwError "native packing inventory missing"
    let some signs := inventories[3 * i + 1]? | throwError "native sign inventory missing"
    let some inverses := inventories[3 * i + 2]? | throwError "native inverse inventory missing"
    result ← NativeOperations.extend result current.context entries.facts signs.facts inverses.facts
  return result

mutual

/-- Discover only predecessor requests by checking the reader's acceptance
predicate, then rebuild its expression with the collected closed inventories.
The final record must still pass `checkedRecord` at its original owner. -/
unsafe def NativeAssembly.complete (data : NativeAssembly) (index : Nat)
    (build : NativeOperations → MetaM Expr) : MetaM Expr := do
  diagnostic s!"begin predecessor collection at depth {index}"
  if index == 0 then return ← build (← operations data 0 #[])
  let mut initial := #[]
  let mut types := []
  for i in [:index] do
    let current ← owner data i
    for kind in #[``Packing, ``ValueSign, ``InverseFact] do
      let type ← mkAppM kind #[current.context]
      initial := initial.push (⟨← mkListLit type []⟩ : Inventory)
      types := types ++ [← mkAppM ``List #[type]]
  let rec bindInventories (remaining : List Expr) (arguments : Array Expr) : MetaM Expr := do
    match remaining with
    | [] =>
      let read ← build (← operations data index (arguments.map fun facts => ⟨facts⟩))
      mkLambdaFVars arguments (← mkAppM ``Option.isSome #[read])
    | type :: rest =>
      withLocalDeclD `inventory type fun value => bindInventories rest (arguments.push value)
  let program ← bindInventories types #[]
  diagnostic s!"reader program constructed at depth {index}"
  let mut rules : SimpTheorems := {}
  for name in #[``Dag.replay_eq, ``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let context ← Simp.mkContext (simpTheorems := #[rules]) (config := { decide := false })
    (congrTheorems := ← getSimpCongrTheorems)
  let collected ← collectMany data.fuel program initial context (data.supply index)
  diagnostic s!"collected {collected.requests.size} requests at depth {index}"
  match collected.outcome with
  | .checked true _ _ => build (← operations data index collected.inventories)
  | .checked false _ _ => throwError "native original record packet was rejected"
  | _ => throwError "native predecessor discovery did not finish after {collected.requests.size} requests"

/-- Strict recursive graph and polynomial codecs share this assembly's
original owners and scalar readers. Every recursive request has lower depth. -/
unsafe def NativeAssembly.codecs (data : NativeAssembly) : MetaM NativeCodecs := do
  let base ← owner data 0
  return ⟨data.factory, base.valueCodec, fun index codec polynomial claimed packet =>
    data.complete index fun operations => data.read index operations codec polynomial claimed packet⟩

/-- Independently read a scalar packet using saturated predecessor inventories
and a strict graph codec. Native production contributes only tags and JSON. -/
unsafe def NativeAssembly.scalar (data : NativeAssembly) (index : Nat)
    (polynomial : Expr) : MetaM Expr := do
  let current ← owner data index
  cacheRecord #[current.context, toExpr index, toExpr "SignFact", polynomial] do
    diagnostic s!"produce scalar packet at depth {index}"
    let (claimed, packet) ← NativePackets.sign current.valueCodec current.contextCodec
      current.context polynomial (data.factory.owners.map NativeOwner.context)
    let strict ← (← data.codecs).graph index packet
    diagnostic s!"strict scalar graph codec ready at depth {index}"
    let reader ← data.complete index fun operations =>
      data.read index operations strict polynomial (toExpr claimed) (jsonExpr packet)
    shareRecord (← data.factory.readScalar current polynomial (toExpr claimed) reader)

/-- Decode a native-produced polynomial through independently checked child
facts. Its literal representation can be used as a supplied key; agreement
with any computation is checked by the eventual original operation reader. -/
unsafe def NativeAssembly.polynomial (data : NativeAssembly) (index : Nat)
    (polynomial : Expr) : MetaM Expr := do
  let current ← owner data index
  let packet ← NativePackets.polynomial current.valueCodec polynomial
    (data.factory.owners.map NativeOwner.context)
  let strict ← (← data.codecs).values index (← values packet)
  checkedRecord (← mkAppM ``Except.toOption
    #[← mkAppM ``Codec.readPoly #[strict, jsonExpr packet]])

/-- Check the original packing request with a literal supplied remainder fact
and cached reduction. The reader verifies the exact difference from that
remainder; no native equality or proof object is exported. -/
unsafe def NativeAssembly.packing (data : NativeAssembly) (index : Nat)
    (polynomial : Expr) : MetaM Expr := do
  let current ← owner data index
  cacheRecord #[current.context, toExpr index, toExpr "Packing", polynomial] do
    let remainder ← data.polynomial index (mkApp current.reduction polynomial)
    let fact ← data.scalar index remainder
    diagnostic "packing: scalar supplied"
    let facts ← mkListLit (← inferType fact) [fact]
    diagnostic "packing: original fact inventory constructed"
    let packet ← NativePackets.packing current.valueCodec current.contextCodec current.context
      current.reduction polynomial (data.factory.owners.map NativeOwner.context)
    diagnostic "packing: native packet produced"
    let strict ← (← data.codecs).graph index packet
    diagnostic "packing: strict graph codec constructed"
    let reader ← data.complete index fun operations => do
      let (reduce, same) ← operations.reduction current.context
      operations.packingReader current.context strict current.contextCodec reduce same facts
        polynomial (jsonExpr packet)
    shareRecord (← checkedRecord reader)

/-- Check the retained operand's cached tag through its original packet. -/
unsafe def NativeAssembly.valueSign (data : NativeAssembly) (index : Nat)
    (value : Expr) : MetaM Expr := do
  let current ← owner data index
  cacheRecord #[current.context, toExpr index, toExpr "ValueSign", value] do
    let packet ← NativePackets.storedSign current.valueCodec current.contextCodec value
      (data.factory.owners.map NativeOwner.context)
    let strict ← (← data.codecs).graph index packet
    let reader ← data.complete index fun operations =>
      operations.valueSignReader current.context strict current.contextCodec value (jsonExpr packet)
    shareRecord (← checkedRecord reader)

/-- Check the actual local splitting inverse and original operand. A supplied
literal candidate is independently packed and compared with the candidate
computed using equal cached coefficient operations. -/
unsafe def NativeAssembly.inverse (data : NativeAssembly) (index : Nat)
    (argument : Expr) : MetaM Expr := do
  let current ← owner data index
  cacheRecord #[current.context, toExpr index, toExpr "InverseFact", argument] do
    let candidate ← data.polynomial index (← mkAppM ``Element.inverseCandidate #[argument])
    let entry ← data.packing index candidate
    let result ← mkAppM ``Packing.value #[entry]
    let packet ← NativePackets.inverse current.valueCodec current.contextCodec current.context
      argument result (data.factory.owners.map NativeOwner.context)
    let strict ← (← data.codecs).graph index packet
    let reader ← data.complete index fun operations =>
      operations.inverseReader current.context strict current.contextCodec argument entry (jsonExpr packet)
    shareRecord (← checkedRecord reader)

/-- Supply only requests at a strictly earlier original owner. Same labels in
unregistered contexts cannot satisfy a predecessor inventory. -/
unsafe def NativeAssembly.supply (data : NativeAssembly) (before : Nat)
    (request : Request) (_inventories : Array Inventory) : MetaM (Option Expr) := do
  for i in [:before] do
    let current ← owner data i
    if current.context == request.context ||
        (← withTransparency .all (isDefEq current.context request.context)) then
      let kind := match request.kind with
        | .coefficient => "packing"
        | .valueSign => "stored sign"
        | .inverse => "inverse"
      diagnostic s!"supply {kind} at depth {i}"
      match request.kind with
      | .coefficient => return some (← data.packing i request.polynomial)
      | .valueSign =>
        let some value := request.value | throwError "native stored-sign request lost its operand"
        return some (← data.valueSign i value)
      | .inverse =>
        let some value := request.value | throwError "native inverse request lost its operand"
        return some (← data.inverse i value)
  return none

end

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
