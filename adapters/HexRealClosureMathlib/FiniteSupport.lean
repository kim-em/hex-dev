/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteData
public meta import HexRealClosureMathlib.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- An exact lookup reached by finite transport, together with its original
local hypotheses. The inventory is retained separately from the requested key. -/
structure Lookup where
  leaf : Leaf
  inventory : Expr
  key : Expr
  request : Request

/-- Recognize the original packing, stored-sign or inverse lookup without
reducing the lookup itself. Inverse requests retain the operand polynomial;
discovery does not compute an inverse candidate. -/
def Leaf.lookup? (leaf : Leaf) : MetaM (Option Lookup) := leaf.withContext do
  let type := leaf.type
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``Eq && arguments.size == 3 &&
      arguments[0]!.isConstOf ``Bool && arguments[2]!.isConstOf ``Bool.true do return none
  let left := arguments[1]!
  unless left.getAppFn.isConstOf ``Option.isSome do return none
  let lookup := left.getAppArgs.back!
  let kind ← if lookup.getAppFn.isConstOf ``Packing.find then pure EvidenceKind.coefficient
    else if lookup.getAppFn.isConstOf ``ValueSign.find then pure EvidenceKind.valueSign
    else if lookup.getAppFn.isConstOf ``InverseFact.find then pure EvidenceKind.inverse
    else return none
  let args := lookup.getAppArgs
  unless args.size ≥ 2 do throwError "invalid finite lookup"
  let option ← whnf (← inferType lookup)
  unless option.getAppFn.isConstOf ``Option do throwError "invalid finite lookup result"
  let record := option.getAppArgs.back!
  let key := args.back!
  let polynomial ← if kind == .coefficient then pure key
    else mkAppM ``Element.polynomial #[key]
  return some ⟨leaf, args[args.size - 2]!, key,
    { context := record.getAppArgs.back!, polynomial, kind,
      value := if kind == .coefficient then none else some key }⟩

private def addRecord (lookup : Lookup) (fact : Expr)
    (inventories : Array Inventory) : MetaM (Array Inventory) := lookup.leaf.withContext do
  if fact.hasFVar || fact.hasMVar || fact.hasSorry then throwError "incomplete finite support record"
  let type ← inferType fact
  let expected := match lookup.request.kind with
    | .coefficient => ``Packing
    | .valueSign => ``ValueSign
    | .inverse => ``InverseFact
  unless type.getAppFn.isConstOf expected do throwError "finite support record has the wrong kind"
  unless ← withTransparency .all (isDefEq type.getAppArgs.back! lookup.request.context) do
    throwError "finite support record has the wrong context"
  let key ← match lookup.request.kind with
    | .coefficient => mkAppM ``Packing.original #[fact]
    | .valueSign => mkAppM ``ValueSign.value #[fact]
    | .inverse => do
      let inverse ← mkAppM ``InverseFact.inverse #[fact]
      mkAppM ``Packing.Inverse.argument #[inverse]
  unless ← withTransparency .all (isDefEq key lookup.key) do
    throwError "finite support record binds a different key: {key}; requested: {lookup.key}"
  let statement ← mkEq key lookup.key
  let proof ← mkEqRefl key
  let binders := (← getLCtx).getFVarIds.map mkFVar
  let statement ← mkForallFVars binders statement
  let proof ← mkLambdaFVars binders proof
  let _ ← auditProof proof statement
  kernelCheck `__finiteSupportBinding statement proof
  let equation ← mkEq fact fact
  let reflexive ← mkEqRefl fact
  let _ ← auditProof reflexive equation
  kernelCheck `__finiteSupportRecord equation reflexive
  for i in [:inventories.size] do
    let some inventory := inventories[i]? | throwError "finite inventory index mismatch"
    if ← withTransparency .all (isDefEq inventory.facts lookup.inventory) then
      let facts ← mkAppM ``List.cons #[fact, inventory.facts]
      return inventories.set! i ⟨facts⟩
  throwError "finite lookup refers to an unregistered inventory"

/-- An unresolved result retains all exact remaining obligations and makes no
proof claim. A complete result includes a closed ordinary-kernel theorem,
abstracting the caller's local variables and hypotheses. -/
inductive SupportResult where
  | complete (type proof : Expr)
  | unresolved (leaves : Array Leaf)

/-- The inventories actually used by finite transport, including records for
keys reached only by construction equations or transport guards. -/
structure Support where
  inventories : Array Inventory
  requests : Array Request
  result : SupportResult

/-- Collect lookup records reached by the finite proof premises, rather than
only those reached by Boolean acceptance. The type builder is rerun with the
updated inventories. All other leaves are returned until the caller supplies
their predecessor arithmetic and sign premises. Fuel bounds unsuccessful
collection; it is not evidence of completeness. -/
def collectSupport (fuel : Nat) (initial : Array Inventory)
    (type : Array Inventory → MetaM Expr) (supply : Supplier)
    (record : Lookup → Array Inventory → MetaM (Option Expr)) : MetaM Support := do
  let mut seen : Array Expr := #[]
  for inventory in initial do
    if inventory.facts.hasFVar || inventory.facts.hasMVar || inventory.facts.hasSorry then
      throwError "incomplete finite support inventory"
    let list ← whnf (← inferType inventory.facts)
    unless list.getAppFn.isConstOf ``List do throwError "finite support inventory must be a list"
    let element := list.getAppArgs.back!
    unless #[``Packing, ``ValueSign, ``InverseFact].any
        (fun name => element.getAppFn.isConstOf name) do
      throwError "finite support inventory has an unsupported record type"
    for previous in seen do
      if ← isDefEq previous element then throwError "duplicate finite support inventory"
    seen := seen.push element
    let equation ← mkEq inventory.facts inventory.facts
    let proof ← mkEqRefl inventory.facts
    let _ ← auditProof proof equation
    kernelCheck `__finiteSupportInventory equation proof
  go fuel initial #[]
where
  go (remaining : Nat) (inventories : Array Inventory) (requests : Array Request) :
      MetaM Support := do
    let statement ← type inventories
    if statement.hasMVar || statement.hasSorry then
      throwError "incomplete finite support statement"
    unless ← isProp statement do throwError "finite support statement must be a proposition"
    let missing ← leaves statement supply
    if missing.isEmpty then
      let proof ← build statement supply
      let binders := (← getLCtx).getFVarIds.map mkFVar
      let statement ← mkForallFVars binders statement
      let proof ← mkLambdaFVars binders proof
      if statement.hasFVar || proof.hasFVar then throwError "open finite support theorem"
      let _ ← auditProof proof statement
      kernelCheck `__finiteSupportProof statement proof
      return ⟨inventories, requests, .complete statement proof⟩
    for leaf in missing do
      if let some lookup ← leaf.lookup? then
        match remaining with
        | 0 => return ⟨inventories, requests, .unresolved missing⟩
        | n + 1 =>
          let supplied ← lookup.leaf.withContext (record lookup inventories)
          let some fact := supplied | return ⟨inventories, requests, .unresolved missing⟩
          let inventories ← addRecord lookup fact inventories
          return ← go n inventories (requests.push lookup.request)
    return ⟨inventories, requests, .unresolved missing⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
