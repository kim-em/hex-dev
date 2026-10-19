/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteData
public meta import HexRealClosureTheory.FiniteData

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

/-- Close a statement and its proof over the same used declarations. Solved
metavariables, including levels in local types, are instantiated before selecting
dependencies. Unused discovery hypotheses contribute no checked premises. -/
private def close (type proof : Expr) : MetaM (Expr × Expr) := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  let context ← instantiateLCtxMVars (← getLCtx)
  withLCtx context (← getLocalInstances) do
    let used ← (collectFVars (collectFVars {} type) proof).addDependencies
    let binders := context.getFVarIds.filter used.fvarSet.contains |>.map mkFVar
    let type ← mkForallFVars binders type (usedLetOnly := false) (generalizeNondepLet := false)
    let proof ← mkLambdaFVars binders proof (usedLetOnly := false) (generalizeNondepLet := false)
    return (← instantiateMVars type, ← instantiateMVars proof)

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

/-- Change only the inventory of an exact lookup. The owner, key, kind and
local hypotheses remain those of the original request. -/
def Lookup.withInventory (lookup : Lookup) (inventory : Expr) : Lookup := Id.run do
  let found := lookup.leaf.type.getAppArgs[1]!.getAppArgs.back!
  let arguments := found.getAppArgs
  let refreshed := mkAppN found.getAppFn (arguments.set! (arguments.size - 2) inventory)
  let type := lookup.leaf.type.replace fun value =>
    if value == found then some refreshed else none
  return { lookup with inventory, leaf := { lookup.leaf with type } }

/-- A lookup proof with its exact native owner, key and inventory. Only closed
statements are retained, so discovery hypotheses cannot escape their scope. -/
structure KnownLookup where
  lookup : Lookup
  proof : Expr

/-- Retain a supplied proof only when its statement and term are closed. -/
def Lookup.remember (lookup : Lookup) (proof : Expr) : MetaM (Option KnownLookup) := do
  if lookup.leaf.type.hasFVar || lookup.leaf.type.hasMVar || lookup.leaf.type.hasSorry ||
      proof.hasFVar || proof.hasMVar || proof.hasSorry then return none
  unless (← inferType proof) == lookup.leaf.type do return none
  return some ⟨lookup, proof⟩

/-- Lift a successful exact lookup through syntactic list additions. Matching
never compares denotations or evaluates a key. Other owners, kinds, keys and
inventories need their own evidence. -/
def KnownLookup.find? (known : KnownLookup) (lookup : Lookup) : MetaM (Option Expr) := do
  unless known.lookup.request.kind == lookup.request.kind &&
      known.lookup.request.context == lookup.request.context &&
      known.lookup.key == lookup.key do return none
  unless (lookup.withInventory known.lookup.inventory).leaf.type == known.lookup.leaf.type do
    return none
  let found := lookup.leaf.type.getAppArgs[1]!.getAppArgs.back!
  let arguments := found.getAppArgs
  let parameters := arguments.extract 0 (arguments.size - 2)
  let mut inventory := lookup.inventory
  let mut additions : Array (Expr × Expr) := #[]
  while inventory != known.lookup.inventory do
    let args := inventory.getAppArgs
    unless inventory.getAppFn.isConstOf ``List.cons && args.size == 3 do return none
    additions := additions.push (args[1]!, args[2]!)
    inventory := args[2]!
  let rule := match lookup.request.kind with
    | .coefficient => ``Packing.find_cons
    | .valueSign => ``ValueSign.find_cons
    | .inverse => ``InverseFact.find_cons
  let mut proof := known.proof
  for (head, tail) in additions.reverse do
    proof := mkAppN (mkConst rule found.getAppFn.constLevels!)
      (parameters ++ #[tail, lookup.key, head, proof])
  unless (← inferType proof) == lookup.leaf.type do return none
  return some proof

/-- Consult retained exact lookup proofs before the caller's decision procedure.
Successful closed decisions are retained across passes and into reconstruction. -/
def lookupSupplier (known : IO.Ref (Array KnownLookup)) (decisions : Supplier) : Supplier :=
    fun type => do
  let leaf : Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
  let some lookup ← leaf.lookup? | return none
  let entries ← known.get
  for offset in [:entries.size] do
    let some entry := entries[entries.size - 1 - offset]? |
      throwError "retained lookup index changed"
    if let some proof ← entry.find? lookup then
      if entry.lookup.inventory != lookup.inventory then
        if let some lifted ← lookup.remember proof then known.modify (·.push lifted)
      return some proof
  let supplied ← decisions type
  if let some proof := supplied then
    if let some entry ← lookup.remember proof then known.modify (·.push entry)
  return supplied

private def retainBinding (type proof : Expr) : MetaM Expr := do
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__finiteSupportBinding)
  let levels := collectLevelParams (collectLevelParams {} type) proof |>.params.toList
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := levels, type, value := proof }) none (doCheck := true))
  return mkConst name (levels.map Lean.Level.param)

/-- Prefer an exact inventory slot across the entire table before attempting
any definitional comparison. Alias compatibility is checked only on a miss. -/
def Lookup.inventoryIndex? (lookup : Lookup) (inventories : Array Inventory) :
    MetaM (Option Nat) := lookup.leaf.withContext do
  if let some index := inventories.findIdx? (·.facts == lookup.inventory) then return some index
  for i in [:inventories.size] do
    let some inventory := inventories[i]? | throwError "finite inventory index mismatch"
    if ← withTransparency .all (isDefEq inventory.facts lookup.inventory) then return some i
  return none

/-- Record insertion requires a registered inventory. -/
def Lookup.inventoryIndex (lookup : Lookup) (inventories : Array Inventory) : MetaM Nat := do
  let some index ← lookup.inventoryIndex? inventories |
    throwError "finite lookup refers to an unregistered inventory"
  return index

private def addRecord (lookup : Lookup) (fact : Expr)
    (inventories : Array Inventory) : MetaM (Array Inventory × Option KnownLookup) := lookup.leaf.withContext do
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
  let binding ← mkEq key lookup.key
  let proof ← mkEqRefl key
  let (statement, proof) ← close binding proof
  let _ ← auditProof proof statement
  -- Only closed, unchanged keys enter the reusable lookup table. Open guards
  -- retain the existing abstraction and ordinary-kernel checking path.
  let retained ← if statement == binding && !statement.hasFVar then
      pure (some (← retainBinding statement proof))
    else do
      kernelCheck `__finiteSupportBinding statement proof
      pure none
  let equation ← mkEq fact fact
  let reflexive ← mkEqRefl fact
  let _ ← auditProof reflexive equation
  kernelCheck `__finiteSupportRecord equation reflexive
  let i ← lookup.inventoryIndex inventories
  let some inventory := inventories[i]? | throwError "finite inventory index mismatch"
  let facts ← mkAppM ``List.cons #[fact, inventory.facts]
  let known ← match retained with
    | none => pure none
    | some binding =>
      let rule := match lookup.request.kind with
        | .coefficient => ``Packing.find_head
        | .valueSign => ``ValueSign.find_head
        | .inverse => ``InverseFact.find_head
      let proof ← mkAppM rule #[inventory.facts, lookup.key, fact, binding]
      (lookup.withInventory facts).remember proof
  return (inventories.set! i ⟨facts⟩, known)

/-- An unresolved result retains all exact remaining obligations and makes no
proof claim. A complete result includes a closed ordinary-kernel theorem,
abstracting the caller's used local variables and hypotheses. -/
inductive SupportResult where
  | complete (type proof : Expr)
  | unresolved (leaves : Array Leaf)

/-- Insert one record only after checking its native owner, kind and exact
original key, and checking its binding with the ordinary kernel. -/
def Lookup.insert (lookup : Lookup) (fact : Expr) (inventories : Array Inventory) :
    MetaM (Array Inventory) := return (← addRecord lookup fact inventories).1

/-- Insert an exact record and retain the checked closed-key lookup proof.
The optional retained lookup refers to the exact inventory after insertion. -/
def Lookup.insertKnown (lookup : Lookup) (fact : Expr) (inventories : Array Inventory) :
    MetaM (Array Inventory × Option KnownLookup) := addRecord lookup fact inventories

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
      let (statement, proof) ← close statement proof
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
          let (inventories, _) ← addRecord lookup fact inventories
          return ← go n inventories (requests.push lookup.request)
    return ⟨inventories, requests, .unresolved missing⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
