/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.FiniteSupport

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Distinct closed native lookup predicates. Neither a reader nor the key is
reduced, and unresolved caller metavariables are never assigned. -/
def batchCandidates (leaves : Array Leaf) : MetaM (Array Lookup) := do
  let mut seen : ExprSet := {}
  let mut result := #[]
  for leaf in leaves do
    let type ← instantiateMVars leaf.type
    if type.hasFVar || type.hasMVar || type.hasSorry || seen.contains type then continue
    let some lookup ← ({ leaf with type } : Leaf).lookup? | continue
    if lookup.inventory.getAppFn.isConstOf ``List.nil then continue
    seen := seen.insert type
    result := result.push lookup
  return result

private structure BatchNode where
  type : Expr
  proof : Expr
  paths : Array (Array Bool)

private def conjunction (types : Array Expr) : MetaM BatchNode := do
  let reflexive ← mkEqRefl (mkConst ``Bool.true)
  let mut nodes := types.map fun type => ({ type, proof := reflexive, paths := #[#[]] } : BatchNode)
  while nodes.size > 1 do
    let mut next := #[]
    for i in [: (nodes.size + 1) / 2] do
      let some left := nodes[2 * i]? | throwError "lookup conjunction lost its left node"
      if let some right := nodes[2 * i + 1]? then
        next := next.push {
          type := mkApp2 (mkConst ``And) left.type right.type
          proof := mkAppN (mkConst ``And.intro) #[left.type, right.type, left.proof, right.proof]
          paths := left.paths.map (#[false] ++ ·) ++ right.paths.map (#[true] ++ ·) }
      else next := next.push left
    nodes := next
  let some node := nodes[0]? | throwError "empty lookup conjunction"
  return node

/-- Native bits only select proposed proofs. The ordinary kernel checks every
selected original predicate together, including its owner, key, inventory and
instances. A false positive or resource failure propagates. False bits produce
no evidence; callers must retain their usual decision fallback.

The balanced conjunction shares checking work and keeps each retained
projection short. The producing environment must accompany the returned terms.
All final reconstruction guards and the joint theorem still require checking. -/
private def checkLookupChunk (lookups : Array Lookup) (accepted : Array Bool) :
    MetaM (Array KnownLookup) := do
  unless lookups.size == accepted.size do throwError "lookup batch result changed length"
  let mut selected := #[]
  for i in [:lookups.size] do
    if !accepted[i]! then continue
    let some input := lookups[i]? | throwError "lookup batch lost an input"
    let leaf := input.leaf
    let type ← instantiateMVars leaf.type
    if type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "lookup batch requires a closed predicate"
    let some lookup ← ({ leaf with type } : Leaf).lookup? |
      throwError "lookup batch requires an original native lookup"
    selected := selected.push lookup
  if selected.isEmpty then return #[]
  let node ← conjunction (selected.map (·.leaf.type))
  let _ ← auditProof node.proof node.type
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__finiteLookupBatch)
  let levels := collectLevelParams (collectLevelParams {} node.type) node.proof |>.params.toList
  let declaration := Declaration.thmDecl {
    name, levelParams := levels, type := node.type, value := node.proof }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  match (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true) with
  | .ok environment => setEnv environment
  | .error error =>
    if let .appTypeMismatch _ _ _ (.forallE _ expected _ _) _ := error then
      if let some index := selected.findIdx? (·.leaf.type == expected) then
        throwError "{error.toMessageData options}\nlookup batch predicate {index}: {expected}"
    throwKernelException error
  let batch := mkConst name (levels.map Lean.Level.param)
  let mut result := #[]
  for i in [:selected.size] do
    let mut proof := batch
    let mut type := node.type
    for right in node.paths[i]! do
      let args := type.getAppArgs
      unless type.getAppFn.isConstOf ``And && args.size == 2 do
        throwError "lookup batch projection lost its conjunction"
      proof := mkAppN (mkConst (if right then ``And.right else ``And.left))
        #[args[0]!, args[1]!, proof]
      type := args[if right then 1 else 0]!
    let closedProof ← instantiateMVars proof
    let some lookup := selected[i]? | throwError "lookup batch lost a selected predicate"
    let some retained ← lookup.remember closedProof |
      throwError "lookup batch projection changed its closed original predicate"
    result := result.push retained
  return result

/-- Bound native programs and individual kernel checks while retaining
sharing between related predicates. This is not an input-size limit. -/
def lookupBatchSize : Nat := 64

/-- Check arbitrary many lookup suggestions in bounded groups. Each accepted
predicate is checked in its complete original form; resource errors propagate. -/
def checkLookupBatch (lookups : Array Lookup) (accepted : Array Bool) :
    MetaM (Array KnownLookup) := do
  unless lookups.size == accepted.size do throwError "lookup batch result changed length"
  let mut result := #[]
  for group in [: (lookups.size + lookupBatchSize - 1) / lookupBatchSize] do
    let start := group * lookupBatchSize
    let finish := min (start + lookupBatchSize) lookups.size
    result := result ++ (← checkLookupChunk (lookups.extract start finish) (accepted.extract start finish))
  return result

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
