/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.KernelReplay
public import HexRealClosureTheory.TransportInventory

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Inspect the retained list structure without enumerating polynomial
coefficients. Applied aliases are restricted to this module's checked support
functions; other applied inventory APIs retain their existing fallback. -/
def supportHead (value : Expr) : MetaM Expr := do
  let mut value := value
  for _ in [:64] do
    if value.getAppFn.isConstOf ``List.append || value.getAppFn.isConstOf ``List.cons ||
        value.getAppFn.isConstOf ``List.nil ||
        value.getAppFn.isConstOf ``Transport.Inventory.coefficients then return value
    if let .proj recordName index receiver := value then
      unless recordName == ``Prod && index < 2 do return value
      let constructor ← withTransparency .all (whnf receiver)
      unless constructor.getAppFn.isConstOf ``Prod.mk do return value
      value := constructor.getAppArgs[2 + index]!
      continue
    let .const name levels := value.getAppFn | return value
    if value.isApp then
      unless isPrivateName name && (name.toString.splitOn "__finiteSupport").length > 1 do
        return value
    let .defnInfo info ← getConstInfo name | return value
    value := (info.value.instantiateLevelParams info.levelParams levels).beta value.getAppArgs
  return value

private def combine (coefficient : Expr) (blocks : Array Expr) : MetaM Expr := do
  let mut blocks := blocks
  while blocks.size > 1 do
    let mut next : Array Expr := #[]
    for i in [:(blocks.size + 1) / 2] do
      let some left := blocks[2 * i]? | throwError "finite support block missing"
      let value ← if let some right := blocks[2 * i + 1]? then
          mkAppM ``List.append #[left, right]
        else pure left
      next := next.push value
    blocks := next
  if let some block := blocks[0]? then return block
  mkListLit coefficient []

private def checkedData (type value : Expr) : MetaM Expr := do
  for expression in #[type, value] do
    if expression.hasFVar || expression.hasMVar || expression.hasSorry || expression.hasLooseBVars then
      throwError "support sharing requires closed complete data"
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__finiteSupport)
  let levels := collectLevelParams (collectLevelParams {} type) value |>.params.toList
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let declaration := Declaration.defnDecl {
    name, levelParams := levels, type, value, hints := .regular 0, safety := .safe }
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  return mkConst name (levels.map Level.param)

private inductive Blocks where
  | leaf (value : Expr)
  | node (left right : Blocks)

private def shape (input : Array Expr) : MetaM Blocks := do
  let mut current := input.map Blocks.leaf
  while current.size > 1 do
    let mut next := #[]
    for i in [:(current.size + 1) / 2] do
      let some left := current[2*i]? | throwError "support tree lost its left branch"
      next := next.push (if let some right := current[2*i+1]? then .node left right else left)
    current := next
  let some result := current[0]? | throwError "support sharing requires a block"
  return result

private def tuple (leafType : Expr) : Blocks → MetaM (Expr × Expr)
  | .leaf value => pure (leafType, value)
  | .node left right => do
    let (leftType, leftValue) ← tuple leafType left
    let (rightType, rightValue) ← tuple leafType right
    let typeValue ← mkAppM ``Prod #[leftType, rightType]
    let type ← checkedData (← inferType typeValue) typeValue
    let value ← mkAppOptM ``Prod.mk
      #[some leftType, some rightType, some leftValue, some rightValue]
    return (type, value)

private def functions (carrier sourceType : Expr) :
    Blocks → Array Nat → MetaM Expr
  | .leaf _, path => do
    let value ← withLocalDeclD `source sourceType fun source => do
      let result := path.foldl (fun value index => Expr.proj ``Prod index value) source
      mkLambdaFVars #[source] result
    let result ← checkedData (← inferType value) value
    return result
  | .node left right, path => do
    let first ← functions carrier sourceType left (path.push 0)
    let second ← functions carrier sourceType right (path.push 1)
    let value ← withLocalDeclD `source sourceType fun source => do
      let result ← mkAppOptM ``List.append
        #[some carrier, some (mkApp first source), some (mkApp second source)]
      mkLambdaFVars #[source] result
    let result ← checkedData (← inferType value) value
    return result

/-- Combine finite support blocks in their original order, keeping duplicates.
Closed blocks share one checked tuple and small fold functions. Each generated
definition is checked by the ordinary kernel, and the complete resulting graph
passes the existing dependency audit before it is returned. Failed construction
rolls back declarations and their environment-scoped audit results. Open blocks
retain the same balanced append expression without creating global declarations. -/
def appendSupport (coefficient : Expr) (blocks : Array Expr) : MetaM Expr := do
  if blocks.size ≤ 1 then return ← combine coefficient blocks
  for expression in #[coefficient] ++ blocks do
    if expression.hasMVar || expression.hasSorry || expression.hasLooseBVars then
      throwError "incomplete finite support"
  if coefficient.hasFVar || blocks.any (·.hasFVar) then return ← combine coefficient blocks
  let saved ← Meta.saveState
  try
    let carrier ← checkedData (← inferType coefficient) coefficient
    let listTypeValue ← mkAppM ``List #[carrier]
    let listType ← checkedData (← inferType listTypeValue) listTypeValue
    let tree ← shape blocks
    let (type, value) ← tuple listType tree
    let data ← checkedData type value
    let function ← functions carrier type tree #[]
    let result := mkApp function data
    let _ ← auditProof result listType
    return result
  catch error =>
    saved.restore
    throw error

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
