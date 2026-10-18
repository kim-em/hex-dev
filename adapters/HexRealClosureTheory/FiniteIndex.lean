/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteData
public import HexRealClosureTheory.TransportInventory
public meta import HexRealClosureTheory.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"coefficient lookup: {message} [heartbeats={(← IO.getNumHeartbeats) / 1000}]"
      handle.flush

private def readIndex (value : Expr) : MetaM (Option Nat) :=
  withNewMCtxDepth <| withTransparency .all do getNatValue? (← whnf value)

/-- Share the checked premise of the standard list-membership theorem.
The list getter and its dictionaries come from that theorem's type. -/
private def retainEntry (statement proof : Expr) : MetaM Expr := do
  let statement ← instantiateMVars statement
  let proof ← instantiateMVars proof
  if statement.hasFVar || proof.hasFVar then throwError "open coefficient position"
  let _ ← auditProof proof statement
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientEntry)
  let parameters := collectLevelParams (collectLevelParams {} statement) proof |>.params.toList
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let declaration := Declaration.thmDecl {
    name, levelParams := parameters, type := statement, value := proof }
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  return mkConst name (parameters.map Level.param)

/-- One reduced inventory cell, with a lazily read natural coefficient index. -/
structure CoefficientCell where
  value : Expr
  tail : Expr
  index : Option (Option Nat) := none

/-- A prefix of one exact closed inventory. No proof terms are cached. -/
structure CoefficientWalk where
  inventory : Expr
  rest : Expr
  cells : Array CoefficientCell := #[]
  complete : Bool := false

/-- Scope traversal reuse to the lifetime of one agreement supplier. -/
abbrev CoefficientCache := IO.Ref (Option CoefficientWalk)

private def findCoefficient (inventory function : Expr) (wanted : Nat)
    (cache : Option CoefficientCache) : MetaM (Option (Nat × Expr)) := do
  if let some cache := cache then
    let mut walk := match ← cache.get with
      | some previous => if previous.inventory == inventory then previous
          else { inventory, rest := inventory }
      | none => { inventory, rest := inventory }
    let mut position := 0
    while true do
      if walk.cells.size ≤ position then
        if walk.complete then
          cache.set (some walk)
          return none
        let literal ← withTransparency .all (whnf walk.rest)
        if literal.getAppFn.isConstOf ``List.nil then
          cache.set (some { walk with complete := true })
          return none
        unless literal.getAppFn.isConstOf ``List.cons do
          throwError "coefficient lookup requires a literal finite inventory"
        let args := literal.getAppArgs
        let cell : CoefficientCell := ⟨args[1]!, literal, none⟩
        walk := { walk with rest := args[2]!, cells := walk.cells.push cell }
      let some cell := walk.cells[position]? | throwError "coefficient walk lost its position"
      let value := cell.value
      if value.isApp && value.appFn! == function then
        let index ← match cell.index with
          | some index => pure index
          | none => readIndex value.appArg!
        walk := { walk with cells := walk.cells.set! position { cell with index := some index } }
        if index == some wanted then
          cache.set (some walk)
          return some (position, value)
      position := position + 1
    return none
  let mut rest := inventory
  let mut position := 0
  while true do
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then return none
    unless literal.getAppFn.isConstOf ``List.cons do
      throwError "coefficient lookup requires a literal finite inventory"
    let args := literal.getAppArgs
    let value := args[1]!
    if value.isApp && value.appFn! == function then
      if (← readIndex value.appArg!) == some wanted then return some (position, value)
    position := position + 1
    rest := args[2]!
  return none

/-- A literal suffix and the kernel-checked equation relating it to the exact
original inventory. Its proof constant lives in the producing environment. -/
private structure Suffix where
  start : Nat
  tail : Expr
  equality : Expr

/-- Retain checked suffixes in the same environment branch as their constants.
An earlier request keeps later suffixes available for subsequent requests. -/
private initialize suffixes : EnvExtension (PHashMap Expr (Array Suffix)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def suffixMember (inventory : Expr) (position : Nat) (value : Expr)
    (cache : Option CoefficientCache) : MetaM Expr := do
  let inventory ← instantiateMVars inventory
  let value ← instantiateMVars value
  if inventory.hasFVar || inventory.hasMVar || value.hasFVar || value.hasMVar then
    throwError "coefficient suffix requires a closed inventory and value"
  let saved := suffixes.getState (← getEnv) |>.find? inventory |>.getD #[]
  let mut chosen : Option Suffix := none
  for entry in saved do
    if entry.start ≤ position && chosen.all (fun previous => previous.start < entry.start) then
      chosen := some entry
  let suffix ← match chosen with
    | some entry => pure entry
    | none => create inventory
  diagnostic s!"using checked suffix {suffix.start}, relative position {position - suffix.start}"
  let membership ← mkAppOptM ``List.mem_of_getElem?
    #[none, some suffix.tail, some (toExpr (position - suffix.start)), some value]
  let .forallE _ premise _ _ ← whnf (← inferType membership) |
    throwError "suffix membership lost its checked position"
  unless premise.getAppFn.isConstOf ``Eq && premise.getAppArgs.size == 3 &&
      premise.getAppArgs.back!.getAppFn.isConstOf ``Option.some do
    throwError "coefficient membership has an unexpected suffix-position premise"
  let began ← IO.getNumHeartbeats
  let entry ← retainEntry premise (← mkEqRefl premise.getAppArgs.back!)
  diagnostic s!"relative suffix position kernel checked: absolute={position} start={suffix.start} offset={position - suffix.start} checkHB={((← IO.getNumHeartbeats) - began) / 1000}"
  let member := mkApp membership entry
  let predicate ← withLocalDeclD `list (← inferType inventory) fun list => do
    let type ← mkAppM ``List.Mem #[value, list]
    mkLambdaFVars #[list] type
  let congruence ← mkAppM ``congrArg #[predicate, suffix.equality]
  let dropped ← mkAppM ``Eq.mpr #[congruence, member]
  mkAppM ``List.mem_of_mem_drop #[dropped]
where
  create (inventory : Expr) : MetaM Suffix := do
    let dropped ← mkAppM ``List.drop #[toExpr position, inventory]
    let tail ← if let some cache := cache then do
        let some walk ← cache.get | throwError "suffix lookup lost its inventory walk"
        unless walk.inventory == inventory do throwError "suffix lookup changed its inventory"
        let some cell := walk.cells[position]? | throwError "suffix lookup lost its literal position"
        pure cell.tail
      else withTransparency .all (whnf dropped)
    unless tail.getAppFn.isConstOf ``List.cons do
      throwError "coefficient suffix requires an actual nonempty position"
    let began ← IO.getNumHeartbeats
    let equality ← retainEntry (← mkEq dropped tail) (← mkEqRefl tail)
    diagnostic s!"suffix equation kernel checked at {position}, checkHB={((← IO.getNumHeartbeats) - began) / 1000}"
    let entry : Suffix := ⟨position, tail, equality⟩
    modifyEnv fun environment => suffixes.modifyState environment fun state =>
      state.insert inventory ((state.find? inventory).getD #[] |>.push entry)
    diagnostic s!"checked suffix retained at {position}"
    return entry

/-- Project a retained coefficient's domain proof using its original coefficient
function and natural index. The selected list position is checked by the kernel;
congruence accounts for the index expression. The complete requested predicate
is retained. Open inventories and missing keys supply no proof. -/
private def coefficientSupplier (agreement : Expr) (cache : Option CoefficientCache) : Supplier :=
    fun type => withNewMCtxDepth do
  let agreement ← instantiateMVars agreement
  let type ← instantiateMVars type
  if agreement.hasMVar || type.hasMVar || agreement.hasSorry || type.hasSorry then return none
  let agreementType ← inferType agreement
  unless agreementType.getAppFn.isConstOf ``Transport.Inventory.Agreement do return none
  let parameters := agreementType.getAppArgs
  let inventory := parameters.back!
  if inventory.hasFVar || inventory.hasMVar then return none
  let domain := parameters[parameters.size - 4]!
  let .app requestedDomain wanted := type | return none
  unless requestedDomain == domain && wanted.getAppFn.isConstOf ``DensePoly.coeff do
    return none
  let function := wanted.appFn!
  let wantedIndex := wanted.appArg!
  let some wantedNat ← readIndex wantedIndex | return none
  let some (position, value) ← findCoefficient inventory function wantedNat cache | return none
  let valueIndex := value.appArg!
  diagnostic s!"original coefficient matched at position {position}"
  let member ← suffixMember inventory position value cache
  diagnostic "actual suffix position checked; original inventory membership constructed"
  let retained ← mkAppM ``And.left #[mkApp2 agreement value member]
  let indexEq ← withTransparency .all do
    mkAppOptM ``id #[some (← mkEq valueIndex wantedIndex),
      some (← mkEqRefl valueIndex)]
  let coefficientEq ← mkAppM ``congrArg #[function, indexEq]
  let predicateEq ← mkAppM ``congrArg #[domain, coefficientEq]
  let proof ← instantiateMVars (← mkAppM ``Eq.mp #[predicateEq, retained])
  let obtained ← instantiateMVars (← inferType proof)
  unless obtained == type do return none
  if proof.hasMVar || proof.hasSorry then return none
  diagnostic "complete original guarded proposition retained"
  return some proof

/-- Project the complete original coefficient predicate without traversal reuse. -/
def lookupCoefficient (agreement : Expr) : Supplier := coefficientSupplier agreement none

/-- Reuse only the walk of an exact closed inventory. Every successful request
still checks its actual list position, index equality and complete predicate. -/
def lookupCoefficientCached (agreement : Expr) (cache : CoefficientCache) : Supplier :=
  coefficientSupplier agreement (some cache)

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
