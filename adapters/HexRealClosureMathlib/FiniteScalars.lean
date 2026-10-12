/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteLift
public meta import HexRealClosureMathlib.FiniteLift

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

private def proofMatches (proof type : Expr) : MetaM Bool := do
  withTransparency .all (isDefEq (← inferType proof) type)

private def inventory (entries data : Expr) (fields : Array Name) (type : Expr) :
    MetaM (Option Expr) := do
  let mut rest := entries
  let mut earlier : Array Expr := #[]
  while true do
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then return none
    unless literal.getAppFn.isConstOf ``List.cons do
      throwError "finite prefix requires literal record inventories"
    let args := literal.getAppArgs
    let value := args[1]!
    rest := args[2]!
    let mut member ← mkAppOptM ``List.mem_cons_self #[some args[0]!, some value, some rest]
    for head in earlier.reverse do member ← mkAppM ``List.mem_cons_of_mem #[head, member]
    let retained := mkApp2 data value member
    for field in fields do
      let proof ← mkAppM field #[retained]
      let obtained ← inferType proof
      if obtained.getAppFn == type.getAppFn &&
          (← withTransparency .all (isDefEq obtained type)) then return some proof
    earlier := earlier.push value
  return none

/-- Supply zero without a record, and unit from its exact retained native key.
Reached natural casts retain a constant-polynomial key and use the predecessor
cast proof. Missing keys remain ordinary finite proof obligations. -/
def Prefix.scalar (level : Prefix) (previous : Supplier) (type : Expr) :
    MetaM (Option Expr) := do
  let args := type.getAppArgs
  unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
  let .app reader value := args[1]! | return none
  if reader != level.reader && reader == level.read then return none
  unless ← withTransparency .all (isDefEq reader level.reader) do return none
  let realZero ← mkAppOptM ``Zero.zero #[some (mkConst ``Real), none]
  if ← withTransparency .all (isDefEq args[2]! realZero) then
    let zero ← mkAppM ``Context.finiteRead_zero
      #[level.context, level.read, level.zero, level.unit, level.descriptor]
    if ← proofMatches zero type then return some zero
  let realUnit ← mkAppOptM ``One.one #[some (mkConst ``Real), none]
  if ← withTransparency .all (isDefEq args[2]! realUnit) then
    let unit ← mkAppM ``Context.finiteRead_one
      #[level.context, level.read, level.zero, level.unit, level.descriptor,
        level.entries, level.packings]
    let unitType ← inferType unit
    let .forallE _ key _ _ := unitType | throwError "invalid finite unit premise"
    let unitResult ← forallTelescopeReducing unitType fun _ result => pure result
    if ← withTransparency .all (isDefEq unitResult type) then
      return some (mkApp unit (← build key previous))
  let arguments := value.getAppArgs
  let n ← if value.getAppFn.isConstOf ``Nat.cast ||
      value.getAppFn.isConstOf ``NatCast.natCast then
      pure arguments.back!
    else if value.getAppFn.isConstOf ``OfNat.ofNat && arguments.size ≥ 2 then
      pure arguments[1]!
    else return none
  unless ← isDefEq (← inferType n) (mkConst ``Nat) do return none
  let .forallE _ source _ _ ← whnf (← inferType level.read) |
    throwError "invalid finite predecessor reader"
  let sourceCast ← mkAppOptM ``Nat.cast #[some source, none, some n]
  let targetCast ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some n]
  let castType ← mkEq (mkApp level.read sourceCast) targetCast
  let cast ← build castType previous
  let castLemma ← mkAppM ``Context.finiteRead_natCast
    #[level.context, level.read, level.zero, level.unit, level.descriptor,
      level.entries, level.packings, n, cast]
  let .forallE _ key _ _ ← inferType castLemma | throwError "invalid finite cast premise"
  let proof := mkApp castLemma (← build key previous)
  unless ← proofMatches proof type do return none
  return some proof

/-- Compose scalar, reached arithmetic and replay laws at the same retained
point. This supplier can be the predecessor of the next verified level. -/
def Prefix.supplyAll (level : Prefix) (previous : Supplier) : Supplier := fun type => do
  -- The prefix's own descriptor was already proved at its predecessor reader.
  -- Reuse that exact premise when a discovered guard requests it again.
  let args := type.getAppArgs
  if type.getAppFn.isConstOf ``Transport.Finite.DescriptorData && args.size ≥ 5 &&
      args[args.size - 5]! == level.read then
    let retained ← inferType level.descriptor
    if ← withTransparency .all (isDefEq retained type) then
      return some level.descriptor
  let count := if type.getAppFn.isConstOf ``Transport.Finite.ReplayData then 8
    else if type.getAppFn.isConstOf ``Transport.Difference ||
        type.getAppFn.isConstOf ``Transport.Product then 3
    else 0
  if count > 0 && args.size ≥ count && args[args.size - count]! == level.read then
    if let some proof ← inventory level.entries level.packings
        #[``Packing.Data.replay, ``Packing.Data.difference] type then return some proof
    if let some proof ← inventory level.records level.signs
        #[``ValueSign.Data.replay] type then return some proof
    let inverses ← mkAppM ``Packing.Inventory.Data.inverses #[level.data]
    if let some proof ← inventory level.facts inverses
        #[``Packing.Inverse.Data.packing, ``Packing.Inverse.Data.original,
          ``Packing.Inverse.Data.inverse, ``Packing.Inverse.Data.product,
          ``Packing.Inverse.Data.difference] type then return some proof
  if let some proof ← level.scalar previous type then return some proof
  level.supply previous type

/-- Construct a successor's actual finite data with the current supplier,
then retain its one selected point and reader. The supplied inventories must
already cover every reached key: this operation does not add records after
the predecessor point was chosen. Iteration composes the predecessor supplier
with `supplyAll`, without installing field laws on native expressions. -/
def Prefix.extend (level : Prefix) (previous : Supplier)
    (next entries records facts : Expr) : MetaM Prefix := do
  let zero ← mkAppM ``Context.finiteRead_zero
    #[level.context, level.read, level.zero, level.unit, level.descriptor]
  let unitLemma ← mkAppM ``Context.finiteRead_one
    #[level.context, level.read, level.zero, level.unit, level.descriptor,
      level.entries, level.packings]
  let .forallE _ key _ _ ← inferType unitLemma | throwError "invalid finite unit premise"
  let unit := mkApp unitLemma (← build key previous)
  let required ← mkAppM ``Packing.Inventory.Data
    #[next, entries, records, facts, level.reader]
  let data ← build required (level.supplyAll previous)
  Prefix.ofData data zero unit

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
