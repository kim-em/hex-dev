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

/-- Supply zero without a record, and unit from its exact retained native key.
Reached natural casts retain a constant-polynomial key and use the predecessor
cast proof. Missing keys remain ordinary finite proof obligations. -/
def Prefix.scalar (level : Prefix) (previous : Supplier) (type : Expr) :
    MetaM (Option Expr) := do
  let args := type.getAppArgs
  unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
  let .app reader value := args[1]! | return none
  unless ← withTransparency .all (isDefEq reader level.reader) do return none
  let zero ← mkAppM ``Context.finiteRead_zero
    #[level.context, level.read, level.zero, level.unit, level.descriptor]
  if ← proofMatches zero type then return some zero
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
