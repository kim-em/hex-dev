/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteOperands
public meta import HexRealClosureTheory.FiniteOperands
public import HexRealClosureTheory.FiniteSupport
public meta import HexRealClosureTheory.FiniteSupport

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- The native owner and inventories of one level, with local reader variables
for dependency discovery. No point or interpretation proof has been chosen. -/
structure Level where
  context : Expr
  entries : Expr
  records : Expr
  facts : Expr
  read : Expr
  reader : Expr

private def Level.usesReader (level : Level) (reader : Expr) : MetaM Bool :=
  withTransparency .all (isDefEq reader level.reader)

private def Level.operations (level : Level) (type : Expr) : MetaM (Option (Array Expr)) := do
  let args := type.getAppArgs
  for (target, premise, count) in #[
      (``Transport.Sum, ``Packing.SumData, 2),
      (``Transport.Product, ``Packing.ProductData, 2),
      (``Transport.Difference, ``Packing.DifferenceData, 2),
      (``Transport.Scaling, ``Packing.ScalingData, 2),
      (``Transport.Differentiation, ``Packing.DifferentiationData, 1),
      (``Transport.Evaluation, ``Packing.EvaluationData, 2),
      (``Transport.PowerData, ``Packing.PowerData, 2)] do
    if type.getAppFn.isConstOf target then
      unless args.size ≥ count + 1 do throwError "invalid dependency operation"
      unless ← level.usesReader args[args.size - count - 1]! do return none
      let operands := args.extract (args.size - count) args.size
      return some #[← mkAppM premise (#[level.entries, level.read] ++ operands)]
  return none

private def Level.replays (level : Level) (type : Expr) : MetaM (Option (Array Expr)) := do
  let args := type.getAppArgs
  for (target, premise, count) in #[
      (``Transport.Finite.DescriptorData, ``Packing.DescriptorData, 2),
      (``Transport.Finite.ReplayData, ``Packing.ReplayData, 5),
      (``Transport.Finite.NodeData, ``Packing.NodeData, 5)] do
    if type.getAppFn.isConstOf target then
      unless args.size ≥ count + 3 do throwError "invalid dependency replay"
      unless ← level.usesReader args[args.size - count - 3]! do return none
      let operands := args.extract (args.size - count) args.size
      return some #[← mkAppM premise (#[level.entries, level.records, level.read] ++ operands)]
  return none

private def Level.key (level : Level) (p : Expr) : MetaM Expr := do
  let found ← mkAppM ``Packing.find #[level.entries, p]
  mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)

private def Level.scalars (level : Level) (type : Expr) : MetaM (Option (Array Expr)) := do
  let args := type.getAppArgs
  unless type.getAppFn.isConstOf ``Eq && args.size == 3 do return none
  let .app reader value := args[1]! | return none
  unless ← level.usesReader reader do return none
  let contextType ← withTransparency .all (whnf (← inferType level.context))
  let parameters := contextType.getAppArgs
  let levels := contextType.getAppFn.constLevels!
  let nativeZero := mkAppN (mkConst ``Element.zero levels) (parameters.push level.context)
  let coefficientOne := mkAppN (mkConst ``One.one [levels[0]!])
    #[parameters[0]!, parameters[4]!]
  let constantOne := mkAppN (mkConst ``DensePoly.C [levels[0]!])
    #[parameters[0]!, parameters[2]!, parameters[3]!, coefficientOne]
  let nativeUnit := mkAppN (mkConst ``Element.ofPoly levels)
    (parameters.push level.context |>.push constantOne)
  let realZero ← mkAppOptM ``Zero.zero #[some (mkConst ``Real), none]
  let realUnit ← mkAppOptM ``One.one #[some (mkConst ``Real), none]
  if value == nativeZero && (← isDefEq args[2]! realZero) then return some #[]
  if value == nativeUnit && (← isDefEq args[2]! realUnit) then
    return some #[← level.key constantOne]
  if (← withTransparency .all (isDefEq value nativeZero)) &&
      (← withTransparency .all (isDefEq args[2]! realZero)) then return some #[]
  let .forallE _ predecessor _ _ ← whnf (← inferType level.read) |
    throwError "invalid predecessor dependency reader"
  if (← withTransparency .all (isDefEq value nativeUnit)) &&
      (← withTransparency .all (isDefEq args[2]! realUnit)) then
    let unit ← mkAppOptM ``One.one #[some predecessor, none]
    return some #[← level.key (← mkAppM ``DensePoly.C #[unit])]
  let cast := value.getAppArgs
  let n? := if value.getAppFn.isConstOf ``Nat.cast ||
      value.getAppFn.isConstOf ``NatCast.natCast then cast.back?
    else if value.getAppFn.isConstOf ``OfNat.ofNat then cast[1]?
    else none
  let some n := n? | return none
  unless ← isDefEq (← inferType n) (mkConst ``Nat) do return none
  let native ← mkAppOptM ``Nat.cast #[some predecessor, none, some n]
  let real ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some n]
  unless ← withTransparency .all (isDefEq args[2]! real) do return none
  return some #[← level.key (← mkAppM ``DensePoly.C #[native]),
    ← mkEq (mkApp level.read native) real]

/-- Lower a reached operation, replay or scalar law to its exact predecessor
premises. The result is dependency data only: it asserts no arithmetic or
sign equation for either local reader and supplies no proof. -/
def Level.lower (level : Level) (leaf : Leaf) : MetaM (Option (Array Expr)) := leaf.withContext do
  if let some result ← level.operations leaf.type then return some result
  if let some result ← level.replays leaf.type then return some result
  if leaf.type.getAppFn.isConstOf ``Transport.Leading then
    let args := leaf.type.getAppArgs
    if ← level.usesReader args[args.size - 2]! then
      return some #[← mkAppM ``ValueSign.LeadingData #[level.records, args.back!]]
  level.scalars leaf.type

/-- Stop at real scalar equations and operation/replay boundaries before
the original operands disappear. Container equalities remain available to
structural traversal. Lookups and guards retain their original hypotheses. -/
def dependencyBoundary (type : Expr) : MetaM Bool := do
  if type.getAppFn.isConstOf ``Eq && type.getAppArgs.size == 3 &&
      type.getAppArgs[0]!.isConstOf ``Real then return true
  return #[``Transport.Sum, ``Transport.Product, ``Transport.Difference,
    ``Transport.Scaling, ``Transport.Differentiation, ``Transport.Evaluation,
    ``Transport.Leading, ``Transport.PowerData,
    ``Transport.Finite.DescriptorData, ``Transport.Finite.ReplayData,
    ``Transport.Finite.NodeData].any (fun name => type.getAppFn.isConstOf name)

/-- Follow predecessor dependencies without choosing any interpretation.
Each returned leaf retains its own local hypotheses. Exact lookup decisions
may discharge existing records; remaining lookups, base operations and unknown
guards are returned for support collection. Fuel limits lowering depth and
cannot turn an unresolved obligation into a proof. -/
def descend (fuel : Nat) (levels : Array Level) (roots : Array Leaf)
    (decisions : Supplier := fun _ => pure none) : MetaM (Array Leaf) := do
  let mut result := #[]
  for leaf in roots do result := result ++ (← go fuel leaf)
  return result
where
  go (remaining : Nat) (leaf : Leaf) : MetaM (Array Leaf) := leaf.withContext do
    for level in levels do
      if let some required ← level.lower leaf then
        if required.isEmpty then return #[]
        let n + 1 := remaining | throwError "finite dependency lowering exhausted its depth bound"
        let mut result := #[]
        for type in required do
          let children ← frontier type dependencyBoundary decisions
          for child in children do result := result ++ (← go n child)
        return result
    return #[leaf]

/-- Dependency discovery retains the updated native records and every
remaining base operation or guard. Saturation means only that no missing
lookup remains; it is not a proof of realization or arithmetic agreement. -/
structure Discovery where
  levels : Array Level
  requests : Array Request
  leaves : Array Leaf
  saturated : Bool

private def levelInventories (levels : Array Level) : Array Inventory :=
  levels.flatMap (fun level => #[⟨level.entries⟩, ⟨level.records⟩, ⟨level.facts⟩])

private def replaceInventories (levels : Array Level) (inventories : Array Inventory) :
    MetaM (Array Level) := do
  unless inventories.size == 3 * levels.size do throwError "dependency inventory arity changed"
  let mut result := #[]
  for i in [:levels.size] do
    let some level := levels[i]? | throwError "dependency level index changed"
    let some entries := inventories[3 * i]? | throwError "dependency packing inventory missing"
    let some records := inventories[3 * i + 1]? | throwError "dependency sign inventory missing"
    let some facts := inventories[3 * i + 2]? | throwError "dependency inverse inventory missing"
    result := result.push { level with
      entries := entries.facts, records := records.facts, facts := facts.facts }
  return result

/-- Close the reached native lookup dependencies across all retained levels
before interpreting coefficients. Rebuild the requested premises after each
checked insertion. Only exact lookup checks can be discharged during this
pass, so supplied proofs cannot hide arithmetic inputs. The returned base
operations and guards still need the staged bootstrap and verified prefix
suppliers; this discovery pass chooses no real points and proves no theorem. -/
def collectDependencies (fuel : Nat) (initial : Array Level)
    (types : Array Level → MetaM (Array Expr)) (decisions : Supplier)
    (record : Lookup → Array Level → MetaM (Option Expr)) : MetaM Discovery := do
  let _ ← collectSupport 0 (levelInventories initial) (fun _ => pure (mkConst ``True))
    (fun _ => pure none) (fun _ _ => throwError "inventory validation invoked a producer")
  go fuel initial #[]
where
  go (remaining : Nat) (levels : Array Level) (requests : Array Request) : MetaM Discovery := do
    let lookupDecisions : Supplier := fun type => do
      let leaf : Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
      if (← leaf.lookup?).isSome then decisions type else pure none
    let mut roots := #[]
    for type in ← types levels do
      if type.hasMVar || type.hasSorry then throwError "incomplete dependency statement"
      unless ← isProp type do throwError "dependency statement must be a proposition"
      roots := roots ++ (← frontier type dependencyBoundary lookupDecisions)
    let leaves ← descend (levels.size + 1) levels roots lookupDecisions
    for leaf in leaves do
      if let some lookup ← leaf.lookup? then
        let n + 1 := remaining | return ⟨levels, requests, leaves, false⟩
        let some fact ← leaf.withContext (record lookup levels) |
          return ⟨levels, requests, leaves, false⟩
        let inventories ← lookup.insert fact (levelInventories levels)
        let levels ← replaceInventories levels inventories
        return ← go n levels (requests.push lookup.request)
    return ⟨levels, requests, leaves, true⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
