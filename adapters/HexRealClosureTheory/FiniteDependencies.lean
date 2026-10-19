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
  /-- Closed lookup terms, including projections of checked batches and
  compositions of checked key bindings. Consumers must kernel-check the terms
  and keep the producing environment intact. -/
  known : Array KnownLookup

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

/-- Bind a reached lookup to the current version of its original inventory.
Keys and owners are unchanged; the next discovery pass checks the resulting
inventory against every requested premise. -/
private def refreshLookup (lookup : Lookup) (before after : Array Inventory) :
    MetaM (Option (Lookup × Nat)) := lookup.leaf.withContext do
  unless before.size == after.size do throwError "dependency inventory arity changed"
  let some index ← lookup.inventoryIndex? before | return none
  let some current := after[index]? | throwError "dependency current inventory missing"
  return some (lookup.withInventory current.facts, index)

/-- Prepare checked closed lookups reached by a preliminary discovery pass.
The ordinary pass still calls its original decision supplier for every request
not covered by the returned exact proofs. After an insertion, preparation also
checks the remaining lookups against the updated inventories. Preparation
consumes no record fuel; only native record insertion consumes that budget. -/
abbrev LookupPreparation := Array Leaf → MetaM (Array KnownLookup)

private def prepareKnown (known : IO.Ref (Array KnownLookup)) (prepare : LookupPreparation)
    (pending : Array Leaf) : MetaM Nat := do
  let mut allowed : ExprSet := {}
  for leaf in pending do allowed := allowed.insert (← instantiateMVars leaf.type)
  let entries ← prepare pending
  for entry in entries do
    unless allowed.contains entry.lookup.leaf.type do
      throwError "lookup preparation returned an unrequested predicate"
    let some lookup ← entry.lookup.leaf.lookup? |
      throwError "lookup preparation returned a non-lookup predicate"
    let some retained ← lookup.remember entry.proof |
      throwError "lookup preparation returned incomplete or mismatched evidence"
    known.modify (·.push retained)
  return entries.size

private def dependencyLeaves (levels : Array Level) (types : Array Expr)
    (decisions : Supplier) : MetaM (Array Leaf) := do
  let mut roots := #[]
  for type in types do
    if type.hasMVar || type.hasSorry then throwError "incomplete dependency statement"
    unless ← isProp type do throwError "dependency statement must be a proposition"
    roots := roots ++ (← frontier type dependencyBoundary decisions)
  descend (levels.size + 1) levels roots decisions

/-- Close the reached native lookup dependencies across all retained levels
before interpreting coefficients. Insert the missing records from one frontier
before rebuilding the requested premises. Only exact lookup checks can be discharged during this
pass, so supplied proofs cannot hide arithmetic inputs. The returned base
operations and guards still need the staged bootstrap and verified prefix
suppliers; this discovery pass chooses no real points and proves no theorem. -/
def collectDependencies (fuel : Nat) (initial : Array Level)
    (types : Array Level → MetaM (Array Expr)) (decisions : Supplier)
    (record : Lookup → Array Level → MetaM (Option Expr))
    (prepare : Option LookupPreparation := none) : MetaM Discovery := do
  let _ ← collectSupport 0 (levelInventories initial) (fun _ => pure (mkConst ``True))
    (fun _ => pure none) (fun _ _ => throwError "inventory validation invoked a producer")
  let known ← IO.mkRef (#[] : Array KnownLookup)
  go known fuel initial #[]
where
  go (known : IO.Ref (Array KnownLookup)) (remaining : Nat) (levels : Array Level)
      (requests : Array Request) : MetaM Discovery := do
    let required ← types levels
    let began ← IO.getNumHeartbeats
    let mut preliminary := 0
    let mut preparation := 0
    let fallbacks ← IO.mkRef (0 : Nat)
    let mut refreshedChecks := 0
    let mut insertedPreparation := 0
    if remaining > 0 then
      if let some prepare := prepare then
        let pending ← dependencyLeaves levels required (lookupSupplier known (fun _ => pure none))
        let inspected ← IO.getNumHeartbeats
        preliminary := inspected - began
        let _ ← prepareKnown known prepare pending
        preparation := (← IO.getNumHeartbeats) - inspected
    let lookupDecisions := lookupSupplier known (fun type => do
      fallbacks.modify (· + 1)
      decisions type)
    let finalBegan ← IO.getNumHeartbeats
    let leaves ← dependencyLeaves levels required lookupDecisions
    let finalCost := (← IO.getNumHeartbeats) - finalBegan
    let original := levelInventories levels
    let mut current := levels
    let mut requests := requests
    let mut budget := remaining
    let mut inserted := false
    let mut missing := false
    for position in [:leaves.size] do
      let some leaf := leaves[position]? | throwError "dependency frontier lost a leaf"
      if let some lookup ← leaf.lookup? then
        if budget == 0 then
          missing := true
          continue
        let inventories := levelInventories current
        let some (refreshed, index) ← refreshLookup lookup original inventories | do
          missing := true
          continue
        let some previousInventory := original[index]? |
          throwError "dependency original inventory missing"
        let some currentInventory := inventories[index]? |
          throwError "dependency current inventory missing"
        -- A changed slot forces a new pass. An unchanged alias remains an
        -- unresolved original statement, even if the canonical lookup is known.
        let changed := currentInventory.facts != previousInventory.facts
        if changed || refreshed.inventory != lookup.inventory then
          refreshedChecks := refreshedChecks + 1
          let pending ← refreshed.leaf.withContext do
            frontier refreshed.leaf.type dependencyBoundary lookupDecisions
          if pending.isEmpty then
            if !changed then missing := true
            continue
        let lookup := refreshed
        missing := true
        let n + 1 := budget | continue
        let some fact ← lookup.leaf.withContext (record lookup current) | continue
        let (inventories, entry) ← lookup.insertKnown fact (levelInventories current)
        if let some entry := entry then known.modify (·.push entry)
        current ← replaceInventories current inventories
        requests := requests.push lookup.request
        budget := n
        inserted := true
        if let some prepare := prepare then
          let preparing ← IO.getNumHeartbeats
          let retained := lookupSupplier known (fun _ => pure none)
          let mut pending := #[]
          let updated := levelInventories current
          for leaf in leaves.extract (position + 1) leaves.size do
            let type ← instantiateMVars leaf.type
            if type.hasFVar || type.hasMVar || type.hasSorry then continue
            if let some lookup ← ({ leaf with type } : Leaf).lookup? then
              if let some (refreshed, _) ← refreshLookup lookup original updated then
                let supplied ← refreshed.leaf.withContext (retained refreshed.leaf.type)
                if supplied.isNone then pending := pending.push refreshed.leaf
          let prepared ← if pending.isEmpty then pure 0 else prepareKnown known prepare pending
          let cost := (← IO.getNumHeartbeats) - preparing
          insertedPreparation := insertedPreparation + cost
          if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
            IO.FS.withFile path .append fun handle => do
              handle.putStrLn s!"dependency insertion: position={position} pending={pending.size} prepared={prepared} preparationHB={cost/1000}"
              handle.flush
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"dependency pass: preliminaryHB={preliminary/1000} preparationHB={preparation/1000} finalHB={finalCost/1000} insertionPreparationHB={insertedPreparation/1000} fallbacks={(← fallbacks.get)} refreshed={refreshedChecks} leaves={leaves.size} inserted={requests.size}"
        handle.flush
    if inserted then
      if _decreased : budget < remaining then return ← go known budget current requests
      throwError "dependency insertion did not consume its record budget"
    return ⟨levels, requests, leaves, !missing, ← known.get⟩
  termination_by remaining

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
