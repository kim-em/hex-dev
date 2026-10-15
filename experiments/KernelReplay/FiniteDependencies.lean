/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteDependencies
public meta import HexRealClosureTheory.FiniteDependencies
public meta import HexRealClosureTheory.NativeBatch
public import KernelReplay.FiniteJoint
public meta import KernelReplay.FiniteData
import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all KernelReplay.FiniteData
import all HexRealClosureTheory.PackingArithmetic
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Codec.Coefficients
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all KernelReplay.FiniteTowerProbe

private def delayedNat : Nat → Nat
  | 0 => 0
  | n + 1 => delayedNat n + 1

private def deferred (n : Nat) : Prop :=
  if delayedNat n == n then True else False

@[instance_reducible] private def cacheZero : Zero Rat := inferInstance

private def inventoryAlias (entries : List (Hex.RealClosure.Algebraic.Packing
    Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.first)) := entries

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe
open Lean Meta Elab Command

private def retain (name : Name) (type proof : Expr) : MetaM Unit := do
  let binders := (← getLCtx).getFVarIds.map mkFVar
  let type ← mkForallFVars binders type
  let proof ← mkLambdaFVars binders proof
  kernelCheck name type proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe ++ name,
    levelParams := [], type, value := proof })

private unsafe def checkRefreshed (initial : FiniteData.Level) : MetaM Unit := do
  let wrappedRequests (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
    let some current := levels[0]? | throwError "refreshed preparation lost its level"
    let mut key ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
    let keyType ← inferType key
    let mut required := #[]
    for _ in [:9] do
      key ← mkAppOptM ``id #[some keyType, some key]
      let found ← mkAppM ``Packing.find #[current.entries, key]
      required := required.push (← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true))
    return required
  let onlyEmpty : FiniteData.Supplier := fun type => do
    let leaf : FiniteData.Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
    if let some lookup ← leaf.lookup? then
      unless lookup.inventory.getAppFn.isConstOf ``List.nil do
        throwError "refreshed lookup bypassed preparation and reached the per-request decider"
    return none
  let refreshed ← FiniteData.collectDependencies 1 #[initial] wrappedRequests onlyEmpty
    (fun lookup _ => do return some (← FiniteTowerPackets.packing lookup.request.polynomial))
    (some FiniteData.NativeBatch.prepare)
  unless refreshed.saturated && refreshed.requests.size == 1 && refreshed.known.size == 9 do
    throwError "post-insertion preparation lost a normalized key or consumed additional record fuel"
  for entry in refreshed.known do
    kernelCheck `__refreshedPreparedLookup entry.lookup.leaf.type entry.proof

syntax (name := finiteDependenciesProbe) "#finite_dependencies_probe" : command
@[command_elab finiteDependenciesProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let deferredType := mkApp (mkConst ``deferred) (toExpr (1024 : Nat))
  let stopped ← withOptions (fun options => maxRecDepth.set options 256) do
    FiniteData.frontier deferredType (fun type => pure (type.getAppFn.isConstOf ``deferred))
  let [leaf] := stopped.toList |
    throwError "dependency discovery did not retain one stopped native predicate"
  unless leaf.type == deferredType do
    throwError "dependency discovery evaluated a stopped native predicate"
  let owner := mkConst ``FiniteTower.first
  let readType ← mkArrow (mkConst ``Rat) (mkConst ``Real)
  let source ← mkAppM ``Element #[owner]
  let readerType ← mkArrow source (mkConst ``Real)
  withLocalDeclD `read readType fun read =>
    withLocalDeclD `reader readerType fun reader => do
      let level : FiniteData.Level := {
        context := owner
        entries := mkConst ``FiniteTowerProbe.nestedEntries
        records := mkConst ``FiniteTowerProbe.nestedSigns
        facts := ← mkListLit (← mkAppM ``InverseFact #[owner]) []
        read := read
        reader := reader }
      let nativeUnit ← mkAppOptM ``One.one #[some source, none]
      let realUnit ← mkAppOptM ``One.one #[some (mkConst ``Real), none]
      let nativePair ← mkAppM ``Prod.mk #[mkApp reader nativeUnit, mkApp reader nativeUnit]
      let realPair ← mkAppM ``Prod.mk #[realUnit, realUnit]
      let container ← mkEq (← mkAppM ``Option.some #[nativePair])
        (← mkAppM ``Option.some #[realPair])
      let containerLeaves ← FiniteData.frontier container FiniteData.dependencyBoundary
      unless !containerLeaves.isEmpty do
        throwError "container scalar discovery lost its reached equations"
      for leaf in containerLeaves do
        unless leaf.type.getAppFn.isConstOf ``Eq &&
            leaf.type.getAppArgs[0]!.isConstOf ``Real do
          throwError "container scalar discovery stopped before its real-reader equations"
        let some lowered ← level.lower leaf |
          throwError "container scalar discovery missed its demanded unit packing"
        unless lowered.size == 1 do
          throwError "container scalar discovery lost its exact unit key"
      let product ← mkAppM ``Transport.Product
        #[reader, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
      let frontier ← FiniteData.frontier product FiniteData.dependencyBoundary
      unless frontier.size == 1 do throwError "dependency boundary expanded the upper operation"
      let some leaf := frontier[0]? | throwError "dependency boundary lost the operation"
      let some required ← level.lower leaf | throwError "upper operation was not lowered"
      unless required.size == 1 do throwError "product dependency has the wrong arity"
      let expected ← mkAppM ``Packing.ProductData
        #[level.entries, read, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
      let statement ← mkEq required[0]! expected
      retain `productLowering statement (← mkEqRefl required[0]!)
      let decisions : FiniteData.Supplier := fun type => do
        let args := type.getAppArgs
        if type.getAppFn.isConstOf ``Eq && args.size == 3 && args[0]!.isConstOf ``Bool then
          FiniteDataProbe.supply type
        else pure none
      let predecessor ← FiniteData.frontier required[0]! FiniteData.dependencyBoundary decisions
      unless predecessor.size == 2 do throwError "predecessor product lost its product or accumulator sum"
      for operation in predecessor do
        let some coefficients ← operation.coefficients? |
          throwError "predecessor operation lost its original coefficient support"
        unless !coefficients.hasFVar do throwError "coefficient support depends on an unchosen reader"
      let descended ← FiniteData.descend 1 #[level] frontier decisions
      unless descended.size == 2 do throwError "recursive lowering lost a predecessor operation"
      let some productLeaf := descended[0]? | throwError "recursive lowering lost its product"
      let some coefficients ← productLeaf.coefficients? | throwError "recursive lowering lost its inputs"
      let expectedInputs ← mkListLit (mkConst ``Rat) [toExpr (1 : Rat), toExpr (2 : Rat)]
      retain `productInputs (← mkEq coefficients expectedInputs) (← mkEqRefl coefficients)
      try
        let _ ← FiniteData.descend 0 #[level] frontier decisions
        throwError "dependency lowering ignored its depth bound"
      catch error =>
        unless (← error.toMessageData.toString).startsWith "finite dependency lowering exhausted" do
          throw error
      withLocalDeclD `other readerType fun other => do
        let type ← mkAppM ``Transport.Product
          #[other, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
        let leaf : FiniteData.Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
        unless (← level.lower leaf).isNone do
          throwError "dependency lowering used a different reader of the same type"
      let raw := mkConst ``FiniteTower.nextRaw
      let evidence ← mkAppM ``Hex.SignDet.Replay.leaf #[mkConst ``FiniteDataProbe.decodedNode]
      let original := mkConst ``FiniteTowerProbe.nestedRoot
      kernelCheck `__finiteDependencyRaw
        (← mkEq (← mkAppM ``Hex.SignDet.Descriptor.raw #[original]) raw)
        (mkConst ``FiniteTowerProbe.nestedRoot_raw)
      kernelCheck `__finiteDependencyReplay
        (← mkEq (← mkAppM ``Hex.SignDet.Descriptor.evidence #[original]) evidence)
        (mkConst ``FiniteWitness.root_evidence)
      let sourceSign ← Elab.Term.elabTerm (← `(Element.sign (context := FiniteTower.first))) none
      let targetSign ← Elab.Term.elabTerm (← `(fun x : ℝ => (SignType.sign x : Int))) none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let descriptor ← mkAppM ``Transport.Finite.DescriptorData
        #[reader, ← instantiateMVars sourceSign, ← instantiateMVars targetSign, raw, evidence]
      let descriptorLeaves ← FiniteData.frontier descriptor FiniteData.dependencyBoundary
      unless descriptorLeaves.size == 1 do throwError "descriptor boundary lost its literal replay"
      let lowerDescriptor ← FiniteData.descend 1 #[level] descriptorLeaves decisions
      let mut arithmetic := 0
      for leaf in lowerDescriptor do
        unless (← leaf.lookup?).isNone do throwError "descriptor lowering lost a retained key"
        if let some inputs ← leaf.coefficients? then
          unless ← isDefEq (← inferType inputs) (← mkAppM ``List #[mkConst ``Rat]) do
            throwError "descriptor lowering retained an algebraic coefficient operation"
          arithmetic := arithmetic + 1
      unless arithmetic > 0 do throwError "descriptor lowering lost its predecessor arithmetic"
      let noEntries ← mkListLit (← mkAppM ``Packing #[owner]) []
      let empty := { level with entries := noEntries }
      let requested (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
        let some current := levels[0]? | throwError "dependency discovery lost its level"
        return #[← mkAppM ``Transport.Product
          #[current.reader, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]]
      let absent ← FiniteData.collectDependencies 0 #[empty] requested decisions
        (fun _ _ => throwError "zero-fuel dependency discovery invoked a producer")
      unless !absent.saturated && absent.requests.isEmpty do
        throwError "dependency discovery accepted missing records"
      -- With no insertion budget, an unavailable inventory remains unresolved.
      -- Inspecting the frontier must not attempt to produce or register it.
      let foreignKey ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
      let foreignFound ← mkAppM ``Packing.find #[level.entries, foreignKey]
      let foreignRequest ← mkEq (← mkAppM ``Option.isSome #[foreignFound])
        (mkConst ``Bool.true)
      let foreign ← FiniteData.collectDependencies 0 #[empty]
        (fun _ => pure #[foreignRequest]) (fun _ => pure none)
        (fun _ _ => throwError "zero-fuel foreign lookup invoked a producer")
      unless !foreign.saturated && foreign.requests.isEmpty do
        throwError "zero-fuel foreign lookup lost its unresolved obligation"
      let wrongPolynomial ← mkAppM ``DensePoly.C #[toExpr (3 : Rat)]
      let wrong ← FiniteTowerPackets.packing wrongPolynomial
      try
        let _ ← FiniteData.collectDependencies 1 #[empty] requested decisions
          (fun _ _ => pure (some wrong))
        throwError "dependency collector accepted a different original key"
      catch error =>
        unless (← error.toMessageData.toString).startsWith "finite support record binds a different key" do
          throw error
      let collected ← FiniteData.collectDependencies 1 #[empty] requested decisions
        (fun lookup _ => do
          unless lookup.request.kind == .coefficient do
            throwError "product dependency requested a different record kind"
          return some (← FiniteTowerPackets.packing lookup.request.polynomial))
      unless collected.saturated && collected.requests.size == 1 do
        throwError "dependency record insertion did not reach a fixed point"
      unless collected.leaves.size == 2 do
        throwError "dependency record insertion assumed predecessor arithmetic"
      let cached ← FiniteData.collectDependencies 0 collected.levels requested decisions
        (fun _ _ => throwError "cached dependency discovery invoked a producer")
      unless cached.saturated && cached.requests.isEmpty do
        throwError "cached dependency discovery did not replay"
      let some retained := collected.known[0]? | throwError "preparation control lost its checked lookup"
      let exact := retained.lookup.leaf.type
      let fallbackCalls ← IO.mkRef (0 : Nat)
      let fallback : FiniteData.Supplier := fun type => do
        fallbackCalls.modify (· + 1)
        FiniteDataProbe.supply type
      let prepared ← FiniteData.collectDependencies 1 collected.levels (fun _ => pure #[exact]) fallback
        (fun _ _ => throwError "prepared lookup invoked a record producer")
        (some FiniteData.NativeBatch.prepare)
      unless prepared.saturated && prepared.requests.isEmpty && (← fallbackCalls.get) == 0 do
        throwError "prepared lookup was not reused before the original decision supplier"
      let missed ← FiniteData.collectDependencies 1 collected.levels (fun _ => pure #[exact]) fallback
        (fun _ _ => throwError "missed batch hint invoked a record producer")
        (some (fun _ => pure #[]))
      unless missed.saturated && (← fallbackCalls.get) > 0 do
        throwError "missed batch hint suppressed the original decision supplier"
      let zero ← FiniteData.collectDependencies 0 collected.levels (fun _ => pure #[exact]) fallback
        (fun _ _ => throwError "zero-fuel prepared lookup invoked a producer")
        (some (fun _ => throwError "zero-fuel discovery invoked batch preparation"))
      unless zero.saturated do throwError "zero-fuel preparation changed ordinary lookup replay"
      try
        let other := { retained with lookup := { retained.lookup with
          leaf := { retained.lookup.leaf with type := mkConst ``True } } }
        let _ ← FiniteData.collectDependencies 1 collected.levels (fun _ => pure #[exact]) fallback
          (fun _ _ => throwError "unrequested batch evidence invoked a producer")
          (some (fun _ => pure #[other]))
        throwError "preparation accepted an unrequested predicate"
      catch error =>
        unless (← error.toMessageData.toString).startsWith "lookup preparation returned an unrequested predicate" do
          throw error
      let passes ← IO.mkRef (0 : Nat)
      let batch (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
        passes.modify (· + 1)
        let some current := levels[0]? | throwError "batch discovery lost its level"
        let mut requested := #[]
        for number in [1, 2, 3, 1] do
          let polynomial ← mkAppM ``DensePoly.C #[toExpr (number : Rat)]
          let found ← mkAppM ``Packing.find #[current.entries, polynomial]
          requested := requested.push
            (← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true))
        return requested
      let produce (lookup : FiniteData.Lookup) (_ : Array FiniteData.Level) := do
        return some (← FiniteTowerPackets.packing lookup.request.polynomial)
      checkRefreshed empty
      let decisionCount ← IO.mkRef (0 : Nat)
      let counted : FiniteData.Supplier := fun type => do
        decisionCount.modify (· + 1)
        decisions type
      let batched ← FiniteData.collectDependencies 3 #[empty] batch counted produce
      unless batched.saturated && batched.requests.size == 3 && batched.leaves.isEmpty do
        throwError "batch discovery lost a key or charged a repeated request twice"
      unless (← passes.get) == 2 do
        throwError "dependency discovery rebuilt the full frontier after individual records"
      unless (← decisionCount.get) == 6 do
        throwError "exact lookup reuse expected six decisions, got {← decisionCount.get}"
      let known ← IO.mkRef batched.known
      let cachedLookup := FiniteData.lookupSupplier known
        (fun _ => throwError "retained closed lookup invoked its decision procedure")
      for type in ← batch batched.levels do
        let some proof ← cachedLookup type | throwError "retained lookup lost its exact key"
        unless (← inferType proof) == type do
          throwError "retained lookup changed the exact statement"
        let _ ← auditProof proof type
        kernelCheck `__finiteKnownLookup type proof
      -- Exact inserted bindings suffice even when the external decider cannot
      -- normalize these lookups. Repeated keys must not consume more records.
      let noDecisions ← FiniteData.collectDependencies 10 #[empty] batch
        (fun _ => pure none) produce
      unless noDecisions.saturated && noDecisions.requests.size == 3 do
        throwError "checked insertion bindings did not prevent duplicate collection"
      let aliasKey ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
      let some firstKnown := batched.known[0]? | throwError "alias control lost its checked record"
      unless firstKnown.lookup.key == aliasKey do throwError "alias control has a different key"
      let literal := firstKnown.lookup.inventory
      let parameters := literal.getAppArgs
      unless literal.getAppFn.isConstOf ``List.cons && parameters.size == 3 do
        throwError "alias control has no literal inserted record"
      let aliasFact := parameters[1]!
      let aliasRequests (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
        let some current := levels[0]? | throwError "alias control lost its level"
        let aliased ← mkAppM ``inventoryAlias #[current.entries]
        let mut statements := #[]
        for inventory in #[current.entries, aliased] do
          let found ← mkAppM ``Packing.find #[inventory, aliasKey]
          statements := statements.push
            (← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true))
        return statements
      let aliases ← FiniteData.collectDependencies 2 #[empty] aliasRequests
        (fun _ => pure none) (fun _ _ => pure (some aliasFact))
      unless !aliases.saturated && !aliases.leaves.isEmpty && aliases.requests.size == 1 do
        throwError "inventory alias reported saturation with an unresolved lookup"
      let foreignPositive ← FiniteData.collectDependencies 1 #[empty]
        (fun _ => pure #[foreignRequest]) (fun _ => pure none)
        (fun _ _ => throwError "foreign inventory invoked a producer with positive fuel")
      unless !foreignPositive.saturated && foreignPositive.requests.isEmpty do
        throwError "foreign inventory changed refusal policy with positive fuel"
      let fallbackCount ← IO.mkRef (0 : Nat)
      let fallback := FiniteData.lookupSupplier known (fun _ => do
        fallbackCount.modify (· + 1)
        return none)
      let query (finder inventory key : Expr) : MetaM Unit := do
        let type ← mkEq (← mkAppM ``Option.isSome #[← mkAppM finder.constName! #[inventory, key]])
          (mkConst ``Bool.true)
        unless (← fallback type).isNone do throwError "lookup cache accepted a different request"
      let unitKey ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
      let otherKey ← mkAppM ``DensePoly.C #[toExpr (4 : Rat)]
      let some complete := batched.levels[0]? | throwError "batch discovery lost its owner"
      query (mkConst ``Packing.find) complete.entries otherKey
      query (mkConst ``Packing.find) level.entries unitKey
      let otherOwner ← Elab.Term.elabTerm
        (← `(Context.adjoin FiniteTower.firstRoot (fun _ => false))) none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let otherEntries ← mkListLit (← mkAppM ``Packing #[← instantiateMVars otherOwner]) []
      query (mkConst ``Packing.find) otherEntries unitKey
      let value ← Elab.Term.elabTerm
        (← `(Element.ofPoly (context := FiniteTower.first) (DensePoly.C (1 : Rat)))) none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      query (mkConst ``ValueSign.find) level.records value
      let typed ← mkAppM ``Packing.find #[complete.entries, unitKey]
      let arguments := typed.getAppArgs
      let changed := mkAppN typed.getAppFn (arguments.set! 2 (mkConst ``cacheZero))
      let changedType ← mkEq (← mkAppM ``Option.isSome #[changed]) (mkConst ``Bool.true)
      check changedType
      unless (← fallback changedType).isNone do
        throwError "lookup cache ignored a changed implicit instance"
      unless (← fallbackCount.get) == 5 do
        throwError "lookup cache failed to delegate a changed key, inventory, owner, kind or instance"
      let uncached ← IO.mkRef (#[] : Array FiniteData.KnownLookup)
      let reflexive := FiniteData.lookupSupplier uncached
        (fun _ => return some (← mkEqRefl (mkConst ``Bool.true)))
      let originalType ← mkEq (← mkAppM ``Option.isSome #[typed]) (mkConst ``Bool.true)
      let some proof ← reflexive originalType | throwError "ordinary lookup proof was discarded"
      kernelCheck `__finiteReflexiveLookup originalType proof
      unless (← uncached.get).isEmpty do
        throwError "lookup cache retained a proof with a different syntactic type"
      let limited ← FiniteData.collectDependencies 1 #[empty] batch decisions produce
      unless !limited.saturated && limited.requests.size == 1 && !limited.leaves.isEmpty do
        throwError "batch discovery accepted a missing key after exhausting its record budget"
      let three ← mkAppOptM ``Nat.cast #[some source, none, some (toExpr (3 : Nat))]
      let realThree ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (toExpr (3 : Nat))]
      let castType ← mkEq (mkApp reader three) realThree
      let castLeaf : FiniteData.Leaf := ⟨castType, ← getLCtx, ← getLocalInstances⟩
      let some casts ← level.lower castLeaf | throwError "natural cast dependency was not lowered"
      unless casts.size == 2 do throwError "natural cast lost its key or predecessor equation"
      let keyLeaf : FiniteData.Leaf := ⟨casts[0]!, ← getLCtx, ← getLocalInstances⟩
      let some lookup ← keyLeaf.lookup? | throwError "cast dependency lost its original key"
      let expectedKey ← mkAppM ``DensePoly.C #[toExpr (3 : Rat)]
      retain `castKey (← mkEq lookup.key expectedKey) (← mkEqRefl lookup.key)
      let zero ← mkAppOptM ``Zero.zero #[some source, none]
      let realZero ← mkAppOptM ``Zero.zero #[some (mkConst ``Real), none]
      let zeroLeaf : FiniteData.Leaf := ⟨← mkEq (mkApp reader zero) realZero,
        ← getLCtx, ← getLocalInstances⟩
      let some zeroRequired ← level.lower zeroLeaf | throwError "stored zero dependency was not recognized"
      unless zeroRequired.isEmpty do throwError "stored zero dependency required a packing key"
      logInfo "dependency discovery lowered product and cast premises with unchosen readers; original operands retained"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
set_option smartUnfolding false in
/-- info: dependency discovery lowered product and cast premises with unchosen readers; original operands retained -/
#guard_msgs in
#finite_dependencies_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe.productLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe.productLowering
