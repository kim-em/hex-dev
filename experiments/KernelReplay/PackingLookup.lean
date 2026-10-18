/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.NativeBatch
public import KernelReplay.FiniteTowerProbe
public meta import KernelReplay.FiniteTowerProbe

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.PackingLookup

/-- A logical identity deliberately unavailable to native execution. -/
noncomputable def uncompiled (p : DensePoly Rat) : DensePoly Rat := p

end Hex.RealClosure.Algebraic.KernelReplay.PackingLookup
end

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.PackingLookup
open Lean Meta Elab Command FiniteData

private def statement (inventory key : Expr) : MetaM Expr := do
  let found ← mkAppM ``Packing.find #[inventory, key]
  mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)

syntax (name := packingLookup) "#packing_lookup" : command
@[command_elab packingLookup]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let fact ← Term.elabTerm (← `(FiniteTowerProbe.nestedEntries[0]'(by decide))) none
    let next ← Term.elabTerm (← `(FiniteTowerProbe.nestedEntries[1]'(by decide))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fact ← instantiateMVars fact
    let next ← instantiateMVars next
    let key ← mkAppM ``Packing.original #[fact]
    let other ← mkAppM ``Packing.original #[next]
    if ← withTransparency .all (isDefEq key other) then
      throwError "packing lookup fixture needs distinct original keys"
    let empty ← mkListLit (← inferType fact) []
    let head ← mkAppM ``List.cons #[fact, empty]
    let extended ← mkAppM ``List.cons #[next, head]
    let changedKey ← mkAppOptM ``id #[some (← inferType key), some key]
    let zero ← mkAppOptM ``Zero.zero #[some (← inferType key), none]
    let arithmetic ← mkAppM ``HAdd.hAdd #[key, zero]
    let aliased ← mkAppOptM ``id #[some (← inferType head), some head]
    let mut leaves := #[]
    for inventory in #[head, extended, aliased] do
      for requested in #[key, changedKey, arithmetic] do
        leaves := leaves.push (⟨← statement inventory requested, ← getLCtx, ← getLocalInstances⟩ : Leaf)
    let retained ← NativeBatch.prepare (leaves ++ leaves)
    unless retained.size == leaves.size do throwError "lookup batch lost or duplicated an original predicate"
    for i in [:leaves.size] do
      let some entry := retained[i]? | throwError "lookup batch lost a projection"
      let some expected := leaves[i]? | throwError "lookup batch lost an input"
      unless entry.lookup.leaf.type == expected.type &&
          (← inferType entry.proof) == expected.type do
        throwError "lookup batch changed the full original predicate"
      let _ ← auditProof entry.proof expected.type
      kernelCheck `__packingLookup expected.type entry.proof
    -- A universe parameter in a closed key alias must be bound by the
    -- retained equality theorem, even when the polynomial carrier is concrete.
    let aliasName := mkPrivateName (← getEnv) (← mkFreshUserName `__packingKeyAlias)
    let universeName ← mkFreshUserName `keyUniverse
    let keyType ← inferType key
    let aliasDeclaration := Declaration.defnDecl {
      name := aliasName, levelParams := [universeName], type := keyType,
      value := key, hints := .regular 0, safety := .safe }
    withOptions (Elab.async.set · false) do
      withOptions (fun options => options.setBool `debug.skipKernelTC false) do
        addDecl aliasDeclaration
    let polymorphic := mkConst aliasName [.param universeName]
    let type ← statement head polymorphic
    unless type.hasLevelParam do throwError "universe regression lost its named level"
    let aliasLeaf : Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
    unless (← NativeBatch.prepare #[aliasLeaf]).isEmpty do
      throwError "native hints attempted a local definition with no executable code"
    let logicalAlias ← checkLookupBatch (← batchCandidates #[aliasLeaf]) #[true]
    unless logicalAlias.size == 1 do throwError "uncompiled alias lost its ordinary-kernel fallback"
    withOptions (Elab.async.set · false) do
      withOptions (fun options => options.setBool `compiler.postponeCompile false) do
        compileDecl aliasDeclaration
    let named ← NativeBatch.prepare #[⟨type, ← getLCtx, ← getLocalInstances⟩]
    let some entry := named[0]? | throwError "lookup batch lost a closed universe parameter"
    let proof := entry.proof
    unless (← inferType proof) == type do throwError "universe regression changed the lookup"
    let _ ← auditProof proof type
    let parameters := collectLevelParams (collectLevelParams {} type) proof |>.params.toList
    unless parameters.contains universeName do throwError "universe regression dropped its binder"
    let theoremName ← mkFreshUserName `__polymorphicPackingLookup
    withOptions (fun options => options.setBool `debug.skipKernelTC false) do
      addDecl (.thmDecl {
        name := theoremName, levelParams := parameters, type, value := proof })
    for (inventory, requested) in #[(empty, key), (head, other)] do
      let missing : Leaf := ⟨← statement inventory requested, ← getLCtx, ← getLocalInstances⟩
      unless (← NativeBatch.prepare #[missing]).isEmpty do
        throwError "lookup batch supplied a missing original key"
    let logicalKey ← mkAppM ``uncompiled #[key]
    let logical : Leaf := ⟨← statement head logicalKey, ← getLCtx, ← getLocalInstances⟩
    unless (← NativeBatch.prepare #[logical]).isEmpty do
      throwError "native batch attempted a non-executable lookup"
    let logicalCandidates ← batchCandidates #[logical]
    let logicalProofs ← checkLookupBatch logicalCandidates #[true]
    let some logicalProof := logicalProofs[0]? | throwError "logical fallback lost the non-executable lookup"
    kernelCheck `__nonExecutableLookup logical.type logicalProof.proof
    let predicate ← withLocalDeclD `value keyType fun value => do
      mkLambdaFVars #[value] (← mkEq value key)
    let existence ← mkAppOptM ``Exists.intro
      #[some keyType, some predicate, some key, some (← mkEqRefl key)]
    let chosen ← mkAppM ``Classical.choose #[existence]
    let chosenLeaf : Leaf := ⟨← statement head chosen, ← getLCtx, ← getLocalInstances⟩
    unless (← NativeBatch.prepare #[chosenLeaf]).isEmpty do
      throwError "non-executable imported dependency did not preserve fallback"
    let equality ← mkAppM ``Eq.symm #[← mkAppM ``Classical.choose_spec #[existence]]
    let chosenProof ← mkAppM ``Packing.find_head #[empty, chosen, fact, equality]
    let _ ← auditProof chosenProof chosenLeaf.type
    kernelCheck `__chosenLookup chosenLeaf.type chosenProof
    let changed : Leaf := ⟨← statement extended other, ← getLCtx, ← getLocalInstances⟩
    unless (← NativeBatch.prepare #[changed]).size == 1 do
      throwError "old missing inventory suppressed a new matching record"
    let good : Leaf := ⟨← statement head key, ← getLCtx, ← getLocalInstances⟩
    let bad : Leaf := ⟨← statement head other, ← getLCtx, ← getLocalInstances⟩
    let candidates ← batchCandidates #[good, bad]
    unless candidates.size == 2 do throwError "corrupted hint control lost its nonempty inventory"
    let mixed ← NativeBatch.prepare #[good, bad]
    let some success := mixed[0]? | throwError "mixed batch lost its successful lookup"
    unless mixed.size == 1 && success.lookup.leaf.type == good.type do
      throwError "mixed batch did not retain exactly the successful original predicate"
    let some firstCandidate := candidates[0]? | throwError "chunk boundary control lost its lookup"
    let count := 2 * lookupBatchSize + 1
    let repeated ← checkLookupBatch (Array.replicate count firstCandidate) (Array.replicate count true)
    unless repeated.size == count do throwError "kernel batch lost a chunk boundary"
    let mut across := #[]
    let mut wrapped := key
    for _ in [:count] do
      wrapped ← mkAppOptM ``id #[some keyType, some wrapped]
      across := across.push (⟨← statement head wrapped, ← getLCtx, ← getLocalInstances⟩ : Leaf)
    let chunked ← NativeBatch.prepare across
    unless chunked.size == count do throwError "native hints lost a bounded batch"
    for i in #[0, lookupBatchSize - 1, lookupBatchSize, 2 * lookupBatchSize - 1, count - 1] do
      let some checked := chunked[i]? | throwError "native batch lost a boundary projection"
      let some expected := across[i]? | throwError "native batch lost a boundary input"
      unless checked.lookup.leaf.type == expected.type do throwError "batch changed order across a boundary"
      kernelCheck `__lookupChunkBoundary expected.type checked.proof
    let timedOut ← tryCatchRuntimeEx (do
      let _ ← withOptions (fun options => maxHeartbeats.set options 1) do
        checkLookupBatch candidates #[true, false]
      pure false) fun error => do
        let message ← error.toMessageData.toString
        if error.isMaxHeartbeat || message.startsWith "(kernel) deterministic timeout" then
          pure true
        else throw error
    unless timedOut do throwError "kernel timeout was swallowed by lookup batching"
    try
      let _ ← checkLookupBatch candidates #[true, true]
      throwError "lookup batch accepted a corrupted native hint"
    catch error =>
      unless (← error.toMessageData.toString).startsWith "(kernel) application type mismatch" do
        throw error
    unless (← checkLookupBatch candidates #[false, false]).isEmpty do
      throwError "false native bits supplied proof objects"
    withLocalDeclD `inventory (← inferType head) fun inventory => do
      unless (← NativeBatch.prepare #[⟨← statement inventory key, ← getLCtx, ← getLocalInstances⟩]).isEmpty do
        throwError "lookup batch supplied an open inventory"
    withLocalDeclD `key (← inferType key) fun key => do
      unless (← NativeBatch.prepare #[⟨← statement head key, ← getLCtx, ← getLocalInstances⟩]).isEmpty do
        throwError "lookup batch supplied an open key"
    let ordinary ← mkEq (mkConst ``Bool.true) (mkConst ``Bool.true)
    unless (← NativeBatch.prepare #[⟨ordinary, ← getLCtx, ← getLocalInstances⟩]).isEmpty do
      throwError "lookup batch consumed a non-lookup check"
    let value ← mkAppM ``Packing.value #[fact]
    let owner := (← inferType fact).getAppArgs.back!
    for (record, finder) in #[(``ValueSign, ``ValueSign.find), (``InverseFact, ``InverseFact.find)] do
      let inventory ← mkListLit (← mkAppM record #[owner]) []
      let found ← mkAppM finder #[inventory, value]
      let type ← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)
      unless (← NativeBatch.prepare #[⟨type, ← getLCtx, ← getLocalInstances⟩]).isEmpty do
        throwError "lookup batch supplied a missing record of another kind"
    let unknown ← mkFreshExprMVar (some (← inferType key))
    unless (← NativeBatch.prepare #[⟨← statement head unknown, ← getLCtx, ← getLocalInstances⟩]).isEmpty do
      throwError "packing lookup chose the caller's key"
    if ← unknown.mvarId!.isAssigned then throwError "packing lookup assigned the caller's key"
    logInfo "batched lookup preserves complete predicates and named universes; missing, open and corrupted requests rejected"

end Hex.RealClosure.Algebraic.KernelReplay.PackingLookup

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: batched lookup preserves complete predicates and named universes; missing, open and corrupted requests rejected -/
#guard_msgs in
#packing_lookup
