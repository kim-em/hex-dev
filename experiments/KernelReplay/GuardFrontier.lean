/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardOperand
public meta import KernelReplay.GuardOperand
public meta import KernelReplay.GuardFrontierStore
import all KernelReplay.GuardOperand
import all KernelReplay.GuardFrontierStore
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand
import all KernelReplay.GuardDescriptorInputs

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardFrontier
open Lean Meta Elab FiniteData GuardDescriptorInputs

/-- Read only exact imported lookup propositions and their checked projections.
This reuses discovery decisions; no real interpretation is supplied here. -/
private def batch (known : IO.Ref (Array KnownLookup)) (type proof : Expr)
    (table : PHashMap Expr Expr) (fuel : Nat := 16) :
    MetaM (PHashMap Expr Expr) := do
  let fuel + 1 := fuel | throwError "captured lookup conjunction exceeds its bound"
  if type.getAppFn.isConstOf ``And then
    let args := type.getAppArgs
    let left := mkAppN (mkConst ``And.left) #[args[0]!, args[1]!, proof]
    let right := mkAppN (mkConst ``And.right) #[args[0]!, args[1]!, proof]
    let table ← batch known args[0]! left table fuel
    batch known args[1]! right table fuel
  else
    let leaf : Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
    if let some lookup ← leaf.lookup? then
      known.modify (·.push ⟨lookup, proof⟩)
      return table.insert type proof
    throwError "captured lookup batch contains a different predicate"

private def note (began : Nat) (message : String) : MetaM Unit := do
  let _ ← bounded began
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"original frontier: {message} heartbeat={((← IO.getNumHeartbeats)-began)/1000}"
      handle.flush

private def recordType (name : Name) (owner : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf (← inferType owner))
  unless type.getAppFn.isConstOf ``Context do throwError "original owner changed type"
  return mkAppN (mkConst name type.getAppFn.constLevels!) (type.getAppArgs.push owner)

private def requirements (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
  unless levels.size == 2 do throwError "original frontier lost one of its two owners"
  let some second := levels[1]? | throwError "original second level is missing"
  let polynomial := mkConst ``FrameOperand.requestPoly
  let mut result := #[← mkAppM ``Transport.Product #[second.reader, polynomial, polynomial]]
  for level in levels do
    result := result.push (← mkAppM ``Packing.Inventory.Data
      #[level.context, level.entries, level.records, level.facts, level.read])
    let contextType ← withTransparency .all (whnf (← inferType level.context))
    let parameters := contextType.getAppArgs
    let coefficientLevel := contextType.getAppFn.constLevels![0]!
    let unit := mkAppN (mkConst ``One.one [coefficientLevel])
      #[parameters[0]!, parameters[4]!]
    let constant := mkAppN (mkConst ``DensePoly.C [coefficientLevel])
      #[parameters[0]!, parameters[2]!, parameters[3]!, unit]
    let zero ← recordType ``Element.zero level.context
    let one := mkApp (← recordType ``Element.ofPoly level.context) constant
    for (input, name) in #[(zero, ``Zero.zero), (one, ``One.one)] do
      let output ← mkAppOptM name #[some (mkConst ``Real), none]
      result := result.push (← mkEq (mkApp level.reader input) output)
  return result

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let environment ← getEnv
  let names := environment.checked.get.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.FrameJoint." &&
        (name.toString.splitOn "__finiteLookupBatch").length > 1 && info.isTheorem then
      found.push name else found) (#[] : Array Name)
  unless !names.isEmpty do throwError "original imported lookup batches are missing"
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let mut table : PHashMap Expr Expr := {}
  for name in names do
    let _ ← bounded began
    table ← batch known (← getConstInfo name).type (mkConst name) table
  logInfo m!"original discovery lookup batches restored: batches={names.size}"
  let fallback := lookupSupplier known FiniteDataProbe.supply
  let decisions : Supplier := fun type => do
    if let some proof := table.find? type then return some proof
    fallback type
  let first := (← getConstInfo ``GuardCapture.first.data).type.getAppArgs
  let second := (← getConstInfo ``GuardCapture.second.data).type.getAppArgs
  let firstOwner := first[first.size - 5]!
  let secondOwner := second[second.size - 5]!
  let baseReadType ← inferType (mkConst ``GuardCapture.read)
  let firstReadType ← inferType (mkConst ``GuardCapture.first.reader)
  let secondReadType ← inferType (mkConst ``GuardCapture.second.reader)
  withLocalDeclD `baseReader baseReadType fun baseReader =>
    withLocalDeclD `firstReader firstReadType fun firstReader =>
      withLocalDeclD `secondReader secondReadType fun secondReader => do
        let globals := #[baseReader, firstReader, secondReader]
        let scope ← getLCtx
        let levels : Array FiniteData.Level := #[
          ⟨firstOwner, first[first.size-4]!, first[first.size-3]!, first[first.size-2]!,
            baseReader, firstReader⟩,
          ⟨secondOwner, second[second.size-4]!, second[second.size-3]!, second[second.size-2]!,
            firstReader, secondReader⟩]
        let types ← requirements levels
        let mut roots := #[]
        for type in types do
          let remaining ← bounded began
          roots := roots ++ (← withOptions (maxHeartbeats.set · remaining) do
            frontier type dependencyBoundary decisions)
        let remaining ← bounded began
        let leaves ← withOptions (maxHeartbeats.set · remaining) do
          descend 3 levels roots decisions
        unless leaves.size == 3772 do
          throwError "original final discovery frontier changed: {leaves.size}"
        note began "exact3772 discovery leaves recovered"
        let requested : Leaf := ⟨types[0]!, scope, ← getLocalInstances⟩
        for (leaf, index) in (leaves.push requested).zipIdx do
          let _ ← bounded began
          let template ← leaf.withContext do
            let hypotheses := (← getLCtx).getFVarIds.filter (fun id => (scope.find? id).isNone)
            let predicate ← mkForallFVars (hypotheses.map mkFVar) leaf.type (usedOnly := true)
            mkLambdaFVars globals predicate (usedOnly := false)
          let template ← instantiateMVars template
          if template.hasFVar || template.hasMVar || template.hasSorry || template.hasLooseBVars then
            throwError "discovery syntax has an incomplete reader binding"
          modifyEnv (templates.addEntry · template)
          if index % 128 == 0 then note began s!"unproved expression {index} saved"
        note began "all3773 templates retained"
        unless (templates.getState (← getEnv)).size == 3773 do
          throwError "complete discovery expression inventory changed length"
        logInfo m!"original discovery expressions retained: leaves=3772 requested=1 expressions=3773 unchosenReaders=3 proofOfGuards=false aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardFrontier
