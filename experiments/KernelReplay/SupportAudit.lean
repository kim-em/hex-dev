/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
-- Direct dependency auditing requires full private import data.
import KernelReplay.AxiomClosure
import KernelReplay.FiniteReconstruction
import KernelReplay.NativeAssemblyUse

open Lean Meta Elab
open Hex.RealClosure.Algebraic.KernelReplay

private def usesSupport (root : Name) : MetaM Bool := do
  let environment := (← getEnv).checked.get
  let mut pending := [root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    Core.checkSystem "shared support dependency check"
    let name :: rest := pending | throwError "support dependency lost its next name"
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    if isPrivateName name && (`__finiteSupport).isPrefixOf (privateToUserName name) then
      return true
    let some info := environment.find? name |
      throwError "support dependency body is missing: {name}"
    let body := (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    pending := (info.type.getUsedConstants ++ body).toList ++ pending
  return false

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  unless ← usesSupport ``FiniteReconstructionProbe.baseJoint do
    throwError "closed reconstruction did not retain shared support definitions"
  for name in #[``FiniteReconstructionProbe.baseJoint,
      ``FiniteReconstructionProbe.selectedJoint, ``FiniteReconstructionProbe.nestedJoint,
      ``NativeAssemblyStaged.exists_joint, ``NativeAssemblyUse.coordinate] do
    let .thmInfo info ← getConstInfo name |
      throwError "support reconstruction theorem missing: {name}"
    let axioms ← AxiomClosure.audit info.value info.type
    unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
      throwError "support reconstruction changed its complete axiom closure: {name}"
    logInfo m!"support reconstruction direct body audit {name}: {axioms}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  for name in #[``FiniteReconstructionProbe.inventoryReplay,
      ``FiniteReconstructionProbe.inventoryDifference, ``FiniteReconstructionProbe.delegatedProduct,
      ``FiniteReconstructionProbe.inversePacking, ``FiniteReconstructionProbe.inverseOriginal,
      ``FiniteReconstructionProbe.inverseReplay, ``FiniteReconstructionProbe.inverseProduct,
      ``FiniteReconstructionProbe.inverseDifference] do
    let .thmInfo info ← getConstInfo name | throwError "inventory control theorem missing: {name}"
    let axioms ← AxiomClosure.audit info.value info.type
    logInfo m!"inventory direct body audit {name}: {axioms}"
