/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
-- This independent audit needs full private import data.

import KernelReplay.AxiomClosure
import KernelReplay.ProofAudit
import KernelReplay.FrameOperand
import KernelReplay.FramePublic
import KernelReplay.NativeAssemblyUse
import Lean.Util.CollectAxioms

section
open Lean Meta Elab
open Hex.RealClosure.Algebraic.KernelReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let names := #[``ProofAudit.Branch, ``ProofAudit.Branch.leaf,
    ``ProofAudit.Branch.node, ``ProofAudit.Branch.rec, ``ProofAudit.Branch.casesOn]
  for name in names do
    let independent ← AxiomClosure.collect #[name]
    unless independent == #[`Classical.choice] do
      throwError "direct body audit omitted the indexed constructor dependency"
    logInfo m!"dependency closure {name}: independent={independent}; exported={← collectAxioms name}"
  let combined ← AxiomClosure.collect (names ++ #[``propext, ``Quot.sound])
  unless combined == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "direct body audit changed the union of requested roots"
  for name in #[``FrameOperand.beta_native, ``FrameOperand.request_native,
      ``FramePublic.product, ``NativeAssemblyStaged.exists_joint,
      ``NativeAssemblyUse.coordinate] do
    let .thmInfo info ← getConstInfo name | throwError "native source theorem missing"
    let axioms ← AxiomClosure.audit info.value info.type
    logInfo m!"native source direct audit {name}: {axioms}"
  let missing ← mkFreshUserName `missingClosure
  let rejected ← try
    let _ ← AxiomClosure.collect #[missing]
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith
        "axiom closure cannot inspect checked declaration" do throw error
    pure true
  unless rejected do throwError "direct body audit accepted an uninspectable declaration"
  let incomplete ← mkFreshExprMVar (mkConst ``True)
  let rejected ← try
    let _ ← AxiomClosure.audit incomplete (mkConst ``True)
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith
        "independent axiom audit needs a complete closed" do throw error
    pure true
  unless rejected && !(← incomplete.mvarId!.isAssigned) do
    throwError "direct body audit accepted or assigned an incomplete proof"
