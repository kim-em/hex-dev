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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  for name in #[``FiniteReconstructionProbe.baseJoint,
      ``FiniteReconstructionProbe.selectedJoint, ``FiniteReconstructionProbe.nestedJoint,
      ``NativeAssemblyStaged.exists_joint, ``NativeAssemblyUse.coordinate] do
    let .thmInfo info ← getConstInfo name |
      throwError "support reconstruction theorem missing: {name}"
    let axioms ← AxiomClosure.audit info.value info.type
    unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
      throwError "support reconstruction changed its complete axiom closure: {name}"
    logInfo m!"support reconstruction direct body audit {name}: {axioms}"
