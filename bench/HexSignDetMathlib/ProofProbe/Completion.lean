/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Conformance
public meta import HexSignDet.Complete
public meta import HexSignDet.Replay

public section
namespace Hex.SignDetMathlib.ProofProbe.Completion
open Hex Hex.SignDet Hex.SignDet.Conformance
open scoped Hex

set_option maxRecDepth 32768 in
/-- Both supplied descriptors select the positive root of X²−1. Completing
its empty partial word to `[+1,+1]` preserves it; a copied context is rejected. -/
theorem checked :
    singletonRaw.check Sturm.orderSign 7 (.leaf singletonNode) = true ∧
    (singletonRaw.full [1, 1]).check Sturm.orderSign 7 fullReplay = true ∧
    singletonRaw.completes (singletonRaw.full [1, 1]) = true ∧
    singletonRaw.completes {singletonRaw.full [1, 1] with context := 8} = false ∧
    (singletonRaw.full [-1, 1]).check Sturm.orderSign 7 fullReplay = false ∧
    derivativeRaw.completes (derivativeRaw.full [1, 1]) = true ∧
    derivativeRaw.completes (derivativeRaw.full [1, -1]) = false := by
  simp only [RawDescriptor.check, fullReplay, Replay.check, Node.check_eq,
    checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Completion.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Completion
