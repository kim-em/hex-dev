/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Conformance
public meta import HexSignDet.SelectedSigns
public meta import HexSignDet.Replay

public section
namespace Hex.SignDetTheory.ProofProbe.SelectedSigns
open Hex Hex.SignDet Hex.SignDet.Conformance
open scoped Hex

set_option maxRecDepth 32768 in
/-- Literal evidence gives sign +1 for the constant query at the positive
root of X²−1; the same evidence rejects the claimed sign zero. -/
theorem checked :
    singletonRaw.checkSigns Sturm.orderSign 7 [1] #v[1] (.leaf selectedNode) = true ∧
    singletonRaw.checkSigns Sturm.orderSign 7 [1] #v[0] (.leaf selectedNode) = false := by
  simp only [RawDescriptor.checkSigns, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetTheory.ProofProbe.SelectedSigns.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked
end Hex.SignDetTheory.ProofProbe.SelectedSigns
