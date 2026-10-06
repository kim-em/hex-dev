/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Linear
public meta import HexSignDet.Reencode
public meta import HexSignDet.Replay

public section
namespace Hex.SignDetTheory.ProofProbe.Reencoding
open Hex Hex.SignDet Hex.SignDetTheory.Diagnostics.Linear
open scoped Hex

/-- Preserve the joint tree shape and query bindings, but corrupt the count
of the vanishing query at the selected root. -/
@[expose] def wrongCounts : Replay Rat Nat :=
  match joint with
  | .split node left _ => .split node left
      (.leaf {zeroNode with system := {zeroNode.system with counts := #v[1, 0, 0]}})
  | .leaf node => .leaf node

set_option maxRecDepth 32768 in
/-- Re-encode the root of X using 2X. Joint evidence accepts, while copying the
source's old count certificate in place of the joint evidence rejects. -/
theorem checked :
    source.checkReencoding target targetHead .negInf .posInf joint = true ∧
    source.checkReencoding target targetHead .negInf .posInf (.leaf countNode) = false ∧
    source.checkReencoding target targetHead .negInf .posInf wrongCounts = false := by
  refine ⟨reencoded, ?_⟩
  simp only [Descriptor.checkReencoding, source_raw, target_raw, wrongCounts, joint, Replay.check,
      Node.check_eq, checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
      SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetTheory.ProofProbe.Reencoding.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked
end Hex.SignDetTheory.ProofProbe.Reencoding
