/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Diagnostics.Linear
public meta import HexSignDet.Reencode
public meta import HexSignDet.Replay

public section
namespace Hex.SignDetMathlib.ProofProbe.Reencoding
open Hex Hex.SignDet Hex.SignDetMathlib.Diagnostics.Linear
open scoped Hex

set_option maxRecDepth 32768 in
/-- Re-encode the root of X using 2X. Joint evidence accepts, while copying the
source's old count certificate in place of the joint evidence rejects. -/
theorem checked :
    source.checkReencoding target targetHead .negInf .posInf joint = true ∧
    source.checkReencoding target targetHead .negInf .posInf (.leaf countNode) = false := by
  constructor
  · exact reencoded
  · simp only [Descriptor.checkReencoding, source_raw, target_raw, Replay.check,
      Node.check_eq, checkMoment_eq, queryPoly, Sturm.check, TarskiCertificate.check_eq,
      SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
    decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Reencoding.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Reencoding
