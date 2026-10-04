/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Precision.Support
public meta import HexRCF.ProofProbe.Precision.Support
public section

namespace Hex.RCF.ProofProbe.Precision.Bits64
open Hex.RCF.ProofProbe Precision Windows
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.reducedLiterals false
set_option rcf.algebraic.intervalSigns true
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.indexSigns true
set_option rcf.algebraic.monicCore true
set_option rcf.algebraic.signRefinements 0

theorem witness : sentence8 := by precision64_rcf

/-- info: 'Hex.RCF.ProofProbe.Precision.Bits64.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

run_meta do
  let window ← Hex.RCF.ProofProbe.Literals.usesConstructor `Hex.RCF.ProofProbe.Precision.Bits64.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do throwError "precision probe unexpectedly refined its generator"

#print axioms witness
end Hex.RCF.ProofProbe.Precision.Bits64
