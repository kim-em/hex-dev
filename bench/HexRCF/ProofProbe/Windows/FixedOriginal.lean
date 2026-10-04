/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Windows.Support
public meta import HexRCF.ProofProbe.Windows.Support
public section

namespace Hex.RCF.ProofProbe.Windows.FixedOriginal
open Hex.RCF.ProofProbe.Windows
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.reducedLiterals false
set_option rcf.algebraic.intervalSigns true
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.indexSigns true
set_option rcf.algebraic.monicCore true
set_option rcf.algebraic.signRefinements 0

theorem witness : sentence := by fixed_window_rcf

/-- info: 'Hex.RCF.ProofProbe.Windows.FixedOriginal.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

run_meta do
  let window ← Hex.RCF.ProofProbe.Literals.usesConstructor `Hex.RCF.ProofProbe.Windows.FixedOriginal.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do
    throwError "fixed-field probe used the wrong generator-window evidence"

#print axioms witness
end Hex.RCF.ProofProbe.Windows.FixedOriginal
