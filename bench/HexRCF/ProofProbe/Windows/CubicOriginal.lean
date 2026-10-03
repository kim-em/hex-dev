/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofProbe.Literals.Support
public section
open Hex.RCF.ProofProbe.Literals

namespace Hex.RCF.ProofProbe.Windows.CubicOriginal
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.reducedLiterals false
set_option rcf.algebraic.intervalSigns true
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.indexSigns true
set_option rcf.algebraic.monicCore true
set_option rcf.algebraic.signRefinements 0

theorem witness : ∃ x : ℝ, x ^ 2 = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    1 < x ∧ x < (2 : ℝ) ^ (1 / 3 : ℝ) := by rcf

/-- info: 'Hex.RCF.ProofProbe.Windows.CubicOriginal.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

run_meta do
  unless ← usesConstructor `Hex.RCF.ProofProbe.Windows.CubicOriginal.witness
      ``Hex.PolyQuot.reduce 3 do
    throwError "carrier probe changed its literal quotation constructor"
  unless ← usesInterval `Hex.RCF.ProofProbe.Windows.CubicOriginal.witness do
    throwError "carrier probe omitted interval signs"

  let indexed ← usesConstructor `Hex.RCF.ProofProbe.Windows.CubicOriginal.witness
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExistsIndex_eq 0
  unless indexed == true do
    throwError "sign-index probe used the wrong replay route"

-- The collector inventories this output for every fresh build.
#print axioms witness
end Hex.RCF.ProofProbe.Windows.CubicOriginal
