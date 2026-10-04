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

namespace Hex.RCF.ProofProbe.Literals.CubicReduced
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.monicCore false
set_option rcf.algebraic.indexSigns false
set_option rcf.algebraic.intervalSigns false
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.reducedLiterals true

theorem witness : ∃ x : ℝ, x ^ 2 = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    1 < x ∧ x < (2 : ℝ) ^ (1 / 3 : ℝ) := by rcf

/-- info: 'Hex.RCF.ProofProbe.Literals.CubicReduced.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness

run_meta do
  unless ← usesConstructor `Hex.RCF.ProofProbe.Literals.CubicReduced.witness
      ``Hex.PolyQuot.mk 4 do
    throwError "literal probe did not use its selected quotation constructor"

-- The collector inventories this unguarded output for every fresh build.
#print axioms witness
end Hex.RCF.ProofProbe.Literals.CubicReduced
