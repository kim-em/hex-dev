/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ProofProbe.CommonRoots.Shared
set_option maxRecDepth 8192
set_option maxHeartbeats 4800000
set_option Elab.async false
set_option debug.skipKernelTC false
set_option rcf.algebraic.reducedLiterals false
set_option rcf.algebraic.intervalSigns true
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.indexSigns true
set_option rcf.algebraic.monicCore true
set_option rcf.algebraic.signRefinements 0

theorem witness : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧
    (x ^ 2 - Real.sqrt 2) * (x - 1) = 0 ∧ 1 < x ∧ x < 2 := by rcf

#print axioms witness
end Hex.RCF.ProofProbe.CommonRoots.Shared
