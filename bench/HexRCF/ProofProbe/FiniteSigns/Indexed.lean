/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.CertificationInputs
public section
namespace Hex.RCF.ProofProbe.FiniteSigns.Indexed
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
set_option debug.skipKernelTC false
set_option Elab.async false
set_option rcf.algebraic.indexSigns true

theorem witness : ∀ x : ℝ,
    x^2-(Hex.RCF.CertificationInputs.realAlgebraic.toReal+Real.sqrt 2)*x+
      Hex.RCF.CertificationInputs.realAlgebraic.toReal*Real.sqrt 2<0 → 1<x ∧ x<2 := by rcf

#print axioms witness
end Hex.RCF.ProofProbe.FiniteSigns.Indexed
