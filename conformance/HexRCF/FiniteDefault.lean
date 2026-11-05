/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public section
open Hex
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
set_option debug.skipKernelTC false
set_option Elab.async false
namespace Hex.RCF.FiniteDefault

theorem positive : ∀ x : ℝ,
    x^2+CertificationInputs.realAlgebraic.toReal+Real.sqrt 2>0 := by rcf

theorem betweenRoots : ∀ x : ℝ,
    x^2-(CertificationInputs.realAlgebraic.toReal+Real.sqrt 2)*x+
      CertificationInputs.realAlgebraic.toReal*Real.sqrt 2<0 → 1<x ∧ x<2 := by rcf

theorem nested : ∀ x : ℝ,
    x^2+Real.sqrt (CertificationInputs.realAlgebraic.toReal+Real.sqrt 2)>0 := by rcf

end Hex.RCF.FiniteDefault
#print axioms Hex.RCF.FiniteDefault.positive
#print axioms Hex.RCF.FiniteDefault.betweenRoots
#print axioms Hex.RCF.FiniteDefault.nested
