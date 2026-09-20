/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Fixtures
public import HexRCF.Soundness
public section
namespace CadSampleCosts.Sphere
@[expose] def input : Hex.RCF.Sentence := cadSphereInput
@[expose] def certificate : Hex.RCF.Certificate := cadSphereCert
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
#print axioms result
end CadSampleCosts.Sphere
