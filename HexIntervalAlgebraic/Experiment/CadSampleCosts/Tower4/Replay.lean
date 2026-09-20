/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Fixtures
public import HexRCF.Soundness
public section
namespace CadSampleCosts.Tower4
@[expose] def input : Hex.RCF.Sentence := cadTower4Input
@[expose] def certificate : Hex.RCF.Certificate := cadTower4Cert
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
#print axioms result
end CadSampleCosts.Tower4
