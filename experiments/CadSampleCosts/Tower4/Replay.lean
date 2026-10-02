/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import CadSampleCosts.Fixtures
public import HexRCF.Soundness
public import CadSampleCosts.Transport
public meta import CadSampleCosts.Support
public section
namespace CadSampleCosts.Tower4
@[expose] def input : Hex.RCF.Sentence := cadTower4Input
@[expose] def certificate : Hex.RCF.Certificate := cadTower4Cert
theorem correspondence : input.toProp ↔ (∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0) := cad_correspondence% (∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0)
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
theorem sign : ∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0 := correspondence.mp result
end CadSampleCosts.Tower4
