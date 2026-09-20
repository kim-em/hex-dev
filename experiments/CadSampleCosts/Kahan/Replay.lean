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
namespace CadSampleCosts.Kahan
@[expose] def input : Hex.RCF.Sentence := cadKahanInput
@[expose] def certificate : Hex.RCF.Certificate := cadKahanCert
theorem correspondence : input.toProp ↔ (∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0) := cad_correspondence% (∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0)
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
theorem sign : ∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0 := correspondence.mp result
theorem sample : ∀ t : ℝ, t^2-2=0 → 1<t → t<2 → ((1+t)/4)^2+(t/8)^2-1<0 := kahanSign sign
#print axioms sample
#print axioms sign
#print axioms result
end CadSampleCosts.Kahan
