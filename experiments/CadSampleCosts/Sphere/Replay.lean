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
namespace CadSampleCosts.Sphere
@[expose] def input : Hex.RCF.Sentence := cadSphereInput
@[expose] def certificate : Hex.RCF.Certificate := cadSphereCert
theorem correspondence : input.toProp ↔ (∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0) := cad_correspondence% (∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0)
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
theorem sign : ∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0 := correspondence.mp result
#print axioms sign
#print axioms result
end CadSampleCosts.Sphere
