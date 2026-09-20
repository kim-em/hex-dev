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
namespace CadSampleCosts.Circles
@[expose] def input : Hex.RCF.Sentence := cadCirclesInput
@[expose] def certificate : Hex.RCF.Certificate := cadCirclesCert
theorem correspondence : input.toProp ↔ (∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0) := cad_correspondence% (∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0)
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
theorem sign : ∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0 := correspondence.mp result
theorem sample : ∀ a b : ℝ, a^2+b^2=1 → (a-1)^2+b^2=1 → b>0 → b-a>0 := circlesSign sign
#print axioms sample
#print axioms sign
#print axioms result
end CadSampleCosts.Circles
