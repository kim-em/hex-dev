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
namespace CadSampleCosts.Vanishing
@[expose] def input : Hex.RCF.Sentence := cadVanishingInput
@[expose] def certificate : Hex.RCF.Certificate := cadVanishingCert
theorem correspondence : input.toProp ↔ (∀ x : ℝ, x^4+x^2-1=0 → (x^2)^2+x^2-1=0) := cad_correspondence% (∀ x : ℝ, x^4+x^2-1=0 → (x^2)^2+x^2-1=0)
end CadSampleCosts.Vanishing
