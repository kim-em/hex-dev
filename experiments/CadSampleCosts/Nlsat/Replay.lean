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
namespace CadSampleCosts.Nlsat
@[expose] def input : Hex.RCF.Sentence := cadNlsatInput
@[expose] def certificate : Hex.RCF.Certificate := cadNlsatCert
theorem correspondence : input.toProp ↔ (∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0) := cad_correspondence% (∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0)
theorem accepted : certificate.check input = true := by decide +kernel
theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted
theorem sign : ∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0 := correspondence.mp result
theorem sample : ∀ a b : ℝ, 16*a^3-8*a^2+a+16=0 → a<0 → a^2+b^2=1 → a^3+2*a^2+3*b^2-5<0 := nlsatSign sign
#print axioms sample
#print axioms sign
#print axioms result
end CadSampleCosts.Nlsat
