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
namespace CadSampleCosts.CircleParabola
@[expose] def input : Hex.RCF.Sentence := cadCircleParabolaInput
@[expose] def certificate : Hex.RCF.Certificate := cadCircleParabolaCert
theorem correspondence : input.toProp ↔ (∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0) := cad_correspondence% (∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0)
end CadSampleCosts.CircleParabola
