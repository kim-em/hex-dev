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
end CadSampleCosts.Circles
