/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Fixtures
public import HexRCF.Soundness
public section
namespace CadSampleCosts.CircleParabola
@[expose] def input : Hex.RCF.Sentence := cadCircleParabolaInput
@[expose] def certificate : Hex.RCF.Certificate := cadCircleParabolaCert
end CadSampleCosts.CircleParabola
