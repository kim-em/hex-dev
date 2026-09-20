/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import CadSampleCosts.Fixtures
import Mathlib.Util.CountHeartbeats
public section
namespace CadSampleCosts.CircleParabola.Kernel
@[expose] def input : Hex.RCF.Sentence := cadCircleParabolaInput
@[expose] def certificate : Hex.RCF.Certificate := cadCircleParabolaCert
set_option profiler true in
set_option profiler.threshold 0 in
#count_heartbeats in
theorem accepted : certificate.check input = true := by decide +kernel
end CadSampleCosts.CircleParabola.Kernel
