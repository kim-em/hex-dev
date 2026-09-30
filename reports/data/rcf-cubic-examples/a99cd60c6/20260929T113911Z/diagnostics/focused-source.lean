/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRCF.RealCoefficients

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option profiler true
set_option profiler.threshold 1000

example : ∃ x : ℝ,
    (x - (2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = 0 ∧
    x ^ 3 = 2 ∧ 1 < x ∧ x < 3 / 2 := by
  rcf
