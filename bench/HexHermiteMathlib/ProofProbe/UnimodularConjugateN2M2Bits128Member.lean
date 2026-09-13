/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexHermiteMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : (![-127605887595351923798765477786913079292, 2] : Fin 2 → ℤ) ∈
    Submodule.span ℤ (Set.range !![42535295865117307932921825928971026432, 0; -85070591730234615865843651857942052860, 2]) := by hermite

#print axioms result
