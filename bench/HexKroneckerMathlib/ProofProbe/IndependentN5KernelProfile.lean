/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexKroneckerMathlib.ProofProbe.IndependentN5Construction

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 0
open KroneckerProbe.IndependentN5

theorem declineResult : (match Hex.Kronecker.sizeExprEq {} 25 leftTree rightTree with
    | .ok s => !s.accepts {}
    | .error _ => false) = true := by
  decide +kernel

#print axioms declineResult
