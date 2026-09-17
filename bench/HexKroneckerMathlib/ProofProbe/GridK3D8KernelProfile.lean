/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexKroneckerMathlib.ProofProbe.GridK3D8Construction

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 0
open KroneckerProbe.GridK3D8
theorem kernelResult : Hex.Kronecker.Kernel.exprEq 3 leftTree rightTree = true := by
  decide +kernel
#print axioms kernelResult
