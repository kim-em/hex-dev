/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic

-- Keep this check separate from tests that intentionally import the comparator.
run_cmd do
  if (← Lean.getEnv).contains `norm_det then
    throwError "Hex determinant tactics must not import Mathlib's norm_det"
