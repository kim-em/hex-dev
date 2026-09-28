/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultIdentity4Hex.certificate (x : Int) : {d : Int // Matrix.det !![1 + 1*x, 2*x, 3*x, 4*x; 2*x, 1 + 4*x, 6*x, 8*x; 3*x, 6*x, 1 + 9*x, 12*x; 4*x, 8*x, 12*x, 1 + 16*x] = d} := by
  let c := det% !![1 + 1*x, 2*x, 3*x, 4*x; 2*x, 1 + 4*x, 6*x, 8*x; 3*x, 6*x, 1 + 9*x, 12*x; 4*x, 8*x, 12*x, 1 + 16*x]
  exact ⟨c.value, c.proof⟩
