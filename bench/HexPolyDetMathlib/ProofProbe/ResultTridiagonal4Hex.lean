/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultTridiagonal4Hex.certificate (x : Int) : {d : Int // Matrix.det (HexPolyDetMathlib.ProofProbe.tridiagonal x) = d} := by
  let c := det% (HexPolyDetMathlib.ProofProbe.tridiagonal x)
  exact ⟨c.value, c.proof⟩
