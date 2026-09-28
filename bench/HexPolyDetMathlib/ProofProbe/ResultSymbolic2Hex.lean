/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultSymbolic2Hex.certificate (x : Int) : {d : Int // Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  let c := det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int)
  exact ⟨c.value, c.proof⟩
