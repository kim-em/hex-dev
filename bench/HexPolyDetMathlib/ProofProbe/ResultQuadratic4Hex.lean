/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (HexPolyDetMathlib.ProofProbe.quadratic x) = d} := by
  let c := det% (HexPolyDetMathlib.ProofProbe.quadratic x)
  exact ⟨c.value, c.proof⟩

#print axioms certificate
