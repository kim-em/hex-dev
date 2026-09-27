/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

private def certificate : {d : Int // Matrix.det (!![(1 : Int), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  let c := det% (!![(1 : Int), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int)
  exact ⟨c.value, c.proof⟩

#print axioms certificate
