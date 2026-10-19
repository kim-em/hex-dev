/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPosDefTheory
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! Complete-call positive-definiteness proof probe. -/

theorem result : (CartanMatrix.E 8).PosDef := by pos_def

#print axioms result
