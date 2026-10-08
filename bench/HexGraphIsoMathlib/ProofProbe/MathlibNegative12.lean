/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.ProofProbe.Support

public meta import HexGraphIsoMathlib.ProofProbe.Support

public section

/-! The negative random `n = 12` pair on the Mathlib route. -/

set_option maxRecDepth 400000

open Hex.GraphIso.MathlibProofProbe in
example : IsEmpty (g12 ≃g g12b) := by graph_iso
