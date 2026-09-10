/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIsoMathlib.ProofProbe.Support

/-! The positive random `n = 12` relabelled pair on the Mathlib route. -/

open Hex.GraphIso.MathlibProofProbe in
example : Nonempty (g12 ≃g g12relabelled) := by graph_iso
