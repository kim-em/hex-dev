/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIsoMathlib.ProofProbe.Support

/-! Negative same-family goal at `n = 10`: `G(5, 2)` against the
pentagonal prism `G(5, 1)`. -/

open Hex.GraphIso.MathlibProofProbe in
example : IsEmpty (gpetersen 5 2 ≃g gpetersen 5 1) := by graph_iso
