/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIsoMathlib.ProofProbe.Support

/-! Positive different-vertex-type goal at `n = 10`: the generalized
Petersen and Kneser presentations coincide at `(5, 2)`. -/

open Hex.GraphIso.MathlibProofProbe in
example : Nonempty (gpetersen 5 2 ≃g kneser 5 2) := by graph_iso
