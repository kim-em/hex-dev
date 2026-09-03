/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The positive random `n = 12` pair related by the recorded
relabelling (SPEC release case 1). -/

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : Isomorphic g12 g12relabelled := by graph_iso
