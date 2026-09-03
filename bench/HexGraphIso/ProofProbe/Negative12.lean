/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The negative pair from the two recorded `G(12, 1/2)` seeds (SPEC
release case 2). -/

set_option maxRecDepth 400000

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : ¬ Isomorphic g12 g12b := by graph_iso
