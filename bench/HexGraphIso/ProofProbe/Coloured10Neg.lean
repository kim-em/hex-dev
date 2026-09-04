/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The negative ordered-colour pair at `n = 10` (SPEC release case 3,
negative half): an adjacent marked pair against a non-adjacent one.
-/

set_option maxRecDepth 100000

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : ¬ Isomorphic edgeMarkA nonedgeMark := by graph_iso
