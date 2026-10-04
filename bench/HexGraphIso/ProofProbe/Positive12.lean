/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.ProofProbe.Support

public meta import HexGraphIso.ProofProbe.Support

public section

/-! The positive random `n = 12` pair related by the recorded
relabelling. -/

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : Isomorphic g12 g12relabelled := by graph_iso
