/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.ProofProbe.Support

public meta import HexGraphIso.ProofProbe.Support

public section

/-! The positive ordered-colour pair at `n = 10`: the Petersen graph
with two different adjacent pairs marked with colour zero. -/

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : Isomorphic edgeMarkA edgeMarkB := by graph_iso
