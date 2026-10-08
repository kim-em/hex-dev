/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexGraphIso.SparseProofProbe.Support

public meta import HexGraphIso.SparseProofProbe.Support

public section

set_option maxRecDepth 100000

open Hex.GraphIso Hex.GraphIso.SparseProofProbe in
theorem Hex.GraphIso.SparseProofProbe.coloured10Neg :
    ¬ Sparse.Isomorphic edgeMarkA nonedgeMark := by graph_iso

/-- info: 'Hex.GraphIso.SparseProofProbe.coloured10Neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.GraphIso.SparseProofProbe.coloured10Neg
