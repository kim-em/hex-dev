/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso.SparseProofProbe.Support

set_option maxRecDepth 100000

open Hex.GraphIso Hex.GraphIso.SparseProofProbe in
theorem Hex.GraphIso.SparseProofProbe.coloured10Neg :
    ¬ Sparse.Isomorphic edgeMarkA nonedgeMark := by graph_iso

#print axioms Hex.GraphIso.SparseProofProbe.coloured10Neg
