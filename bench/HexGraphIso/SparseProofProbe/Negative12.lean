/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso.SparseProofProbe.Support

set_option maxRecDepth 100000

open Hex.GraphIso Hex.GraphIso.SparseProofProbe in
theorem Hex.GraphIso.SparseProofProbe.negative12 :
    ¬ Sparse.Isomorphic random12 random12b := by graph_iso

/-- info: 'Hex.GraphIso.SparseProofProbe.negative12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.GraphIso.SparseProofProbe.negative12
