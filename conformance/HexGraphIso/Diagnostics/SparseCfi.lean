/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso.SparseProofProbe.Support

/-! Scheduled negative CFI replay, with the dense probe's larger limits. -/

set_option maxRecDepth 4000000
set_option maxHeartbeats 40000000

open Hex.GraphIso Hex.GraphIso.SparseProofProbe in
theorem Hex.GraphIso.SparseProofProbe.cfi_ne : ¬ Sparse.Isomorphic (cfi false) (cfi true) := by
  graph_iso (maxSearchNodes := 100000000) (maxCertRecords := 100000000)

#print axioms Hex.GraphIso.SparseProofProbe.cfi_ne
