/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso
import HexGraphIso.SparseTestGraphs
import HexGraphIso.ProofProbe.Support

/-! Imported native sparse inputs for fresh-module kernel replay probes.
The CFI pair shares the dense probe's adjacency predicate, constructing sparse
edges directly without allocating a dense graph. -/

namespace Hex.GraphIso.SparseProofProbe

open Hex

export SparseTestGraphs
  (random12 random12relabeled random12b edgeMarkA edgeMarkB nonedgeMark)

/-- The untwisted or singly twisted CFI graph over `K4`, in sparse storage. -/
def cfi (twist : Bool) : Sparse.Colored 40 1 :=
  ⟨SparseGraph.ofEdges ((List.finRange 40).flatMap fun i =>
      (List.finRange 40).filterMap fun j =>
        if i < j && ProofProbe.cfiAdjCore twist i.val j.val then some (i, j) else none),
    Coloring.trivial 40⟩

end Hex.GraphIso.SparseProofProbe
