/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Colored
public import HexGraphIso.Nauty.Sparse.Search

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Run the sparse search from a native coloured graph. -/
def runColored (G : GraphIso.Sparse.Colored n k) : State n :=
  let (lab, ends) := initialPartitionWith n k G.coloring.cells.toArray Fin.val
  run (Graph.ofGraph G.graph) lab ends

/-- Diagnostic checked canonical graph and label. `Sparse.Result` proves
unconditional success; the total API extracts this same result. -/
def searchResult? (G : GraphIso.Sparse.Colored n k) :
    Option (GraphIso.Sparse.CanonResult n k) := do
  let l ← Label.ofArray? n (runColored G).canonlab
  return ⟨G.relabel l, l⟩

theorem searchResult?_relabel {G : GraphIso.Sparse.Colored n k}
    {r : GraphIso.Sparse.CanonResult n k} (h : searchResult? G = some r) :
    r.form = G.relabel r.label := by
  unfold searchResult? at h
  cases he : Label.ofArray? n (runColored G).canonlab <;> simp [he] at h
  subst r
  rfl

end Hex.GraphIso.Nauty.Sparse
