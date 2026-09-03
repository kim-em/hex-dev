/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import NautyFFI

/-! Development-only compatibility adapter for the graph-isomorphism benches. -/

namespace Hex.BenchOracle.Nauty

/-- One canonical-labelling answer from the pinned nauty 2.9.3: the
canonical labelling and the canonical upper-triangle adjacency bits in
row-major order as a `0`/`1` string. -/
structure CanonResult where
  lab : Array Nat
  tri : String
  deriving Repr

/-- Canonicalize one coloured graph through the pinned nauty
comparator. `adj` lists each vertex's adjacency row as a `0`/`1`
string. -/
def canon (n k : Nat) (colors : List Nat) (adj : List String) :
    IO CanonResult := do
  unless colors.length == n do
    throw <| IO.userError s!"nauty canon: expected {n} colours, got {colors.length}"
  let graph : NautyFFI.Graph :=
    { colorCount := k
      colors := colors.toArray
      adjacency := (adj.map fun row =>
        (row.toList.map fun c => c == '1').toArray).toArray }
  let result ← IO.ofExcept (NautyFFI.canonicalize graph)
  let tri := String.ofList <| result.form.adjacency.toList.map fun edge =>
    if edge then '1' else '0'
  return { lab := result.labelling, tri }

end Hex.BenchOracle.Nauty
