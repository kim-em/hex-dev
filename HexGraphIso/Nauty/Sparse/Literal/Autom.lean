/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Literal.Range
public import HexGraphIso.Nauty.Sparse.Autom

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

/-- The sparse automorphism test with exported range iteration. Degrees,
generation marks, and the fixed-vertex shortcut are the production operations. -/
def isautom (g : Graph n) (p : Array Nat) : Bool := Id.run do
  let mut marks := Array.replicate n 0
  for i in range 0 n do
    if p[i]! != i then
      let pi := p[i]!
      if g.degree pi != g.degree i then return false
      let stamp := i + 1
      for j in range g.offsets[i]! g.offsets[i + 1]! do
        marks := marks.set! p[g.neighbor j]! stamp
      for j in range g.offsets[pi]! g.offsets[pi + 1]! do
        if marks[g.neighbor j]! != stamp then return false
  return true

theorem isautom_eq : @isautom = @Sparse.isautom := by
  funext n g p
  simp only [isautom, Sparse.isautom, range_forIn]

end Hex.GraphIso.Nauty.Sparse.Literal
