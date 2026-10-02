/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Translated from nauty 2.9.3 nausparse.c, copyright Brendan McKay and
Adolfo Piperno, Apache 2.0.
-/
module

public import HexGraphIso.Nauty.Sparse.Cells

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Arrays retained across refinement calls. Marks use a monotonically
increasing generation; counts are cleared when their cell is first touched. -/
structure Scratch where
  cellstart : Array Nat := #[]
  cellend : Array Nat := #[]
  indexed : Bool := false
  hits : Array Nat := #[]
  marks : Array Nat := #[]
  vmarks : Array Nat := #[]
  stamp : Nat := 0
deriving Inhabited

/-- Allocate scratch arrays for a graph of order `n`. -/
def Scratch.fresh (n : Nat) : Scratch := {
  cellstart := Array.replicate n n, cellend := Array.replicate n 0
  hits := Array.replicate n 0
  marks := Array.replicate n 0, vmarks := Array.replicate n 0 }

/-- The working state of `refine_sg`. Only equality with the current
generation stamp is observed. -/
structure RefineSt (n : Nat) where
  lab : Array Nat
  ptn : Array Nat
  active : VSet n
  queue : Array Nat
  cellstart : Array Nat
  cellend : Array Nat
  indexed : Bool := false
  hits : Array Nat
  marks : Array Nat
  vmarks : Array Nat
  stamp : Nat := 0
  numcells : Nat
  longcode : Nat
deriving Inhabited

namespace RefineSt

/-- Retain the reusable arrays after refinement. -/
def toScratch (s : RefineSt n) : Scratch := {
  cellstart := s.cellstart, cellend := s.cellend, indexed := s.indexed
  hits := s.hits, marks := s.marks
  vmarks := s.vmarks, stamp := s.stamp }

/-- Activate a cell and append its start to the ordered splitter queue. -/
def push (s : RefineSt n) (v : Nat) : RefineSt n :=
  { s with active := s.active.insert v, queue := s.queue.push v }

/-- Incorporate one refinement event into nauty's invariant code. -/
@[inline] def hash (s : RefineSt n) (v : Nat) : RefineSt n :=
  { s with longcode := mash s.longcode v }

end RefineSt

/-- Vertex-to-cell indices, using `n` for singleton vertices, and the last
position of each current cell. Entries at other positions are not read. -/
def indexCells (n : Nat) (lab ptn : Array Nat) (level : Nat)
    (starts ends : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut starts := starts
  let mut ends := ends
  let mut first := 0
  for _ in [0:n] do
    if first >= n then break
    let last := cellEnd ptn level first
    ends := ends.set! first last
    if first < last then
      for i in [first:last + 1] do starts := starts.set! lab[i]! first
    else starts := starts.set! lab[first]! n
    first := last + 1
  return (starts, ends)

end Hex.GraphIso.Nauty.Sparse
