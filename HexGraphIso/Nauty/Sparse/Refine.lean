/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Translated from nauty 2.9.3 nausparse.c, copyright Brendan McKay and
Adolfo Piperno, Apache 2.0.
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.Counts

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A singleton splitter: untouched vertices keep their order and touched
vertices are written in reverse order, as in `HITS[--k]`. -/
def splitSingleton (g : Graph n) (level split : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let stamp := s.stamp + 1
  let mut marks := s.marks
  let mut touched := #[]
  let mut hitVertices := s.vmarks
  -- The neighbour loop borrows `s` for cell indices. Release its aliases
  -- to the two arrays being updated, so their first writes can be in place.
  let s := { s with marks := #[], vmarks := #[] }
  let vertex := s.lab[split]!
  for e in [g.offsets[vertex]!:g.offsets[vertex + 1]!] do
    let j := g.neighbor e
    hitVertices := hitVertices.set! j stamp
    let k := s.cellstart[j]!
    if k != n && marks[k]! != stamp then
      marks := marks.set! k stamp
      touched := touched.push k
  touched := sortCells touched
  let mut s := { s with marks, vmarks := hitVertices, stamp }
  s := s.hash touched.size
  for first in touched do
    s := s.hash first
    let last := s.cellend[first]! + 1
    let mut lab := s.lab
    s := { s with lab := #[] }
    let mut v2 := first
    let mut hit := #[]
    for j in [first:last] do
      let v := lab[j]!
      if s.vmarks[v]! == stamp then hit := hit.push v
      else
        lab := lab.set! v2 v
        v2 := v2 + 1
    s := s.hash hit.size
    let mut starts := s.cellstart
    s := { s with cellstart := #[] }
    let mut v3 := v2
    for t in [0:hit.size] do
      let j := hit[hit.size - 1 - t]!
      starts := starts.set! j v2
      lab := lab.set! v3 j
      v3 := v3 + 1
    if v2 != v3 && v2 != first then
      if v2 == first + 1 then starts := starts.set! lab[first]! n
      if v3 == v2 + 1 then starts := starts.set! lab[v2]! n
      s := { s with
        numcells := s.numcells + 1, ptn := s.ptn.set! (v2 - 1) level
        cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1) }
      s := s.hash v2
      if v2 - first <= v3 - v2 && !s.active.mem first then s := s.push first
      else s := s.push v2
    s := { s with lab, cellstart := starts }
  return s

/-- Count only vertices in touched nontrivial cells. Rows of `hits` are
cleared on first touch, without a full vertex scan for each splitter. -/
def splitNontrivial (g : Graph n) (level split : Nat) (s : RefineSt n) : RefineSt n := Id.run do
  let stamp := s.stamp + 1
  let mut marks := s.marks
  let mut hits := s.hits
  let s := { s with marks := #[], hits := #[] }
  let mut touched := #[]
  let last := s.cellend[split]! + 1
  for i in [split:last] do
    let vertex := s.lab[i]!
    for e in [g.offsets[vertex]!:g.offsets[vertex + 1]!] do
      let j := g.neighbor e
      let k := s.cellstart[j]!
      if k != n then
        if marks[k]! != stamp then
          marks := marks.set! k stamp
          touched := touched.push k
          for l in [k:s.cellend[k]! + 1] do
            hits := hits.set! s.lab[l]! 0
        hits := hits.set! j (hits[j]! + 1)
  touched := sortCells touched
  let mut s := { s with marks, hits, stamp }
  s := s.hash touched.size
  for first in touched do s := splitCounts level first false s
  return s

/-- `refine_sg`, including its shallow distance split and preference for
singleton splitters among the first ten active entries. -/
def refineWith (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch) : RefineSt n := Id.run do
  -- Walk the packed set in the same ascending order as nauty's initial
  -- active scan, without constructing and filtering a list of all vertices.
  let mut initialQueue := #[]
  let mut next := active.nextElem none
  for _ in [0:n] do
    let some i := next | break
    initialQueue := initialQueue.push i
    next := active.nextElem (some i)
  let mut s : RefineSt n := {
    cellstart := scratch.cellstart, cellend := scratch.cellend, indexed := false
    hits := scratch.hits, marks := scratch.marks
    vmarks := scratch.vmarks, stamp := scratch.stamp
    lab, ptn, active, queue := initialQueue
    numcells, longcode := numcells }
  if initialQueue.isEmpty then return { s with longcode := cleanup s.longcode }
  let (starts, ends) := indexCells n lab ptn level s.cellstart s.cellend
  s := { s with cellstart := starts, cellend := ends, indexed := true }
  if level <= 2 && initialQueue.size == 1 && ptn[initialQueue[0]!]! <= level && numcells <= n / 8 then
    let split := initialQueue[0]!
    s := { s with
      queue := #[], active := s.active.erase split
      hits := distvals g lab[split]! }
    let mut first := 0
    for _ in [0:n] do
      if first >= n then break
      let last := s.cellend[first]!
      if first < last then s := splitCounts level first true s
      first := last + 1
  -- A split adds no more queue entries than new cells. With at most n
  -- initial active entries bounded by the initial cell count, n iterations
  -- suffice before the queue empties.
  for _ in [0:n] do
    if s.queue.isEmpty || s.numcells >= n then break
    let mut pos := s.queue.size - 1
    for i in [0:min s.queue.size 10] do
      if s.ptn[s.queue[i]!]! <= level then
        pos := i
        break
    let split := s.queue[pos]!
    let queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop
    s := { s with queue, active := s.active.erase split }
    s := s.hash split
    if s.ptn[split]! <= level then s := splitSingleton g level split s
    else s := splitNontrivial g level split s
  return { s with longcode := cleanup (mash s.longcode s.numcells) }

/-- Standalone refinement with freshly initialized scratch storage. -/
def refine (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) : RefineSt n :=
  refineWith g level lab ptn active numcells (.fresh n)

end Hex.GraphIso.Nauty.Sparse
