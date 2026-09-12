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

def toScratch (s : RefineSt n) : Scratch := {
  cellstart := s.cellstart, cellend := s.cellend, indexed := s.indexed
  hits := s.hits, marks := s.marks
  vmarks := s.vmarks, stamp := s.stamp }

def push (s : RefineSt n) (v : Nat) : RefineSt n :=
  { s with active := s.active.insert v, queue := s.queue.push v }

def hash (s : RefineSt n) (v : Nat) : RefineSt n :=
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

/-- Divide one cell by counts or distances. The first two minimum
fragments use nauty's three-way insertion; later fragments use its exact
indirect sort. `distance` selects the distinct distance-branch code updates. -/
def splitCounts (level first : Nat) (distance : Bool) (s : RefineSt n) : RefineSt n := Id.run do
  let last := s.cellend[first]! + 1
  let mut s := s.hash first
  let mut w1 := s.hits[s.lab[first]!]!
  let mut v2 := first + 1
  for _ in [first + 1:last] do
    if s.hits[s.lab[v2]!]! != w1 then break
    v2 := v2 + 1
  if v2 == last then return s
  let mut w2 := n + 2
  let mut v3 := v2
  let mut lab := s.lab
  s := { s with lab := #[] }
  for j in [v2:last] do
    let lj := lab[j]!
    let w3 := s.hits[lj]!
    if w3 == w1 then
      lab := lab.set! j lab[v3]!
      lab := lab.set! v3 lab[v2]!
      lab := lab.set! v2 lj
      v2 := v2 + 1
      v3 := v3 + 1
    else if w3 == w2 then
      lab := lab.set! j lab[v3]!
      lab := lab.set! v3 lj
      v3 := v3 + 1
    else if w3 < w1 then
      lab := lab.set! j lab[v2]!
      lab := lab.set! v2 lab[first]!
      lab := lab.set! first lj
      v3 := v2 + 1
      v2 := first + 1
      w2 := w1
      w1 := w3
    else if w3 < w2 then
      lab := lab.set! j lab[v2]!
      lab := lab.set! v2 lj
      v3 := v2 + 1
      w2 := w3
  s := { s with lab }
  s := (s.hash (if distance then w2 else w1)).hash v2
  if last == v2 then return s
  let mut starts := s.cellstart
  s := { s with cellstart := #[] }
  if v2 == first + 1 then starts := starts.set! s.lab[first]! n
  if v3 == v2 + 1 then starts := starts.set! s.lab[v2]! n
  else
    for k in [v2:v3] do starts := starts.set! s.lab[k]! v2
  s := { s with
    cellstart := starts, numcells := s.numcells + 1
    cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    ptn := s.ptn.set! (v2 - 1) level }
  if last == v3 then
    if v2 - first <= v3 - v2 && !s.active.mem first then return s.push first
    else return s.push v2
  if !distance then s := s.hash v3
  s := { s with lab := Sort.indirect s.lab s.hits v3 (last - v3) }
  s := s.push v2
  let mut bigpos : Option Nat := none
  let mut bigsize := v2 - first
  if v2 - first < v3 - v2 then
    bigpos := some (s.queue.size - 1)
    bigsize := v3 - v2
    if !distance then s := s.hash bigsize
  let mut k := v3 - 1
  for _ in [v3:last] do
    if k >= last - 1 then break
    s := { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 }
    if distance then s := s.hash k
    let l := k + 1
    s := s.push l
    let w3 := s.hits[s.lab[l]!]!
    if !distance then s := s.hash w3
    k := l
    for _ in [l:last - 1] do
      if s.hits[s.lab[k + 1]!]! != w3 then break
      s := { s with cellstart := s.cellstart.set! s.lab[k + 1]! l }
      k := k + 1
    let size := k - l + 1
    s := { s with cellend := s.cellend.set! l k }
    if size == 1 then
      s := { s with cellstart := s.cellstart.set! s.lab[l]! n }
    else
      s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
      if size > bigsize then
        bigsize := size
        bigpos := some (s.queue.size - 1)
  if let some pos := bigpos then
    if !s.active.mem first then
      if distance then s := s.hash pos
      s := { s with
        active := (s.active.erase s.queue[pos]!).insert first
        queue := s.queue.set! pos first }
  return s

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
