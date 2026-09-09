/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexGraphIso.Nauty.Search.Generic
public import HexGraphIso.Limits

public section

/-! State and primitive transitions used by the structured search and its mathematical view. -/

namespace Hex.GraphIso.Nauty

/-- The sentinel code above every real refinement code: nauty's `077777`. -/
@[expose] def codeSentinel : Nat := 0o77777

/-- Search termination and nonlocal return control. -/
abbrev Exit := Generic.Exit

/-- The five node classifications. -/
abbrev Leaf := Generic.Leaf

/-- Search state: what nauty keeps in file-scope variables for the
duration of one `nauty()` call on `n` vertices. Every field is named
for the nauty global or `statsblk` member it mirrors, except `wsCap`,
`genTrace`, and `workperm`.

`lab` and `ptn` are the partition nest: position `i` ends a cell at
level `l` exactly when `ptn[i] ≤ l`. `active` holds the positions of
the cells still to be used as splitters by `refine`. `fixedpts` holds
the vertices individualized on the path from the root to this node.

`firstlab` and `canonlab` are the labellings of the first leaf and of
the best-so-far leaf. `firstcode` and `canoncode` hold the refinement
code of their ancestor at each level, terminated by `codeSentinel`.
`firsttc` holds the target-cell position chosen at each level of the
first path, or `-1` where there is none. `canong` holds the adjacency
rows of the best-so-far leaf, correct in its first `samerows` rows,
and `canonlevel` is that leaf's level.

`eqlevFirst` (`eqlev_first`) and `eqlevCanon` (`eqlev_canon`) are the
deepest levels to which this node's codes agree with the first leaf's
and with the best-so-far leaf's. `compCanon` (`comp_canon`) is `-1`,
`0` or `1` as this node's code at level `eqlevCanon + 1` is less than,
equal to, or greater than the best-so-far leaf's. `gcaFirst`
(`gca_first`) and `gcaCanon` (`gca_canon`) are the levels of the
greatest common ancestors of this node with those two leaves, and
`cosetindex` and `stabvertex` are the vertices individualized there.

`orbits` sends each vertex to the least vertex of its orbit under the
automorphisms found so far. `noncheaplevel` is one past the level of
the deepest ancestor for which `cheapautom` is false. `allsamelevel`
is the level of the least ancestor of the first leaf all of whose
descendant leaves are known to be equivalent. The reusable `workperm`
array holds the scatter permutation prepared at a leaf. Return levels
and short-prune requests are carried by `Exit`.

`numnodes`, `numorbits`, `numgenerators`, `numbadleaves`, `maxlevel`,
`tctotal` and `canupdates` are the members of nauty's `statsblk`: the
nodes visited, the orbits, the generators reported, the leaves that
were neither an automorphism nor an improvement, the greatest depth
reached, the total size of the target cells chosen, and the number of
times the best-so-far leaf was replaced. -/
structure Search (n : Nat) where
  lab : Array Nat
  ptn : Array Nat
  active : VSet n
  orbits : Array Nat
  fixedpts : VSet n := .empty
  /-- nauty's automorphism workspace: stored `(fix, mcr)` pairs of
  discovered automorphisms, read by `shortprune` and `longprune`. Once
  `wsCap` pairs are present the last slot is overwritten instead of a
  new one being added. `wsCap` is 500, the number of pairs that fit in
  the `2 * 500 * m` setwords `densenauty` supplies. -/
  autos : Array (VSet n × VSet n) := #[]
  wsCap : Nat := 500
  firstcode : Array Nat
  canoncode : Array Nat
  firsttc : Array Int
  firstlab : Array Nat
  canonlab : Array Nat
  canong : Array (VSet n)
  samerows : Nat := 0
  compCanon : Int := 0
  eqlevFirst : Nat := 0
  eqlevCanon : Int := -1
  gcaFirst : Nat := 0
  gcaCanon : Nat := 0
  canonlevel : Nat := 0
  noncheaplevel : Nat := 1
  allsamelevel : Nat := 0
  cosetindex : Nat := 0
  stabvertex : Nat := 0
  numnodes : Nat := 0
  tctotal : Nat := 0
  canupdates : Nat := 0
  numorbits : Nat
  numgenerators : Nat := 0
  numbadleaves : Nat := 0
  maxlevel : Nat := 1
  /-- No nauty counterpart: every accepted automorphism kept in full,
  in discovery order, for the certificate producer, alongside the
  bounded `(fix, mcr)` pairs of `autos`. `run` discards it. -/
  genTrace : Array (Array Nat) := #[]
  /-- Scratch permutation, allocated at initialization and filled by leaf comparisons. -/
  workperm : Array Nat
deriving Inhabited

variable {n : Nat}

/-- Record an automorphism pair in the bounded workspace. -/
def pushAuto (st : Search n) (pair : VSet n × VSet n) : Search n :=
  if st.autos.size == st.wsCap then
    { st with autos := st.autos.set! (st.wsCap - 1) pair }
  else
    { st with autos := st.autos.push pair }

/-- Count and refine a node before comparing its refinement code. -/
@[inline] def visit (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    Nat × Nat × Search n := Id.run do
  let mut st := { st with numnodes := st.numnodes + 1 }
  let rs := refine ctx level st.lab st.ptn st.active numcells
  st := { st with lab := rs.lab, ptn := rs.ptn, active := rs.active }
  return (rs.numcells, rs.longcode, st)

/-- Record the refinement code on the first path. -/
@[inline] def recordFirst (level refcode : Nat) (st : Search n) : Search n :=
  { st with firstcode := st.firstcode.set! level refcode }

/-- The comparison bookkeeping of nauty's `othernode` between the
refinement and the target-cell choice: the first-path level-code
comparison and the best-so-far level-code comparison. -/
def compareCodes (level : Nat) (code : Nat) (st : Search n) :
    Search n := Id.run do
  let mut st := st
  if st.eqlevFirst == level - 1 ∧ code == st.firstcode[level]! then
    st := { st with eqlevFirst := level }
  if st.eqlevCanon == Int.ofNat level - 1 then
    if code < st.canoncode[level]! then
      st := { st with compCanon := -1 }
    else if code > st.canoncode[level]! then
      st := { st with compCanon := 1 }
    else
      st := { st with compCanon := 0, eqlevCanon := Int.ofNat level }
  if st.compCanon > (0 : Int) then
    st := { st with canoncode := st.canoncode.set! level code }
  return st

/-- Choose a target cell exactly when children can be required. Only a
canonically smaller off-path node uses the first path's target hint. -/
@[inline] def chooseTarget (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) : Int × VSet n × Nat × Search n := Id.run do
  let mut st := st
  let mut tc : Int := -1
  let mut tcell := VSet.empty
  let mut size := 0
  if (if first then numcells != n
      else numcells < n && (st.eqlevFirst == level || st.compCanon >= 0)) then
    let hinted := !first && st.compCanon < 0
    let hint := if hinted then st.firsttc[level]! else -1
    let (pos, cell, count) := maketargetcell ctx st.lab st.ptn level tcLevel hint
    tc := Int.ofNat pos
    tcell := cell
    size := count
    if hinted && tc != st.firsttc[level]! then
      st := { st with eqlevFirst := level - 1 }
    st := { st with tctotal := st.tctotal + size }
  if first then
    st := { st with firsttc := st.firsttc.set! level tc }
  return (tc, tcell, size, st)

/-- nauty's `firstterminal`: install the first leaf as both the first-path
data and the initial best-so-far leaf. -/
def firstterminal (level : Nat) (st : Search n) : Search n := Id.run do
  let mut st := st
  st := { st with
    maxlevel := level
    gcaFirst := level, allsamelevel := level, eqlevFirst := level
    firstcode := st.firstcode.set! (level + 1) codeSentinel
    firsttc := st.firsttc.set! (level + 1) (-1)
    firstlab := st.lab
    canonlevel := level, eqlevCanon := Int.ofNat level, gcaCanon := level
    compCanon := 0
    samerows := 0
    canonlab := st.lab
    canupdates := 1 }
  let mut canoncode := st.canoncode
  for i in [0 : level + 1] do
    canoncode := canoncode.set! i st.firstcode[i]!
  canoncode := canoncode.set! (level + 1) codeSentinel
  return { st with canoncode }

/-- Scatter the current labelling through a reference labelling. Detach
the scratch field while filling it so each element update consumes just
the array, rather than reconstructing the search record. -/
@[inline] def scatter (refLab : Array Nat) (st : Search n) : Search n := Id.run do
  let mut workperm := st.workperm
  let st := { st with workperm := #[] }
  for i in [0 : n] do
    workperm := workperm.set! refLab[i]! st.lab[i]!
  return { st with workperm }

/-- Classify an off-path node, constructing its permutation in the
scratch array and comparing canonical rows only after tied levels. -/
def classify (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    Leaf × Search n := Id.run do
  let mut st := st
  if st.eqlevFirst != level && st.compCanon < 0 then
    return (.bad, st)
  if numcells != n then
    return (.internal, st)
  if st.eqlevFirst == level then
    st := scatter st.firstlab st
    if st.gcaFirst >= st.noncheaplevel || isautom ctx st.workperm then
      return (.autoFirst, st)
  let mut sr := 0
  if st.compCanon == 0 then
    if level < st.canonlevel then
      st := { st with compCanon := 1 }
    else
      st := { st with
        canong := updatecan ctx st.canong st.canonlab st.samerows
        samerows := n }
      let (c, s) := testcanlab ctx st.canong st.lab
      st := { st with compCanon := c }
      sr := s
  if st.compCanon == 0 then
    st := scatter st.canonlab st
    return (.autoCanon, st)
  else if st.compCanon > 0 then
    return (.better sr, st)
  else
    return (.bad, st)

/-- Record a permutation and its workspace pair, then join its orbits.
The caller decides whether it counts as a new generator. -/
@[inline] def admit (st : Search n) : Search n := Id.run do
  let mut st := st
  st := { st with genTrace := st.genTrace.push st.workperm }
  st := pushAuto st (fmperm st.workperm n)
  let (orbits, numorbits) := orbjoin st.orbits st.workperm n
  return { st with orbits, numorbits }

/-- Install a better leaf, retaining its already compared row prefix. -/
@[inline] def install (level sr : Nat) (st : Search n) : Search n :=
  { st with
    canupdates := st.canupdates + 1
    canonlab := st.lab
    canonlevel := level, eqlevCanon := Int.ofNat level, gcaCanon := level
    compCanon := 0
    canoncode := st.canoncode.set! (level + 1) codeSentinel
    samerows := sr }

/-- Return past a bad or newly installed leaf. The all-same level limits
the return, and the noncheap level can extend it. -/
def pruneReturn (level : Nat) (st : Search n) : Exit × Search n := Id.run do
  let mut st := st
  let ispruneok := level != st.noncheaplevel
  if ispruneok then
    st := pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)
  let save : Int :=
    if Int.ofNat st.allsamelevel > st.eqlevCanon then
      Int.ofNat st.allsamelevel - 1
    else st.eqlevCanon
  let newlevel : Int :=
    if Int.ofNat st.noncheaplevel <= save then
      Int.ofNat st.noncheaplevel - 1
    else save
  return (.unwind newlevel.toNat (ispruneok && newlevel != Int.ofNat st.gcaFirst), st)

/-- Act on the five classifications. Code 2 without an orbit change
still records its permutation and requests a short prune when needed. -/
def leafExit (leaf : Leaf) (level : Nat) (st : Search n) : Exit × Search n := Id.run do
  let mut st := st
  if leaf != .internal && level > st.maxlevel then
    st := { st with maxlevel := level }
  match leaf with
  | .internal => return (.done, st)
  | .autoFirst =>
    st := admit st
    st := { st with numgenerators := st.numgenerators + 1 }
    return (.unwind st.gcaFirst false, st)
  | .autoCanon =>
    let save := st.numorbits
    st := admit st
    if st.numorbits == save then
      return (.unwind st.gcaCanon (st.gcaCanon != st.gcaFirst), st)
    st := { st with numgenerators := st.numgenerators + 1 }
    if st.orbits[st.cosetindex]! < st.cosetindex then
      return (.unwind st.gcaFirst false, st)
    return (.unwind st.gcaCanon (st.gcaCanon != st.gcaFirst), st)
  | .better sr => return pruneReturn level (install level sr st)
  | .bad => return pruneReturn level { st with numbadleaves := st.numbadleaves + 1 }

/-- Update the deepest noncheap level before descending. -/
@[inline] def cheapCheck (first : Bool) (level : Nat) (st : Search n) : Search n :=
  if (!first || st.noncheaplevel >= level) && !cheapautom st.ptn level n then
    { st with noncheaplevel := level + 1 }
  else st

/-- Individualize a child vertex, recording every first-path coset index. -/
@[inline] def child (first : Bool) (level tc tv : Nat) (st : Search n) : Search n :=
  let (lab, ptn, active) := breakout n st.lab st.ptn (level + 1) tc tv
  let st := { st with lab, ptn, active, fixedpts := st.fixedpts.insert tv }
  if first then { st with cosetindex := tv } else st

/-- After the leftmost child, record its greatest common ancestor and
the vertex fixed by the generators subsequently reported there. -/
@[inline] def afterChildFirst (level tv1 : Nat) (st : Search n) : Search n :=
  { st with gcaFirst := level, stabvertex := tv1 }

/-- Decrement the all-same level only after a complete first-path sweep. -/
@[inline] def afterSweep (first : Bool) (level tcellsize index : Nat)
    (st : Search n) : Search n :=
  if first && tcellsize == index && st.allsamelevel == level + 1 then
    { st with allsamelevel := st.allsamelevel - 1 }
  else st

/-- Reopen the partition below the receiving level, as in nauty’s `recover`. -/
@[inline] def recoverPtn (inf level : Nat) (st : Search n) : Search n := Id.run do
  let mut ptn := st.ptn
  for i in [0 : n] do
    if ptn[i]! > level then
      ptn := ptn.set! i inf
  return { st with ptn }

/-- Clamp the four level counters in nauty’s order. Equality in the last clamp resets the
comparison with the canonical code. -/
@[inline] def recoverLevels (level : Nat) (st : Search n) : Search n := Id.run do
  let mut st := st
  if level < st.noncheaplevel then
    st := { st with noncheaplevel := level + 1 }
  if level < st.eqlevFirst then
    st := { st with eqlevFirst := level }
  if level < st.gcaCanon then
    st := { st with gcaCanon := level }
  if Int.ofNat level <= st.eqlevCanon then
    st := { st with eqlevCanon := Int.ofNat level, compCanon := 0 }
  return st

/-- nauty's `longprune`: intersect the target cell with the minimum-cell
representatives of every stored automorphism fixing all currently fixed
points. -/
def longprune (tcell fixedpts : VSet n)
    (autos : Array (VSet n × VSet n)) : VSet n :=
  autos.foldl
    (fun tcell (fix, mcr) =>
      if fixedpts.subset fix then tcell.inter mcr else tcell)
    tcell

/-- Intersect with the most recently written workspace pair, as in nauty’s `shortprune`. -/
@[inline] def shortprune (tcell : VSet n) (st : Search n) : VSet n :=
  match st.autos.back? with
  | some (_, mcr) => tcell.inter mcr
  | none => tcell

/-- Restore the partition and comparison levels after a child returns. -/
@[inline] def recover (n inf level : Nat) (st : Search n) : Search n :=
  recoverLevels level (recoverPtn inf level st)

/-- Recovery consists of the partition rescan followed by the level clamps. -/
theorem recover_eq (inf level : Nat) (st : Search n) :
    recoverLevels level (recoverPtn inf level st) = recover n inf level st := by
  simp only [recover]

/-- The result of a canonical search on `n` vertices: the canonical
labelling `canonlab` and the adjacency rows `canong` under it, together
with the statistics nauty reports in its `statsblk`. Those are the
nodes visited (`numnodes`), the orbits and generators of the
automorphism group (`numorbits`, `numgenerators`), the leaves that were
neither an automorphism nor an improvement (`numbadleaves`), the
greatest depth reached (`maxlevel`), the total size of the target cells
chosen (`tctotal`), and the number of times the best-so-far leaf was
replaced (`canupdates`). -/
structure RunResult (n : Nat) where
  canonlab : Array Nat
  canong : Array (VSet n)
  numnodes : Nat
  numorbits : Nat
  numgenerators : Nat
  numbadleaves : Nat
  maxlevel : Nat
  tctotal : Nat
  canupdates : Nat
deriving Inhabited, Repr

/-- The initial `ptn` array: `inf` everywhere except `0` at each cell
end. -/
@[expose] def initPtn (n inf : Nat) (cellEnds : List Nat) : Array Nat :=
  cellEnds.foldl (fun ptn e => ptn.set! e 0) (Array.replicate n inf)

/-- The initial active set: one bit per cell start. -/
@[expose] def initActive (n : Nat) (cellEnds : List Nat) : VSet n :=
  (cellEnds.foldl (fun (p : VSet n × Nat) e => (p.1.insert p.2, e + 1))
    (.empty, 0)).1

/-- A traced run: the search result, every accepted automorphism in
discovery order, and the best path's refinement codes. This is the
trace the certificate producer reads. The search's `canoncode` array
and the certificate checker use the same code coordinates (each child
call is seeded with the parent's recomputed cell count), so the codes
are read off the final state directly. -/
structure TraceRun (n : Nat) where
  result : RunResult n
  autos : Array (Array Nat)
  /-- The best leaf's refinement codes at levels `1 .. canonlevel`,
  without the sentinel. -/
  bestCodes : List Nat

variable {k : Nat}

/-- The adjacency row of one vertex of a coloured graph. -/
@[expose] def rowOf (G : Colored n k) (i : Nat) : VSet n :=
  VSet.ofFn fun j =>
    if h : i < n ∧ j < n then G.graph.adj ⟨i, h.1⟩ ⟨j, h.2⟩ else false

theorem mem_rowOf (G : Colored n k) (i j : Nat) :
    (rowOf G i).mem j =
      if h : i < n ∧ j < n then G.graph.adj ⟨i, h.1⟩ ⟨j, h.2⟩ else false := by
  rw [rowOf, VSet.mem_ofFn]
  rcases Decidable.em (i < n ∧ j < n) with h | h
  · rw [dite_eq_left h, show decide (j < n) = true by simp [h.2]]
    rfl
  · rw [dite_eq_right h, Bool.and_false]

/-- The adjacency rows of a coloured graph. -/
@[expose] def rowsOf (G : Colored n k) : Array (VSet n) :=
  ((List.range n).map (rowOf G)).toArray

/-- The vertices of one colour, in increasing order. -/
@[expose] def colorClass (G : Colored n k) (c : Nat) : List Nat :=
  (List.range n).filter fun v =>
    if h : v < n ∧ c < k then
      G.coloring.cells[(⟨v, h.1⟩ : Fin n)] == ⟨c, h.2⟩
    else
      false

/-- The initial `lab` (vertices by increasing colour, then vertex) and the
cell end positions of a coloured graph. -/
@[expose] def initialPartition (G : Colored n k) : Array Nat × List Nat :=
  let classes := (List.range k).map (colorClass G)
  let lab := classes.flatMap id
  let ends := (classes.foldl
    (fun (acc : List Nat × Nat) cl =>
      if cl.isEmpty then acc
      else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length))
    ([], 0)).1
  (lab.toArray, ends.reverse)

end Hex.GraphIso.Nauty
