/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexGraphIso.Nauty.Search.Refine
public import HexGraphIso.Limits

public section

/-!
The canonical search of nauty 2.9.3 dense basic mode, transcribed from
`nauty.c` with the pinned dense options: `getcanon = 1`, undirected,
caller partition, `tc_level = 100`, no vertex invariant, no Schreier
machinery, and no user callbacks. `nauty.c` is normative for every
detail: the first-path bookkeeping, the level-code and canonical
comparisons, the five-way leaf classification, automorphism recording
with its 500-entry workspace overwrite rule, orbit and short/long
pruning, and the return-level unwinding protocol.

The search tree is walked by four mutually recursive functions.
`firstPathNode` is nauty's `firstpathnode` and `firstChildLoop` is its
loop over the target cell: together they descend the leftmost path and
install its leaf as both the first leaf and the initial best-so-far
leaf. `otherNode` is nauty's `othernode` and `otherChildLoop` is its
loop over the target cell: together they visit every node off that
path. Each of the four returns the level the search is to unwind to,
and each takes a fuel argument in place of the unbounded C recursion.

One `SearchSt` record carries what nauty keeps in file-scope variables
for the duration of a `nauty()` call: the partition `(lab, ptn)` with
its active cells and the individualized vertices, the first leaf and
the best-so-far leaf with their labellings, adjacency rows and
refinement codes, the level counters saying how far the current node
still agrees with each of those two leaves, the orbit array, the
bounded workspace of automorphism `(fix, mcr)` pairs that
`shortprune` and `longprune` read, and the counters nauty returns in
its `statsblk`. `runTraced` builds the initial state, calls
`firstPathNode` at level 1, and reads the canonical labelling and rows
out of the final state.

Conformance testing establishes agreement with the external nauty
binary, and agreement with the proven reference implementation on the
isomorphism verdict. `HexGraphIso.Kernel.CheckKey` replays this
module's output before a proof depends on it.
-/

namespace Hex.GraphIso.Nauty

/-- The sentinel code above every real refinement code: nauty's `077777`. -/
@[expose] def codeSentinel : Nat := 0o77777

/-- Search state: what nauty keeps in file-scope variables for the
duration of one `nauty()` call on `n` vertices. Every field is named
for the nauty global or `statsblk` member it mirrors, except `wsCap`
and `genTrace`.

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
descendant leaves are known to be equivalent. `needshortprune` records
that the parent's target cell is to be pruned by `shortprune` on
return.

`numnodes`, `numorbits`, `numgenerators`, `numbadleaves`, `maxlevel`,
`tctotal` and `canupdates` are the members of nauty's `statsblk`: the
nodes visited, the orbits, the generators reported, the leaves that
were neither an automorphism nor an improvement, the greatest depth
reached, the total size of the target cells chosen, and the number of
times the best-so-far leaf was replaced. -/
structure SearchSt (n : Nat) where
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
  needshortprune : Bool := false
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
deriving Inhabited

variable {n : Nat}

/-- Record an automorphism pair in the bounded workspace. -/
def pushAuto (st : SearchSt n) (pair : VSet n × VSet n) : SearchSt n :=
  if st.autos.size == st.wsCap then
    { st with autos := st.autos.set! (st.wsCap - 1) pair }
  else
    { st with autos := st.autos.push pair }

/-- nauty's `recover`: reopen the partition below `level` and pull the
level bookkeeping back. -/
def recover (n inf : Nat) (level : Nat) (st : SearchSt n) : SearchSt n := Id.run do
  let mut ptn := st.ptn
  for i in [0 : n] do
    if ptn[i]! > level then
      ptn := ptn.set! i inf
  let mut st := { st with ptn }
  if level < st.noncheaplevel then
    st := { st with noncheaplevel := level + 1 }
  if level < st.eqlevFirst then
    st := { st with eqlevFirst := level }
  if level < st.gcaCanon then
    st := { st with gcaCanon := level }
  if Int.ofNat level ≤ st.eqlevCanon then
    st := { st with eqlevCanon := Int.ofNat level, compCanon := 0 }
  return st

/-- nauty's `firstterminal`: install the first leaf as both the first-path
data and the initial best-so-far leaf. -/
def firstterminal (level : Nat) (st : SearchSt n) : SearchSt n := Id.run do
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

/-- nauty's `processnode`: classify a non-first-path node and act on it.
Returns the level to return to. -/
def processnode (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    Int × SearchSt n := Id.run do
  let n := n
  let mut st := st
  let mut code := 0
  let mut workperm : Array Nat := .replicate n 0
  let mut sr := 0
  if st.eqlevFirst ≠ level ∧ st.compCanon < 0 then
    code := 4
  else if numcells == n then
    if st.eqlevFirst == level &&
        st.firstcode[level + 1]! == codeSentinel then
      for i in [0 : n] do
        workperm := workperm.set! st.firstlab[i]! st.lab[i]!
      if isautom ctx workperm then
        code := 1
    if code == 0 then
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
        for i in [0 : n] do
          workperm := workperm.set! st.canonlab[i]! st.lab[i]!
        code := 2
      else if st.compCanon > 0 then
        code := 3
      else
        code := 4
  if code ≠ 0 ∧ level > st.maxlevel then
    st := { st with maxlevel := level }
  match code with
  | 0 => return (Int.ofNat level, st)
  | 1 =>
    st := { st with genTrace := st.genTrace.push workperm }
    st := pushAuto st (fmperm workperm n)
    let (orbits, numorbits) := orbjoin st.orbits workperm n
    st := { st with orbits := orbits, numorbits := numorbits, numgenerators := st.numgenerators + 1 }
    return (Int.ofNat st.gcaFirst, st)
  | 2 =>
    st := { st with genTrace := st.genTrace.push workperm }
    st := pushAuto st (fmperm workperm n)
    let save := st.numorbits
    let (orbits, numorbits) := orbjoin st.orbits workperm n
    st := { st with orbits := orbits, numorbits := numorbits }
    if numorbits == save then
      if st.gcaCanon ≠ st.gcaFirst then
        st := { st with needshortprune := true }
      return (Int.ofNat st.gcaCanon, st)
    st := { st with numgenerators := st.numgenerators + 1 }
    if st.orbits[st.cosetindex]! < st.cosetindex then
      return (Int.ofNat st.gcaFirst, st)
    if st.gcaCanon ≠ st.gcaFirst then
      st := { st with needshortprune := true }
    return (Int.ofNat st.gcaCanon, st)
  | _ => -- cases 3 and 4 share their tail
    if code == 3 then
      st := { st with
        canupdates := st.canupdates + 1
        canonlab := st.lab
        canonlevel := level, eqlevCanon := Int.ofNat level, gcaCanon := level
        compCanon := 0
        canoncode := st.canoncode.set! (level + 1) codeSentinel
        samerows := sr }
    else
      st := { st with numbadleaves := st.numbadleaves + 1 }
    let mut ispruneok := false
    if level ≠ st.noncheaplevel then
      ispruneok := true
      st := pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)
    let save : Int :=
      if Int.ofNat st.allsamelevel > st.eqlevCanon then
        Int.ofNat st.allsamelevel - 1
      else
        st.eqlevCanon
    let newlevel : Int :=
      if Int.ofNat st.noncheaplevel ≤ save then
        Int.ofNat st.noncheaplevel - 1
      else
        save
    if ispruneok ∧ newlevel ≠ Int.ofNat st.gcaFirst then
      st := { st with needshortprune := true }
    return (newlevel, st)

/-- nauty's `longprune`: intersect the target cell with the minimum-cell
representatives of every stored automorphism fixing all currently fixed
points. -/
def longprune (tcell fixedpts : VSet n)
    (autos : Array (VSet n × VSet n)) : VSet n :=
  autos.foldl
    (fun tcell (fix, mcr) =>
      if fixedpts.subset fix then tcell.inter mcr else tcell)
    tcell

/-- nauty's `shortprune`: intersect the target cell with the `mcr` set of
the most recently stored automorphism. The store is never empty when this
is called. An empty store leaves the cell unchanged. -/
def shortprune (tcell : VSet n) (st : SearchSt n) : VSet n :=
  match st.autos.back? with
  | some (_, mcr) => tcell.inter mcr
  | none => tcell

set_option maxHeartbeats 800000 in
mutual

/-- nauty's `firstpathnode`: produce a node on the leftmost path. Returns
the level to return to. -/
@[expose] def firstPathNode (ctx : Ctx n) (inf tcLevel : Nat) (fuel : Nat)
    (level numcells : Nat) (st : SearchSt n) : Int × SearchSt n :=
  match fuel with
  | 0 => (0, st)
  | fuel + 1 => Id.run do
    let mut st := { st with numnodes := st.numnodes + 1 }
    let rs := refine ctx level st.lab st.ptn st.active numcells
    st := { st with lab := rs.lab, ptn := rs.ptn, active := rs.active }
    let numcells := rs.numcells
    let refcode := rs.longcode
    st := { st with firstcode := st.firstcode.set! level refcode }
    let mut tc : Int := -1
    let mut tcell : VSet n := .empty
    let mut tcellsize : Nat := 0
    if numcells ≠ n then
      let (tcPos, cellSet, size) := maketargetcell ctx st.lab st.ptn level tcLevel (-1)
      tc := Int.ofNat tcPos
      tcell := cellSet
      tcellsize := size
      st := { st with tctotal := st.tctotal + size }
    st := { st with firsttc := st.firsttc.set! level tc }
    if numcells == n then
      st := firstterminal level st
      return (Int.ofNat level - 1, st)
    if st.noncheaplevel ≥ level ∧ ¬ cheapautom st.ptn level n then
      st := { st with noncheaplevel := level + 1 }
    let tv1 := (tcell.nextElem none).getD 0
    let (r, index, st') :=
      firstChildLoop ctx inf tcLevel fuel (n + 1) level numcells (tc.toNat) tv1
        (tcell.nextElem none) tcell 0 st
    st := st'
    match r with
    | some rtn => return (rtn, st)
    | none =>
      if tcellsize == index ∧ st.allsamelevel == level + 1 then
        st := { st with allsamelevel := st.allsamelevel - 1 }
      return (Int.ofNat level - 1, st)
termination_by (fuel, 0, 0)

/-- The child loop of `firstpathnode`: individualize each surviving
target-cell vertex in ascending order, tracking the orbit index count.
Returns `some rtn` for an early unwind. -/
@[expose] def firstChildLoop (ctx : Ctx n) (inf tcLevel : Nat) (fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell0 : VSet n)
    (index0 : Nat) (st0 : SearchSt n) : Option Int × Nat × SearchSt n :=
  match cfuel, tv? with
  | 0, _ => (none, index0, st0)
  | _, none => (none, index0, st0)
  | cfuel + 1, some tv => Id.run do
    let mut st := st0
    let mut tcell := tcell0
    let mut index := index0
    if st.orbits[tv]! == tv then
      let (lab, ptn, active) := breakout n st.lab st.ptn (level + 1) tc tv
      st := { st with
        lab := lab
        ptn := ptn
        active := active
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv }
      let mut rtnlevel : Int := 0
      if tv == tv1 then
        let (r, st') := firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1) st
        rtnlevel := r
        st := { st' with gcaFirst := level, stabvertex := tv1 }
      else
        let (r, st') := otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) st
        rtnlevel := r
        st := st'
      st := { st with fixedpts := st.fixedpts.erase tv }
      if rtnlevel < Int.ofNat level then
        return (some rtnlevel, index, st)
      if st.needshortprune then
        st := { st with needshortprune := false }
        tcell := shortprune tcell st
      st := recover n inf level st
    if st.orbits[tv]! == tv1 then
      index := index + 1
    return firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
      (tcell.nextElem (some tv)) tcell index st
termination_by (fuel, 1, cfuel)

/-- The comparison bookkeeping of nauty's `othernode` between the
refinement and the target-cell choice: the first-path level-code
comparison and the best-so-far level-code comparison. -/
def otherNodePrep (level : Nat) (code : Nat) (st : SearchSt n) :
    SearchSt n := Id.run do
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

/-- nauty's `othernode`: produce a node off the leftmost path. Returns the
level to return to. -/
@[expose] def otherNode (ctx : Ctx n) (inf tcLevel : Nat) (fuel : Nat)
    (level numcells : Nat) (st : SearchSt n) : Int × SearchSt n :=
  match fuel with
  | 0 => (0, st)
  | fuel + 1 => Id.run do
    let mut st := { st with numnodes := st.numnodes + 1 }
    let rs := refine ctx level st.lab st.ptn st.active numcells
    st := { st with lab := rs.lab, ptn := rs.ptn, active := rs.active }
    let numcells := rs.numcells
    let code := rs.longcode
    st := otherNodePrep level code st
    let mut tc : Int := -1
    let mut tcell : VSet n := .empty
    if numcells < n ∧ (st.eqlevFirst == level ∨ st.compCanon ≥ (0 : Int)) then
      if st.compCanon < (0 : Int) then
        let (tcPos, cellSet, size) :=
          maketargetcell ctx st.lab st.ptn level tcLevel st.firsttc[level]!
        tc := Int.ofNat tcPos
        tcell := cellSet
        st := { st with tctotal := st.tctotal + size }
        if Int.ofNat tcPos ≠ st.firsttc[level]! then
          st := { st with eqlevFirst := level - 1 }
      else
        let (tcPos, cellSet, size) :=
          maketargetcell ctx st.lab st.ptn level tcLevel (-1)
        tc := Int.ofNat tcPos
        tcell := cellSet
        st := { st with tctotal := st.tctotal + size }
    let (rtnlevel, st') := processnode ctx level numcells st
    st := st'
    if rtnlevel < Int.ofNat level then
      return (rtnlevel, st)
    if st.needshortprune then
      st := { st with needshortprune := false }
      tcell := shortprune tcell st
    if ¬ cheapautom st.ptn level n then
      st := { st with noncheaplevel := level + 1 }
    let tv1 := (tcell.nextElem none).getD 0
    let (r, st') :=
      otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells (tc.toNat) tv1
        (tcell.nextElem none) tcell st
    st := st'
    match r with
    | some rtn => return (rtn, st)
    | none => return (Int.ofNat level - 1, st)
termination_by (fuel, 0, 0)

/-- The child loop of `othernode`: individualize each surviving
target-cell vertex in ascending order, applying `shortprune` after any
child that asks for it and `longprune` after the first. Returns
`some rtn` for an early unwind. -/
@[expose] def otherChildLoop (ctx : Ctx n) (inf tcLevel : Nat) (fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell0 : VSet n)
    (st0 : SearchSt n) : Option Int × SearchSt n :=
  match cfuel, tv? with
  | 0, _ => (none, st0)
  | _, none => (none, st0)
  | cfuel + 1, some tv => Id.run do
    let mut st := st0
    let mut tcell := tcell0
    let (lab, ptn, active) := breakout n st.lab st.ptn (level + 1) tc tv
    st := { st with
      lab := lab
      ptn := ptn
      active := active
      fixedpts := st.fixedpts.insert tv }
    let (rtnlevel, st') := otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) st
    st := { st' with fixedpts := st'.fixedpts.erase tv }
    if rtnlevel < Int.ofNat level then
      return (some rtnlevel, st)
    if st.needshortprune then
      st := { st with needshortprune := false }
      tcell := shortprune tcell st
    if tv == tv1 then
      tcell := longprune tcell st.fixedpts st.autos
    st := recover n inf level st
    return otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
      (tcell.nextElem (some tv)) tcell st
termination_by (fuel, 1, cfuel)

end

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

/-- Run the pinned dense-nauty canonical search on `n` vertices with
adjacency rows `g` and the initial ordered partition `(lab0, cellEnds)`,
returning the trace alongside the result. `cellEnds` lists, in order,
the last position of each colour cell. -/
def runTraced (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : TraceRun n := Id.run do
  if n == 0 then
    return {
      result := {
        canonlab := #[]
        canong := #[]
        numnodes := 1
        numorbits := 0
        numgenerators := 0
        numbadleaves := 0
        maxlevel := 1
        tctotal := 0
        canupdates := 1 }
      autos := #[]
      bestCodes := [] }
  let inf := n + 2
  let ctx : Ctx n := { g }
  let st : SearchSt n :=
    { lab := lab0
      ptn := initPtn n inf cellEnds
      active := initActive n cellEnds
      orbits := .ofFn (n := n) fun i => i.val
      firstcode := .replicate (n + 2) 0
      canoncode := .replicate (n + 2) 0
      firsttc := .replicate (n + 2) (-1)
      firstlab := .replicate n 0
      canonlab := .replicate n 0
      canong := .replicate n .empty
      numorbits := n }
  let (_, st) := firstPathNode ctx inf 100 (n + 2) 1 cellEnds.length st
  let canong := updatecan ctx st.canong st.canonlab st.samerows
  return {
    result := {
      canonlab := st.canonlab
      canong := canong
      numnodes := st.numnodes
      numorbits := st.numorbits
      numgenerators := st.numgenerators
      numbadleaves := st.numbadleaves
      maxlevel := st.maxlevel
      tctotal := st.tctotal
      canupdates := st.canupdates }
    autos := st.genTrace
    bestCodes := (List.range' 1 st.canonlevel).map
      fun i => st.canoncode[i]! }

/-- The canonical search result: the traced run with its trace
discarded. -/
def run (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : RunResult n :=
  (runTraced n g lab0 cellEnds).result

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

/-- Run the nauty-compatible search on a coloured graph, returning
the trace for the certificate producer. -/
def runColoredTraced (G : Colored n k) : TraceRun n :=
  let (lab0, cellEnds) := initialPartition G
  runTraced n (rowsOf G) lab0 cellEnds

/-- Run the nauty-compatible search on a coloured graph. -/
def runColored (G : Colored n k) : RunResult n :=
  (runColoredTraced G).result

/-- The nauty-compatible canonical result: the checked label from
`canonlab` and the relabelled coloured graph. `none` only if the raw
search output fails the label check, which conformance shows does not
occur. -/
@[expose] def searchResult? (G : Colored n k) : Option (CanonResult n k) :=
  (Label.ofArray? n (runColored G).canonlab).map fun l =>
    { form := G.relabel l, label := l }

end Hex.GraphIso.Nauty
