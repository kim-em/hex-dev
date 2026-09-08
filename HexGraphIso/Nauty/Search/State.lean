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

/-! State and primitive transitions used by the structured search and its mathematical view. -/

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
