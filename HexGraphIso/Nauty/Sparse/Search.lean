/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Target
public import HexGraphIso.Nauty.Search.State

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Canonical rows and scratch storage carried by the shared search.
Scratch is independent of the partition nest restored during backtracking. -/
structure Storage (n : Nat) extends Rows n where
  scratch : Scratch
deriving Inhabited

def Storage.update (g : Graph n) (s : Storage n) (lab : Array Nat) (same : Nat) : Storage n :=
  { s with toRows := updatecan g s.toRows lab same }

def Storage.invalidate (s : Storage n) : Storage n :=
  { s with scratch := { s.scratch with indexed := false } }

abbrev State (n : Nat) := SearchState n (Storage n)

/-- Count the node and run the sparse refinement dispatch. -/
def visit (g : Graph n) (level numcells : Nat) (st : State n) : Nat × Nat × State n :=
  let scratch := st.canong.scratch
  let st : State n := { st with canong := { st.canong with scratch := default } }
  let r := refineWith g level st.lab st.ptn st.active numcells scratch
  (r.numcells, r.longcode, { st with
    lab := r.lab, ptn := r.ptn, active := r.active
    canong := { st.canong with scratch := r.toScratch }
    numnodes := st.numnodes + 1 })

/-- The shared target guards, with `targetcell_sg` as the graph dispatch. -/
def chooseTarget (first : Bool) (g : Graph n) (tcLevel level numcells : Nat)
    (st : State n) : Int × VSet n × Nat × State n := Id.run do
  let mut st := st
  let mut tc : Int := -1
  let mut tcell := VSet.empty
  let mut size := 0
  if (if first then numcells != n
      else numcells < n && (st.eqlevFirst == level || st.compCanon >= 0)) then
    let hinted := !first && st.compCanon < 0
    let hint := if hinted then st.firsttc[level]! else -1
    let scratch := st.canong.scratch
    st := { st with canong := { st.canong with scratch := default } }
    let (pos, cell, count, scratch) := maketargetCached g st.lab st.ptn level tcLevel hint scratch
    st := { st with canong := { st.canong with scratch } }
    tc := Int.ofNat pos
    tcell := cell
    size := count
    if hinted && tc != st.firsttc[level]! then st := { st with eqlevFirst := level - 1 }
    st := { st with tctotal := st.tctotal + size }
  if first then st := { st with firsttc := st.firsttc.set! level tc }
  return (tc, tcell, size, st)

/-- nauty's five classifications, using sparse automorphism and canonical
row tests. Every other transition is shared with dense nauty. -/
def classify (g : Graph n) (level numcells : Nat) (st : State n) : Leaf × State n := Id.run do
  let mut st := st
  if st.eqlevFirst != level && st.compCanon < 0 then return (.bad, st)
  if numcells != n then return (.internal, st)
  if st.eqlevFirst == level then
    st := scatter st.firstlab st
    if st.gcaFirst >= st.noncheaplevel || isautom g st.workperm then return (.autoFirst, st)
  let mut sr := 0
  if st.compCanon == 0 then
    if level < st.canonlevel then st := { st with compCanon := 1 }
    else
      st := { st with canong := st.canong.update g st.canonlab st.samerows, samerows := n }
      let (c, s) := testcanlab g st.canong.toRows st.lab
      st := { st with compCanon := c }
      sr := s
  if st.compCanon == 0 then
    st := scatter st.canonlab st
    return (.autoCanon, st)
  else if st.compCanon > 0 then return (.better sr, st)
  else return (.bad, st)

instance policy : Generic.Policy (State n) n (γ := Graph n) where
  visit := visit
  recordFirst := recordFirst
  compareCodes := compareCodes
  chooseTarget := chooseTarget
  firstterminal := firstterminal
  classify := classify
  leafExit := leafExit
  cheapCheck := cheapCheck
  child first level tc tv st :=
    let st := child first level tc tv st
    { st with canong := st.canong.invalidate }
  afterChildFirst := afterChildFirst
  leaveChild tv st := { st with fixedpts := st.fixedpts.erase tv }
  orbit st tv := st.orbits[tv]!
  shortprune := shortprune
  longprune tcell st := Nauty.longprune tcell st.fixedpts st.autos
  recover inf level st :=
    let st := recoverLevels level (recoverPtn inf level st)
    { st with canong := st.canong.invalidate }
  afterSweep first level size index st :=
    let st := afterSweep first level size index st
    if first then { st with order := st.order * index } else st

/-- Initial shared bookkeeping and a compressed canonical store. -/
def initial (g : Graph n) (lab : Array Nat) (ends : List Nat) : State n := {
  lab, ptn := initPtn n (n + 2) ends, active := initActive n ends
  orbits := .ofFn (n := n) fun i => i.val
  firstcode := .replicate (n + 2) 0
  canoncode := .replicate (n + 2) 0
  firsttc := .replicate (n + 2) (-1)
  firstlab := .replicate n 0
  canonlab := .replicate n 0
  canong := { toRows := g.blank, scratch := .fresh n }
  workperm := .replicate n 0
  numorbits := n }

/-- The pinned sparse search, retaining its final exit and diagnostic state. -/
def runState (g : Graph n) (lab : Array Nat) (ends : List Nat) : Exit × State n :=
  let st := initial g lab ends
  if n == 0 then (.unwind 0 false, { st with numnodes := 1, canupdates := 1 })
  else Generic.node true g (n + 2) 100 (n + 2) 1 ends.length st

/-- Finish the pending canonical rows, preserving the raw sparse row order. -/
def finish (g : Graph n) (st : State n) : State n :=
  { st with canong := st.canong.update g st.canonlab st.samerows, samerows := n }

def run (g : Graph n) (lab : Array Nat) (ends : List Nat) : State n :=
  finish g (runState g lab ends).2

/-- Stable colour buckets in `O(n + k)` time. Valid colourings use every
bucket; the empty graph has no buckets. -/
@[specialize] def initialPartitionWith (n k : Nat) (colors : Array α) (color : α → Nat) :
    Array Nat × List Nat := Id.run do
  let mut buckets : Array (List Nat) := Array.replicate k []
  for i in [0:n] do
    let c := if h : i < colors.size then color colors[i] else panic! "index out of bounds"
    buckets := buckets.set! c (i :: buckets[c]!)
  let mut lab := #[]
  let mut ends := []
  for bucket in buckets do
    if !bucket.isEmpty then
      for v in bucket.reverse do lab := lab.push v
      ends := (lab.size - 1) :: ends
  return (lab, ends.reverse)

def initialPartition (n k : Nat) (colors : Array Nat) : Array Nat × List Nat :=
  initialPartitionWith n k colors id

end Hex.GraphIso.Nauty.Sparse
