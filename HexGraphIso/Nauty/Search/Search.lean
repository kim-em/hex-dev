/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexGraphIso.Nauty.Search.State
public import HexGraphIso.Nauty.Search.Generic

public section

/-!
Structured canonical search for nauty 2.9.3 dense basic mode. A flat
state carries the globals, while mutually recursive nodes and sweeps
carry the level and target cell. An unwind carries its short-prune
request to the receiving sweep.

The options are `getcanon = 1`, undirected graphs, caller partition,
`tc_level = 100`, no vertex invariant, callbacks, Schreier machinery,
markers, automorphism printing, or asynchronous aborts.

Correspondence with `vendor/nauty-2.9.3/nauty.c`, in source order.
Blank lines, braces, local declarations, and comment blocks belong to the
surrounding row. The two C allocation variants use the same Lean code.
The omitted group-size product does not affect any search decision or
any of the seven returned statistics.

| nauty.c lines | abridged C | Lean declaration | note |
|---|---|---|---|
| 468 | `orbits[i] = i` | `initial` | identity orbits |
| 469-470 | `grpsize1 = 1; grpsize2 = 0` | none | group-size output omitted |
| 471-479 | zero counters, `numorbits = n`, empty fixed points, `noncheaplevel = 1`, `eqlev_canon = -1` | `Search`, `initial` | initial globals |
| 480-490 | workspace, `worktop`, `fmptr` | `Search.autos`, `pushAuto` | pinned 500-pair capacity, initially empty |
| 491-493 | `errstatus = 0; needshortprune = FALSE` | `Exit` | no pending payload initially, aborts pinned out |
| 494-496 | invariant counters | none | pinned-out options: no invariant |
| 497-502 | `firstpathnode(...,1,numcells)` | `runState` | node fuel `n + 2`, sweep fuel `n + 1` |
| 503-508 | aborted/killed status | none | pinned-out options: no abort or kill request |
| 509-513 | `updatecan`; copy canonical labelling | `finish` | `getcanon = 1` |
| 559-587 | first node arguments, locals, target-cell allocation | `node true`, `VSet` | per-level call arguments, managed allocation |
| 588-593 | increment nodes, `doref` | `visit` | count before refinement |
| 594 | `firstcode[level] = refcode` | `recordFirst` | first path only |
| 595-606 | `qinvar` statistics | none | pinned-out options: no invariant |
| 607-615 | `tc = -1`; choose iff `numcells != n`; add size | `chooseTarget true` | unhinted call |
| 616-617 | `firsttc[level] = tc` | `chooseTarget true` | includes terminal `-1` |
| 618-621 | `usernodeproc` | none | pinned-out options: no callback |
| 622-624 | first leaf test and installation | `node true`, `firstterminal` | before cheap check |
| 625-633 | user level and canonical callbacks | none | pinned-out options: no callbacks |
| 634-636 | `return level-1` | `node true` | unwind without short prune |
| 637-642 | kill request | none | pinned-out options: no asynchronous cancellation |
| 643-646 | guarded `cheapautom` | `cheapCheck true` | `noncheaplevel >= level` |
| 647-649 | initialize index and child count | `node`, `sweep` | child count only served callbacks |
| 650-654 | next target vertex; `orbits[tv] == tv` | `sweep true` | reread the pruned cell |
| 655-657 | breakout, fixed point, `cosetindex = tv` | `child true` | every first-path child |
| 658-666 | recurse on first child | `sweep`, `node true` | child count omitted |
| 667-669 | `gca_first = level; stabvertex = tv1` | `afterChildFirst` | after the child returns |
| 670-679 | recurse off first path | `sweep`, `node false` | child count omitted |
| 680-682 | erase fixed point; early return | `sweep` | transport the whole unwind |
| 683-687 | consume short prune | `sweep`, `shortprune` | only at the receiving level |
| 688-689 | `recover` | `recoverPtn`, `recoverLevels` | before next child |
| 690-692 | `orbits[tv] == tv1`: increment index | `sweep true` | includes skipped vertices |
| 693-694 | multiply group size | none | group-size output omitted |
| 695-697 | decrement `allsamelevel` | `afterSweep true` | only complete sweep, both equalities required |
| 698-701 | markers and user level callback | none | pinned-out options: no markers or callbacks |
| 702-703 | `return level-1` | `node` | no short prune |
| 704-717 | other-node documentation | `node false` | no executable decisions |
| 718-747 | other node arguments, locals, target-cell allocation | `node false`, `VSet` | per-level call arguments, managed allocation |
| 748-753 | kill request | none | pinned-out options: no asynchronous cancellation |
| 754-760 | increment nodes, `doref`, code | `visit` | count before refinement |
| 761-770 | `qinvar` statistics | none | pinned-out options: no invariant |
| 771-772 | first code agrees at previous level | `compareCodes` | advance `eqlevFirst` |
| 773-786 | canonical code trichotomy | `compareCodes` | `getcanon = 1` |
| 787-788 | save code iff `comp_canon > 0` | `compareCodes` | retain improved prefix |
| 789-796 | target iff internal and first agreement or nonnegative comparison | `chooseTarget false` | default `tc = -1` |
| 797-802 | hinted target, reset first agreement on target mismatch | `chooseTarget false` | only `compCanon < 0` arm |
| 803-807 | unhinted target; add size | `chooseTarget false` | otherwise |
| 808-811 | user node callback | none | pinned-out options: no callbacks |
| 812-816 | `processnode`, early return | `classify`, `leafExit`, `node false` | internal classification continues |
| 817-821 | post-process short prune | none | dead on reachable states: noninternal classifications unwind below this node |
| 822-825 | `cheapautom` | `cheapCheck false` | after classification, without first-path guard |
| 826-829 | next target vertex | `sweep false` | no orbit skip test |
| 830-831 | breakout and fixed point | `child false` | retain coset index |
| 832-837 | recurse and erase fixed point | `sweep`, `node false` | off-path recursion |
| 838-839 | early unwind | `sweep` | transport short-prune payload |
| 840-845 | consume short prune | `sweep`, `shortprune` | read most recent pair |
| 846-848 | long prune iff `tv == tv1` | `sweep false`, `longprune` | after short prune |
| 849 | Schreier prune | none | pinned-out options: no Schreier machinery |
| 850-853 | recover | `recoverPtn`, `recoverLevels` | before next child |
| 854-856 | `return level-1` | `node` | complete sweep |
| 857-870 | first-terminal documentation and locals | `firstterminal` | no decisions |
| 871-876 | maximum level, first levels, sentinels, labelling | `firstterminal` | install first leaf |
| 877-888 | canonical levels, comparison, rows, codes, update count | `firstterminal` | `getcanon = 1`, `samerows = 0` |
| 889-928 | process-node documentation and locals | `Leaf`, `classify`, `leafExit` | five classifications |
| 929-933 | first disagreement and smaller code; discrete test | `classify` | bad or internal |
| 934-937 | first agreement, scatter permutation | `classify` | reusable scratch, no sentinel guard |
| 938-941 | `gca_first >= noncheaplevel` or `isautom` | `classify` | exact 2.9.3 code-1 admission |
| 942-950 | still unclassified; tied code and shorter level | `classify` | decide level tie before rows |
| 951-959 | `updatecan`, `samerows = n`, `testcanlab` | `classify` | reuse already compared rows |
| 960-964 | equal rows, scatter canonical permutation | `classify` | code 2 |
| 965-973 | greater or smaller canonical comparison | `classify` | better with `sr`, or bad; noncanonical mode pinned out |
| 974-980 | max level; code 0 returns current level | `leafExit` | `.done` continues internal node |
| 981-985 | code 1 workspace overwrite, `fmperm` | `admit`, `pushAuto` | overwrite last pair at 500, append full trace |
| 986-987 | write automorphism | none | pinned-out options: no printing |
| 988-989 | join orbits, increment generators | `admit`, `leafExit .autoFirst` | always count code 1 |
| 990-992 | user automorphism callback, Schreier | none | pinned-out options: no callback or Schreier machinery |
| 993-994 | return first GCA | `leafExit .autoFirst` | no short prune |
| 995-1000 | code 2 pair, save orbit count, join | `admit`, `leafExit .autoCanon` | pair and trace even without orbit change |
| 1001-1005 | unchanged orbit count, return canonical GCA | `leafExit .autoCanon` | no generator increment or coset test; short iff GCAs differ |
| 1006-1007 | write automorphism | none | pinned-out options: no printing |
| 1008 | increment generators | `leafExit .autoCanon` | orbit count changed |
| 1009-1011 | callback and Schreier | none | pinned-out options: no callback or Schreier machinery |
| 1012-1013 | coset representative smaller: return first GCA | `leafExit .autoCanon` | no short prune |
| 1014-1016 | return canonical GCA, short iff GCAs differ | `leafExit .autoCanon` | payload fixed with target |
| 1017-1024 | install better leaf and `sr` | `install` | increment updates, reset comparison, sentinel |
| 1025-1032 | canonical callback | none | pinned-out options: no callback |
| 1033-1038 | better falls through; bad increments bad leaves | `leafExit` | shared prune tail |
| 1039-1050 | `fmptn` iff level differs from noncheap level | `pruneReturn`, `pushAuto` | same 500-pair overwrite rule |
| 1051-1052 | `save`, `newlevel` | `pruneReturn` | preserve signed arithmetic, convert reachable nonnegative target to Nat |
| 1053-1056 | short iff pair stored and target differs from first GCA | `pruneReturn` | payload fixed with target |
| 1057-1071 | recover documentation and locals | `recoverPtn`, `recoverLevels` | no decisions |
| 1072-1074 | reopen partition entries above level | `recoverPtn` | full rescan |
| 1075 | clamp noncheap level | `recoverLevels` | first clamp |
| 1076 | clamp first agreement | `recoverLevels` | second clamp |
| 1077-1079 | clamp canonical GCA | `recoverLevels` | third clamp, canonical mode pinned on |
| 1080-1086 | clamp canonical agreement, reset comparison | `recoverLevels` | fourth clamp uses non-strict inequality |
-/

namespace Hex.GraphIso.Nauty.Engine

/-- Search termination and nonlocal return control. -/
abbrev Exit := Generic.Exit

/-- The five node classifications. -/
abbrev Leaf := Generic.Leaf

/-- The search globals, stored in one record so array updates need only
consume one constructor. Level and target-cell data are call arguments. -/
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

/-- Record an automorphism pair in the bounded workspace. This is
{name}`Hex.GraphIso.Nauty.pushAuto` on the flat engine state. -/
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
data and the initial best-so-far leaf. This retains the updates of
{name}`Hex.GraphIso.Nauty.firstterminal`. -/
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

/-- Reopen the partition below the receiving level, as in the rescan of
{name}`Hex.GraphIso.Nauty.recover`. -/
@[inline] def recoverPtn (inf level : Nat) (st : Search n) : Search n := Id.run do
  let mut ptn := st.ptn
  for i in [0 : n] do
    if ptn[i]! > level then
      ptn := ptn.set! i inf
  return { st with ptn }

/-- Clamp the four level counters in the order of
{name}`Hex.GraphIso.Nauty.recover`. Equality in the last clamp resets the
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

/-- Intersect with the most recently written workspace pair, as in
{name}`Hex.GraphIso.Nauty.shortprune`. -/
@[inline] def shortprune (tcell : VSet n) (st : Search n) : VSet n :=
  match st.autos.back? with
  | some (_, mcr) => tcell.inter mcr
  | none => tcell

set_option maxHeartbeats 800000 in
mutual

/-- Refine a node, classify it, and sweep its surviving children. Only
the leftmost child of a first-path node remains on the first path. -/
@[expose] def node (first : Bool) (ctx : Ctx n) (inf tcLevel fuel : Nat)
    (level numcells : Nat) (st : Search n) : Exit × Search n :=
  match fuel with
  | 0 => (.fuel, st)
  | fuel + 1 => Id.run do
    let (numcells, refcode, st) := visit ctx level numcells st
    let st := if first then recordFirst level refcode st else compareCodes level refcode st
    let (tc, tcell, tcellsize, st) := chooseTarget first ctx tcLevel level numcells st
    let mut st := st
    if first then
      if numcells == n then
        return (.unwind (level - 1) false, firstterminal level st)
    else
      let (leaf, st') := classify ctx level numcells st
      let (exit, st') := leafExit leaf level st'
      st := st'
      match exit with
      | .done => pure ()
      | _ => return (exit, st)
    st := cheapCheck first level st
    let tv := tcell.nextElem none
    let (exit, index, st') := sweep first ctx inf tcLevel fuel (n + 1)
      level numcells tc.toNat (tv.getD 0) tv tcell 0 st
    match exit with
    | .done => return (.unwind (level - 1) false, afterSweep first level tcellsize index st')
    | _ => return (exit, st')
termination_by (fuel, 0, 0)

/-- Visit remaining target vertices in order, rereading the cell after
each prune. The orbit index includes skipped vertices on the first path.
Nodes return an unwind or fuel, so the `done` arm after a child is unreachable. -/
@[expose] def sweep (first : Bool) (ctx : Ctx n) (inf tcLevel fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (tv? : Option Nat) (tcell : VSet n)
    (index : Nat) (st : Search n) : Exit × Nat × Search n :=
  match tv?, cfuel with
  | none, _ => (.done, index, st)
  | some _, 0 => (.fuel, index, st)
  | some tv, cfuel + 1 => Id.run do
    let mut st := st
    let mut tcell := tcell
    if !first || st.orbits[tv]! == tv then
      st := child first level tc tv st
      let (exit, st') := node (first && tv == tv1) ctx inf tcLevel fuel
        (level + 1) (numcells + 1) st
      st := st'
      if first && tv == tv1 then
        st := afterChildFirst level tv1 st
      st := { st with fixedpts := st.fixedpts.erase tv }
      match exit with
      | .fuel => return (.fuel, index, st)
      | .unwind target short =>
        if target < level then
          return (exit, index, st)
        if short then
          tcell := shortprune tcell st
      | .done => pure ()
      if !first && tv == tv1 then
        tcell := longprune tcell st.fixedpts st.autos
      st := recoverLevels level (recoverPtn inf level st)
    let index := if first && st.orbits[tv]! == tv1 then index + 1 else index
    return sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1
      (tcell.nextElem (some tv)) tcell index st
termination_by (fuel, 1, cfuel)

end

/-- Allocate the search globals, including the reusable permutation. -/
def initial (n : Nat) (lab0 : Array Nat) (cellEnds : List Nat) : Search n :=
  { lab := lab0
    ptn := initPtn n (n + 2) cellEnds
    active := initActive n cellEnds
    orbits := .ofFn (n := n) fun i => i.val
    firstcode := .replicate (n + 2) 0
    canoncode := .replicate (n + 2) 0
    firsttc := .replicate (n + 2) (-1)
    firstlab := .replicate n 0
    canonlab := .replicate n 0
    canong := .replicate n .empty
    workperm := .replicate n 0
    numorbits := n }

/-- Run the search and retain the final state and exit for diagnostics.
On a valid nonempty input, cell count is at least the level: refinement
never decreases it and each child increases it. Thus node depth is at most
`n`, so node fuel `n + 2` suffices. A sweep visits at most `n` vertices in
strictly increasing order, so sweep fuel `n + 1` suffices. -/
def runState (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : Exit × Search n :=
  let st := initial n lab0 cellEnds
  if n == 0 then
    (.unwind 0 false, { st with numnodes := 1, canupdates := 1 })
  else
    node true { g } (n + 2) 100 (n + 2) 1 cellEnds.length st

/-- Read the canonical result and trace, updating the remaining rows. -/
def finish (ctx : Ctx n) (st : Search n) : TraceRun n :=
  { result := {
      canonlab := st.canonlab
      canong := updatecan ctx st.canong st.canonlab st.samerows
      numnodes := st.numnodes
      numorbits := st.numorbits
      numgenerators := st.numgenerators
      numbadleaves := st.numbadleaves
      maxlevel := st.maxlevel
      tctotal := st.tctotal
      canupdates := st.canupdates }
    autos := st.genTrace
    bestCodes := if n == 0 then [] else
      (List.range' 1 st.canonlevel).map fun i => st.canoncode[i]! }

/-- Run the structured search with the certificate producer's result type. -/
def runTraced (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : TraceRun n :=
  finish { g } (runState n g lab0 cellEnds).2

/-- Run the structured search, discarding the trace. -/
def run (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : RunResult n :=
  (runTraced n g lab0 cellEnds).result

/-- Run the structured search on a coloured graph, retaining the trace. -/
def runColoredTraced {k : Nat} (G : Colored n k) : TraceRun n :=
  let (lab0, cellEnds) := initialPartition G
  runTraced n (rowsOf G) lab0 cellEnds

/-- Run the structured search on a coloured graph. -/
def runColored {k : Nat} (G : Colored n k) : RunResult n :=
  (runColoredTraced G).result

end Hex.GraphIso.Nauty.Engine

namespace Hex.GraphIso.Nauty

/-- Run the canonical search and retain its accepted generators and path codes. -/
def runTraced (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : TraceRun n := Engine.runTraced n g lab0 cellEnds

/-- Run the canonical search, discarding the trace. -/
def run (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : RunResult n := (runTraced n g lab0 cellEnds).result

variable {n k : Nat}

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
