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
| 688-689 | `recover` | `recover` | partition rescan and level clamps before the next child |
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
| 850-853 | recover | `recover` | partition rescan and level clamps before the next child |
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

namespace Hex.GraphIso.Nauty

variable {n : Nat}

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
      st := Nauty.recover inf level st
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

/-- Run the search with the certificate producer's result type. -/
def runTraced (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : TraceRun n :=
  finish { g } (runState n g lab0 cellEnds).2

/-- Run the search, discarding the trace. -/
def run (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : RunResult n :=
  (runTraced n g lab0 cellEnds).result

/-- Run the search on a coloured graph, retaining the trace. -/
def runColoredTraced {k : Nat} (G : Colored n k) : TraceRun n :=
  let (lab0, cellEnds) := initialPartition G
  runTraced n (rowsOf G) lab0 cellEnds

/-- Run the search on a coloured graph. -/
def runColored {k : Nat} (G : Colored n k) : RunResult n :=
  (runColoredTraced G).result

variable {k : Nat}

/-- The nauty-compatible canonical result: the checked label from
`canonlab` and the relabelled coloured graph. `none` only if the raw
search output fails the label check, which conformance shows does not
occur. -/
@[expose] def searchResult? (G : Colored n k) : Option (CanonResult n k) :=
  (Label.ofArray? n (runColored G).canonlab).map fun l =>
    { form := G.relabel l, label := l }

end Hex.GraphIso.Nauty
