/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert
public import HexGraphIso.IsoLit
public import HexGraphIso.NodeLit
public import HexGraphIso.NodePacked
public import HexGraphIso.Separator
public import HexGraph.Basic
public meta import Lean

public section

/-!
Module-boundary kernel regression ladder for the certificate replay
closure, in the mould of `HexBasic.ModuleBoundaryTests`: every
obligation here is closed by `kdecide`, which assigns the raw
`of_decide_eq_true` shape so that ONLY the module-finalization kernel
evaluates it — the exact obligation the `graph_iso` certificate route
emits. These stages caught two exposure gaps: `mash`/`cleanup` and
`codeSentinel` missing `@[expose]` here, and core `Array.map`
delegating to the unexposed `Array.mapM` (worked around by
`Hex.Array.map'`; upstream fix pending in the lean4 exposure series).
The tests must stay in their own module: the defect class is a
callee's body being unavailable across a module boundary, so a
same-module test proves nothing.
-/

namespace Hex.GraphIso.Nauty

meta section
open Lean Meta Elab Tactic

/-- Close a decidable goal with `of_decide_eq_true (id (Eq.refl true))`,
assigned raw so that ONLY the declaration kernel evaluates it. -/
elab "kdecide" : tactic => do
  let g ← getMainGoal
  let p ← g.getType
  let inst ← synthInstance (← mkAppM ``Decidable #[p])
  let decideApp := mkApp2 (mkConst ``Decidable.decide) p inst
  let refl := mkApp2 (mkConst ``Eq.refl [1])
    (mkConst ``Bool) (mkConst ``Bool.true)
  let eqType ← mkAppM ``Eq #[decideApp, mkConst ``Bool.true]
  let h ← mkExpectedTypeHint refl eqType
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) p inst h)

end

-- sanity: the instrument itself works
example : 2 + 2 = 4 := by kdecide

private def rowsP : Array Nat :=
  List.toArray [50, 69, 138, 276, 521, 385, 770, 548, 104, 208]
private def ctxP : Ctx := { n := 10, g := rowsP }
private def lab0 : Array Nat := List.toArray [0,1,2,3,4,5,6,7,8,9]
private def ptn0 : Array Nat := initPtn 10 12 [9]
private def st0 : RefineSt :=
  { lab := lab0, ptn := ptn0, active := initActive [9], numcells := 1,
    hint := 0, maxpos := 0, longcode := 1 }

set_option maxRecDepth 1000000 in
example : worksetOf lab0 0 9 = 1023 := by kdecide
set_option maxRecDepth 1000000 in
example : countsOf ctxP lab0 1023 0 9 = [3,3,3,3,3,3,3,3,3,3] := by kdecide
set_option maxRecDepth 1000000 in
example : countValues [3,3,3,3,3,3,3,3,3,3] = [3] := by kdecide
set_option maxRecDepth 1000000 in
example : mash 27490 1 = 128 := by kdecide
set_option maxRecDepth 1000000 in
example : mash 27490 1 = 128 := by decide
set_option maxRecDepth 1000000 in
example : mash 27490 1 = 128 := by rfl
set_option maxRecDepth 1000000 in
example : cleanup 128 = 128 := by kdecide
set_option maxRecDepth 1000000 in
example : (nontrivialCell ctxP 1 1023 0 9
    { st0 with active := 0, longcode := mash 1 9 }).longcode = 59 := by
  kdecide
set_option maxRecDepth 1000000 in
example : (refineStep ctxP 1 0 st0).longcode = 27490 := by kdecide
set_option maxRecDepth 1000000 in
example : (refineLoop ctxP 1 48 st0).longcode = 27490 := by kdecide

private def probeGraph : Colored 10 1 :=
  { graph := Hex.Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

private def probeCert : CertNode := (.node [(.node [(.node [.leaf, (.autom 0 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8])), (.autom 1 (List.toArray [0, 1, 6, 8, 5, 4, 2, 9, 3, 7])), (.autom 2 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8]))]), (.autom 0 (List.toArray [0, 4, 3, 8, 5, 1, 9, 2, 6, 7])), (.autom 1 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8]))]), (.autom 0 (List.toArray [1, 0, 4, 3, 2, 6, 5, 9, 8, 7])), (.autom 1 (List.toArray [4, 0, 1, 2, 3, 9, 5, 6, 7, 8])), (.autom 2 (List.toArray [0, 4, 3, 2, 1, 5, 9, 8, 7, 6])), (.autom 1 (List.toArray [0, 4, 3, 2, 1, 5, 9, 8, 7, 6])), (.autom 4 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8])), (.autom 2 (List.toArray [0, 1, 6, 8, 5, 4, 2, 9, 3, 7])), (.autom 3 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8])), (.autom 3 (List.toArray [0, 1, 6, 8, 5, 4, 2, 9, 3, 7])), (.autom 8 (List.toArray [0, 1, 2, 7, 5, 4, 6, 3, 9, 8]))])

private def probeKey : Key := ⟨[128, 27412, 8, 53, 32767], [14, 49, 577, 385, 322, 642, 148, 104, 536, 292]⟩

set_option maxRecDepth 1000000 in
example : (refine { n := 10, g := rowsOf probeGraph } 1
    (initialPartition probeGraph).1
    (initPtn 10 12 (initialPartition probeGraph).2)
    (initActive (initialPartition probeGraph).2)
    (initialPartition probeGraph).2.length).longcode = 128 := by kdecide

-- residual-suspect isolation
example : ((some true : Option Bool) = some true) := by kdecide
example : (compare (5 : Nat) 3 = Ordering.gt) := by kdecide
example : ([1,2,3].zipIdx 0 = [(1,0),(2,1),(3,2)]) := by kdecide
example : (keyCmp probeKey probeKey = Ordering.eq) := by kdecide
set_option maxRecDepth 1000000 in
example : (leafRows { n := 10, g := rowsP } lab0 =
    [50, 69, 138, 276, 521, 385, 770, 548, 104, 208]) := by kdecide
set_option maxRecDepth 1000000 in
example : (discreteAt (initPtn 10 12 [9]) 1 10 = false) := by kdecide
set_option maxRecDepth 1000000 in
example : (checkAutom rowsP (List.toArray [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]) 10
    = true) := by kdecide

set_option maxRecDepth 1000000 in
example : checkNode { n := 10, g := rowsP } 100 probeKey.rows
    (validGammas rowsP 10 probeCert) 1 1
    lab0 (initPtn 10 12 [9]) (initActive [9]) 1 probeCert
    probeKey.codes = none := by kdecide
-- core `Array.map` itself still stalls here (unexposed impl loop; see
-- the upstream draft); the house `Hex.Array.map'` reduces:
example : (Hex.Array.map' (fun w => w + 1) lab0).toList =
    [1,2,3,4,5,6,7,8,9,10] := by kdecide
example : (Hex.Array.map' (fun w => w + 1) #[1, 2]) = #[2, 3] := by kdecide
example : ([1,2,3].isPerm [3,2,1] = true) := by kdecide
set_option maxRecDepth 1000000 in
example : (breakout lab0 (initPtn 10 12 [9]) 2 0 0).2.2 = 1 := by kdecide
set_option maxRecDepth 1000000 in
example : (breakout lab0 (initPtn 10 12 [9]) 2 0 0).1 = lab0 := by kdecide
set_option maxRecDepth 1000000 in
example : (checkCellsPerm (initPtn 10 12 [9]) lab0 lab0 1 10 = true) := by
  kdecide

set_option maxRecDepth 1000000 in
example : checkNode { n := 10, g := rowsP } 100 probeKey.rows
    (validGammas rowsP 10 probeCert) 2 1
    lab0 (initPtn 10 12 [9]) (initActive [9]) 1 probeCert
    probeKey.codes = none := by kdecide
set_option maxRecDepth 1000000 in
example : checkNode { n := 10, g := rowsP } 100 probeKey.rows
    (validGammas rowsP 10 probeCert) 3 1
    lab0 (initPtn 10 12 [9]) (initActive [9]) 1 probeCert
    probeKey.codes = none := by kdecide

set_option maxRecDepth 1000000 in
example : checkNode { n := 10, g := rowsP } 100 probeKey.rows
    (validGammas rowsP 10 probeCert) 4 1
    lab0 (initPtn 10 12 [9]) (initActive [9]) 1 probeCert
    probeKey.codes = some true := by kdecide

set_option maxRecDepth 1000000 in
example : checkKey probeGraph probeCert probeKey = true := by kdecide

/-- The separator closure kernel-reduces: the self-comparison of the
probe graph evaluates both separator codes and their disagreement
test to `false`. -/
example : Hex.GraphIso.sepDiffG probeGraph probeGraph = false := by
  kdecide

example : Hex.GraphIso.sepRootG probeGraph probeGraph = false := by
  kdecide

-- the negative tactic route's flat-literal obligation: pins the
-- kernel closure of flatRows/chunkRows/atD feeding checkNode
set_option maxRecDepth 1000000 in
example : Hex.GraphIso.checkKeyFlat probeGraph
    probeGraph.graph.adjMatrix.data.toList probeCert probeKey
    = true := by kdecide

example : Hex.GraphIso.checkKeyLit probeGraph
    probeGraph.graph.adjMatrix.data.toList probeCert probeKey
    = true := by kdecide

-- the packed-state obligation the tactic emits: pins the kernel
-- closure of the packed replay (pget/pset, the byte-table popCount,
-- the raw bit-set operations) end to end
example : Hex.GraphIso.checkKeyP probeGraph
    probeGraph.graph.adjMatrix.data.toList probeCert probeKey
    = true := by kdecide

end Hex.GraphIso.Nauty
