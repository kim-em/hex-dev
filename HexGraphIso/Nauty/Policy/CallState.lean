/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CheapShape
public import HexGraphIso.Nauty.Policy.HistoryState
public import HexGraphIso.Nauty.Policy.Calls
public import HexGraphIso.Nauty.Policy.EquitableState
public import HexGraphIso.Nauty.Policy.PathState
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- An off-path node carries the pending history of its actual refinement. -/
structure NodePre (G : Colored n k) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) : Prop where
  positive : 1 ≤ level
  partition : SearchOk G level numcells st
  stored : RunInv G ctx st
  ancestor : st.gcaFirst < level
  canonAncestor : st.gcaCanon < level
  history : let r := visit ctx level numcells st
    History ctx tcLevel level (level - 1) r.1 r.2.2
  equitable : Equitable ctx level (st.refined ctx level numcells).lab (st.refined ctx level numcells).ptn
  boundary : Boundary G ctx level st
  cheapBound : st.noncheaplevel ≤ level
  path : PathInv G ctx level st
  starts : ∀ v, st.active.mem v = true → v = 0 ∨ st.ptn[v - 1]! ≤ level
  small : st.noncheaplevel < level → NodeShape n level (st.refined ctx level numcells).ptn

/-- A later-sibling sweep retains the parent history and its recorded target. -/
structure SweepPre (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (first : Bool)
    (level numcells tc tv1 : Nat) (cursor : Option Nat) (cell : VSet n) (st : Search n) : Prop where
  past : Generic.Past first tv1 cursor
  positive : 1 ≤ level
  partition : SearchOk G level numcells st
  target : Generic.Target (fun st => st) level tc cell st
  cursor_mem : ∀ v, cursor = some v → cell.mem v = true
  stored : RunInv G ctx st
  ancestor : st.gcaFirst ≤ level
  canonAncestor : st.gcaCanon ≤ level
  history : History ctx tcLevel level level numcells st
  recorded : Recorded ctx tcLevel level tc st
  equitable : Equitable ctx level st.lab st.ptn
  boundary : Boundary G ctx (level + 1) st
  cheapBound : st.noncheaplevel ≤ level + 1
  path : PathInv G ctx level st
  small : st.noncheaplevel ≤ level → NodeShape n level st.ptn

/-- Below a saved cheap boundary, the actual refined node satisfies the
small-cell theorem's complete geometric and equitable invariant. -/
theorem NodePre.subtree {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n}
    (h : NodePre G ctx tcLevel level numcells st) (hn0 : 0 < n)
    (hc : st.noncheaplevel < level) : SubtreeOk ctx level (st.refined ctx level numcells) := by
  have hv := ((reachPolicy G ctx tcLevel hn0).visit level numcells st h.positive h.partition).1
  exact hv.subtree hn0 h.positive rfl rfl rfl h.equitable (h.small hc)

/-- A cheap sweep supplies the small-cell invariant for its current parent
partition, including after a descendant has returned and recovery ran. -/
theorem SweepPre.subtree {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc tv1 : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st) (hn0 : 0 < n)
    (hc : st.noncheaplevel ≤ level) :
    SubtreeOk ctx level ⟨st.lab, st.ptn, st.active, numcells, 0, 0, 0⟩ :=
  h.partition.subtree hn0 h.positive rfl rfl rfl h.equitable (h.small hc)

/-- At a resumed sweep, every pair passing its fix test has realizers
stabilizing the partition where the filter is applied. -/
theorem SweepPre.local_pairs {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc tv1 : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st) :
    LocalAutos ctx level st := h.path.pairs h.stored.pairs

end Hex.GraphIso.Nauty
