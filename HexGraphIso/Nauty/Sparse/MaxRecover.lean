/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxDescent
public import HexGraphIso.Nauty.Sparse.FirstBoundary
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.ReturnCodes
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The same frozen parent selects another vertex after native recovery
and filtering. The suspended entry and its target coordinate are retained. -/
def Parent.next (p : Parent n) (st : State n) (bs : List Nat) (cell : VSet n) (tv : Nat) : Parent n :=
  { p with state := st, bs := bs, cell := cell, chosen := tv }

/-- Recovered parent geometry, incumbent growth and the literal boundary
alternative preserve the invariant for any next surviving target vertex. -/
theorem Parent.Valid.next {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat}
    {p : Parent n} {out : State n} {ds : List Nat} {cell : VSet n}
    (h : p.Valid G tcLevel)
    (hr : Ready G p.node.level (p.node.target G.graph tcLevel).numcells out)
    (he : FrameOut G p.node.level p.node.level p.state out)
    (hg : Grows (State.key G.graph p.bs p.state) (State.key G.graph ds out))
    (hb : out.noncheaplevel = p.state.noncheaplevel ∨ p.node.level < out.noncheaplevel)
    (ht : Generic.Target State.frame p.node.level p.tc cell out) (hm : cell.mem tv = true) :
    (p.next out ds cell tv).Valid G tcLevel := by
  refine ⟨h.node, h.internal, hr, h.effect.trans he, ht, hm, h.choice.grow hg, ?_⟩
  intro hc
  change out.noncheaplevel ≤ p.node.level at hc
  have hp : p.state.noncheaplevel ≤ p.node.level := by omega
  have hs := h.small hp
  have hptn : out.ptn = p.state.ptn := he.effect.ptnEq h.ready.ok hr.ok
  change NodeShape n p.node.level out.ptn
  rwa [hptn]

/-- Recovering the returned child cannot turn a failed parent guard into
a passing one. This follows the exact clamp written by `recoverLevels`. -/
theorem recover_boundary {level inf : Nat} {before out : State n}
    (h : out.noncheaplevel = before.noncheaplevel ∨ level + 1 ≤ out.noncheaplevel) :
    ((policy (n := n)).recover inf level out).noncheaplevel = before.noncheaplevel ∨
      level < ((policy (n := n)).recover inf level out).noncheaplevel := by
  change (Nauty.recover inf level out).noncheaplevel = before.noncheaplevel ∨
    level < (Nauty.recover inf level out).noncheaplevel
  rw [Nauty.recover_noncheap]
  split <;> omega

/-- The native off-path child supplies the precise boundary alternative
needed when its parent recovers and chooses another surviving vertex. -/
theorem Parent.child_boundary (G : Hex.SparseGraph n) (tcLevel fuel : Nat) (p : Parent n) :
    let out := (Generic.node false (.ofGraph G) (n + 2) tcLevel fuel
      (p.child G tcLevel).level (p.child G tcLevel).numcells (p.child G tcLevel).entry).2
    let back := (policy (n := n)).recover (n + 2) p.node.level
      ((policy (n := n)).leaveChild p.chosen out)
    back.noncheaplevel = p.state.noncheaplevel ∨ p.node.level < back.noncheaplevel := by
  intro out back
  apply recover_boundary
  have hb := node_boundary (.ofGraph G) (n + 2) tcLevel fuel
    (p.child G tcLevel).level (p.child G tcLevel).numcells (p.child G tcLevel).entry
    (by change 0 < p.node.level + 1; omega)
  have he : (p.child G tcLevel).entry.noncheaplevel = p.state.noncheaplevel := by
    dsimp only [Parent.child]
    cases p.first <;> rfl
  rw [he] at hb
  exact hb

/-- The first-path child has the same recovery guarantee, including all
later siblings traversed before its actual return. -/
theorem Parent.first_boundary {G : Hex.SparseGraph n} {tcLevel fuel last : Nat}
    {p : Parent n} {leaf : State n}
    (path : Generic.FirstPath (.ofGraph G) tcLevel fuel
      (p.child G tcLevel).level (p.child G tcLevel).numcells (p.child G tcLevel).entry last leaf) :
    let out := (Generic.node true (.ofGraph G) (n + 2) tcLevel fuel
      (p.child G tcLevel).level (p.child G tcLevel).numcells (p.child G tcLevel).entry).2
    let back := (policy (n := n)).recover (n + 2) p.node.level
      ((policy (n := n)).leaveChild p.chosen (afterChildFirst p.node.level p.chosen out))
    back.noncheaplevel = p.state.noncheaplevel ∨ p.node.level < back.noncheaplevel := by
  intro out back
  apply recover_boundary
  have hb := firstPath_boundary (inf := n + 2) path (by change 0 < p.node.level + 1; omega)
  have he : (p.child G tcLevel).entry.noncheaplevel = p.state.noncheaplevel := by
    dsimp only [Parent.child]
    cases p.first <;> rfl
  rw [he] at hb
  exact hb

end Hex.GraphIso.Nauty.Sparse.Max
