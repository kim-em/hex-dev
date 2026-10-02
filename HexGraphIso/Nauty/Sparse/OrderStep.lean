/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StabilizerHead
public import HexGraphIso.Nauty.Sparse.OrderOps
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A first discrete visit retains the incoming accumulator. -/
theorem Frame.order_leaf {G : Hex.SparseGraph n} {tcLevel fuel : Nat} {f : Frame n}
    (hd : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).1 = n) :
    (Generic.node true (.ofGraph G) (n + 2) tcLevel (fuel + 1)
      f.level f.numcells f.entry).2.order = f.entry.order := by
  rw [Generic.node, Frame.first_step _ hd]
  change (firstterminal f.level
    (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.2.2).order = _
  have ht (level : Nat) (st : State n) : (firstterminal level st).order = st.order := by rfl
  rw [ht, Order.prepare]

/-- The executed first node multiplies the guiding child's accumulator
by the exact orbit size in the true point stabilizer. All sibling calls
preserve the former, and the literal sweep counter supplies the latter. -/
theorem FirstInput.order_step {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    {base : List (Fin n)} [DecidableRel (Aut.Orbit G.toDense base)]
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hf : n ≤ f.level + fuel)
    (hbase : ∀ b : Fin n, f.entry.fixedpts.mem b.val = true ↔ b ∈ base)
    (hreplay : OrbitReplay f.entry) :
    let guide : Fin n := ⟨tv, VSet.mem_lt (VSet.nextElem_mem htv)⟩
    let p := f.firstParent G.graph tcLevel [] tv
    let ch := p.child G.graph tcLevel
    (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1)
      f.level f.numcells f.entry).2.order =
    (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2.order *
      (List.finRange n).countP (fun v => decide (Aut.Orbit G.toDense base guide v)) := by
  intro guide p ch
  let g := Graph.ofGraph G.graph
  let r := Generic.prepareFirst g tcLevel f.level f.numcells f.entry
  let swept := Generic.sweep true g (n + 2) tcLevel fuel (n + 1) f.level
    r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true f.level r.2.2.2.2)
  have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
  have hret := hch.returns path (by change n + 1 ≤ f.level + 1 + fuel; omega)
  have hdone : swept.1 = .done := h.sweep_done hi htv horbit path hf hret
  have hindex : swept.2.1 = (List.finRange n).countP (fun v => decide (Aut.Orbit G.toDense base guide v)) :=
    h.index hi htv horbit path hf hbase hreplay
  have horder : swept.2.2.order =
      (Generic.node true g (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2.order :=
    Order.first g (n + 2) tcLevel fuel n f.level r.1 r.2.1.toNat tv 0 r.2.2.1
      (cheapCheck true f.level r.2.2.2.2) horbit
  have hopen : r.1 ≠ n := Nat.ne_of_lt hi
  rw [Generic.node, f.first_sweep_step _ hopen]
  dsimp only
  rw [htv]
  simp only [Option.getD_some]
  change (match swept.1 with
    | .done => (Generic.Exit.unwind (f.level - 1) false,
        (policy (n := n)).afterSweep true f.level r.2.2.2.1 swept.2.1 swept.2.2)
    | _ => (swept.1, swept.2.2)).2.order = _
  rw [hdone]
  change ((policy (n := n)).afterSweep true f.level r.2.2.2.1 swept.2.1 swept.2.2).order = _
  rw [Order.close, ite_eq_left rfl, horder, hindex]

end Hex.GraphIso.Nauty.Sparse.Max
