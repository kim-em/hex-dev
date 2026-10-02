/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIsoMathlib.Sparse.Stabilizer
public import HexGraphIso.Nauty.Sparse.OrderStep
import all HexGraphIsoMathlib.Sparse.Stabilizer
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Sparse.OrbitReplay
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Sparse.Autos
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The literal accumulator of a first-path call multiplies its incoming
value by the order of the full automorphism stabilizer of its actual base. -/
theorem FirstInput.order {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n} {base : List (Fin n)}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel)
    (hbase : ∀ b : Fin n, f.entry.fixedpts.mem b.val = true ↔ b ∈ base)
    (hreplay : OrbitReplay f.entry) :
    (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2.order =
      f.entry.order * Nat.card (GraphIso.Sparse.Aut.stabilizer G base) := by
  classical
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents base with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    cases path with
    | @leaf _ _ _ _ hd =>
      have hcard : Nat.card (GraphIso.Sparse.Aut.stabilizer G base) = 1 := by
        apply Nat.card_eq_one_iff_exists.mpr
        refine ⟨1, fun p => Subtype.ext ?_⟩
        have hh : Perm.Generated [] p.val := Generation.first_terminal h hd hbase p.property.1 p.property.2
        have hid : p.val = Perm.id n := by
          apply hh.induction (P := fun q => q = Perm.id n)
          · rfl
          · intro q hq; cases hq
          · intro p q hp hq; simp [hp, hq]
          · intro p hp; simp [hp]
        exact hid
      rw [hcard, Nat.mul_one]
      exact Frame.order_leaf hd
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      let g := Graph.ofGraph G.graph
      let r := Generic.prepareFirst g tcLevel level numcells st
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      let guide : Fin n := ⟨tv, VSet.mem_lt (VSet.nextElem_mem htv)⟩
      have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
      have hi : (visit g level numcells st).1 < n := by
        have hr := h.entry.frame.node.visit_ready hn h.entry.frame.positive
        have hc : (visit g level numcells st).1 = bcount (visit g level numcells st).2.2.ptn level n := hr.ok.count
        have hb := bcount_le (visit g level numcells st).2.2.ptn level n
        change (visit g level numcells st).1 ≠ n at hopen
        omega
      have hbudget : n ≤ level + fuel := by change n + 1 ≤ level + (fuel + 1) at hf; omega
      have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
      have hfixed : p.state.fixedpts = st.fixedpts := by
        change (cheapCheck true level r.2.2.2.2).fixedpts = st.fixedpts
        rw [cheap_fixed]
        exact target_fixed true g tcLevel level r.1
          (recordFirst level (f.code G.graph) (visit g level numcells st).2.2)
      have hbaseChild : ∀ b : Fin n, ch.entry.fixedpts.mem b.val = true ↔ b ∈ guide :: base := by
        intro b
        change (p.state.fixedpts.insert guide.val).mem b.val = true ↔ b ∈ guide :: base
        rw [VSet.mem_insert, hfixed]
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_cons]
        rw [hbase]
        constructor
        · rintro (hb | ⟨he, _⟩)
          · exact Or.inr hb
          · exact Or.inl (Fin.ext he.symm)
        · rintro (rfl | hb)
          · exact Or.inr ⟨rfl, guide.isLt⟩
          · exact Or.inl hb
      have hpReplay : OrbitReplay p.state :=
        (orbitReplayPolicy g (n + 2) tcLevel).cheap true level r.2.2.2.2
          ((orbitReplayPolicy g (n + 2) tcLevel).target true level r.1 _
            ((orbitReplayPolicy g (n + 2) tcLevel).record level (f.code G.graph) _
              ((orbitReplayPolicy g (n + 2) tcLevel).visit level numcells st hreplay)))
      have hcReplay : OrbitReplay ch.entry :=
        (orbitReplayPolicy g (n + 2) tcLevel).child true level p.tc tv p.state hpReplay
      have hchildOrder : ch.entry.order = st.order := by
        change ((policy (n := n)).child true level p.tc tv p.state).order = _
        rw [Order.child]
        change (cheapCheck true level r.2.2.2.2).order = _
        rw [Order.cheap, Order.prepare]
      have hdeep := ih (level := ch.level) (numcells := ch.numcells) (codes := ch.codes) (st := ch.entry)
        hch path (by change n + 1 ≤ level + 1 + fuel; omega) hbaseChild hcReplay
      have hstep := h.order_step hi htv horbit path hbudget hbase hreplay
      change (Generic.node true g (n + 2) tcLevel (fuel + 1) level numcells st).2.order =
        (Generic.node true g (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2.order *
          (List.finRange n).countP (fun v => decide (Aut.Orbit G.toDense base guide v)) at hstep
      rw [hstep, hdeep, hchildOrder, Nat.mul_assoc, ← GraphIso.Sparse.Aut.stabilizer_card]

end Hex.GraphIso.Nauty.Sparse.Max

namespace Hex.GraphIso.Sparse.Aut

/-- The order returned by one sparse traversal is the cardinality of
the full colour-preserving automorphism group, including at order zero. -/
theorem order_card (G : Colored n k) : order G = Nat.card (group G) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hc : Nat.card (group G) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      exact ⟨1, fun p => Subtype.ext (Perm.ext (fun v => Fin.elim0 v))⟩
    rw [hc]
    rfl
  · let partition := Nauty.Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    obtain ⟨last, leaf, path, _, _⟩ := Nauty.Sparse.initial_path G hn
    have h := Nauty.Sparse.Max.FirstInput.initial G hn 100
    have hr := Nauty.Sparse.OrbitReplay.initial (.ofGraph G.graph) partition.1 partition.2
    have he := h.order path (by change n + 1 ≤ 1 + (n + 2); omega) (base := []) (by
      intro b
      change (Nauty.VSet.empty : Nauty.VSet n).mem b.val = true ↔ b ∈ ([] : List (Fin n))
      simp) hr
    rw [stabilizer_nil] at he
    change (Nauty.Generic.node true (.ofGraph G.graph) (n + 2) 100 (n + 2) 1 partition.2.length
      (Nauty.Sparse.initial (.ofGraph G.graph) partition.1 partition.2)).2.order = 1 * Nat.card (group G) at he
    change (Nauty.Sparse.runState (.ofGraph G.graph) partition.1 partition.2).2.order = _
    rw [Nauty.Sparse.runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
    simpa only [Nat.one_mul] using he

end Hex.GraphIso.Sparse.Aut
