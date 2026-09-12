/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstPrepare
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every valid native first-path entry with identity orbits reaches a
discrete leaf within the executable's depth bound. The returned leaf has
the production partition and cache invariants. -/
theorem firstPath_exists {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {st : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (h : NodeInv G level numcells st)
    (horbit : ∀ v, v < n → st.orbits[v]! = v) (hf : n + 1 ≤ level + fuel) :
    ∃ last leaf, Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf ∧
      1 ≤ last ∧ Ready G last n leaf := by
  induction fuel generalizing level numcells st with
  | zero =>
    have hb := Nat.le_trans h.ok.bc (bcount_le _ _ _)
    omega
  | succ fuel ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    obtain ⟨hr, ht⟩ := h.prepare (tcLevel := tcLevel) hn hl
    by_cases hdisc : r.1 = n
    · have hr' : Ready G level r.1 r.2.2.2.2 := hr
      rw [hdisc] at hr'
      exact ⟨level, r.2.2.2.2, .leaf fuel level numcells st hdisc, hl, hr'⟩
    · have hc : r.1 < n := by
        have hh : r.1 = bcount r.2.2.2.2.ptn level n := hr.ok.count
        have hb := bcount_le r.2.2.2.2.ptn level n
        omega
      have hv := h.visit_ready hn hl
      have hrec := (hv.record (visit (.ofGraph G.graph) level numcells st).2.1).ready
      have hne : r.2.2.1 ≠ VSet.empty := hrec.first_nonempty hn hl hc
      have htv := VSet.nextElem_none_eq_minElem hne
      let tv := r.2.2.1.minElem
      have hmem : r.2.2.1.mem tv = true := VSet.nextElem_mem htv
      let ready := cheapCheck true level r.2.2.2.2
      have hcheap := hr.cheap true
      have htarget : Generic.Target State.frame level r.2.1.toNat r.2.2.1 ready :=
        ht.of_out hcheap.frame.effect
      have hchild := hcheap.ready.child hn hl true htarget hmem
      have hoready : ready.orbits = st.orbits := by
        dsimp only [ready]
        unfold cheapCheck
        split <;> exact prepareFirst_orbits (.ofGraph G.graph) tcLevel level numcells st
      have hochild : ∀ v, v < n →
          ((policy (n := n)).child true level r.2.1.toNat tv ready).orbits[v]! = v := by
        intro v hv
        change ready.orbits[v]! = v
        rw [hoready]
        exact horbit v hv
      obtain ⟨last, leaf, hpath, hlast, hleaf⟩ := ih (by omega) hchild hochild (by omega)
      refine ⟨last, leaf, .step hdisc htv ?_ hpath, hlast, hleaf⟩
      change ready.orbits[tv]! = tv
      rw [hoready]
      exact horbit tv (VSet.mem_lt hmem)

/-- Stable colour buckets and the initialized identity orbit array give a
successful actual first descent for every nonempty sparse coloured graph. -/
theorem initial_path (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ last leaf, Generic.FirstPath (.ofGraph G.graph) 100 (n + 2) 1 p.2.length
      (initial (.ofGraph G.graph) p.1 p.2) last leaf ∧ 1 ≤ last ∧ Ready G last n leaf := by
  apply firstPath_exists hn (Nat.le_refl _) (NodeInv.initial G hn)
  · intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
  · omega

end Hex.GraphIso.Nauty.Sparse
