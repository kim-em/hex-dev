/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeState
public import HexGraphIso.Nauty.Sparse.FirstPrepare
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An internal native classifier leaves its input state unchanged. -/
theorem classify_internal_state {g : Graph n} {level numcells : Nat} {st : State n}
    (h : (classify g level numcells st).1 = .internal) :
    classify g level numcells st = (.internal, st) := by
  have hnc := classify_open h
  rw [classify_eq] at h ⊢
  split
  · rename_i hb
    simp only [hb, ite_true] at h
    cases h
  · simp only [bne_iff_ne.mpr hnc, ite_true]

/-- A positive canonical code comparison selects a nonempty native cell.
Consequently the sweep executes a child before it can return settled codes. -/
theorem Ready.target_phase {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : numcells < n) :
    let t := chooseTarget false (.ofGraph G.graph) tcLevel level numcells st
    t.2.2.2.compCanon ≤ 0 ∨ (t.2.1.nextElem none).isSome := by
  have hcmp := (chooseTarget_codes false (.ofGraph G.graph) tcLevel level numcells st).2.2.2.1
  by_cases hp : st.compCanon ≤ 0
  · exact Or.inl (hcmp ▸ hp)
  · right
    have hpos : 0 ≤ st.compCanon := by omega
    have hnonempty := h.first_nonempty (tcLevel := tcLevel) hn hl hc
    have hset : (chooseTarget false (.ofGraph G.graph) tcLevel level numcells st).2.1 =
        (chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).2.1 := by
      have hneg : ¬st.compCanon < 0 := by omega
      simp [chooseTarget, hc, show numcells ≠ n by omega, hpos, hneg]
    rw [hset, VSet.nextElem_none_eq_minElem hnonempty]
    rfl

/-- Native off-path preparation records both the general guided target
choice and the stronger saved-target condition used in cheap subtrees. -/
theorem CodeEntry.recorded {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} (h : CodeEntry G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : (prepareOther (.ofGraph G.graph) tcLevel level numcells st).1 < n) :
    let p := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    CheapRecorded level p.2.2.1.toNat p.2.2.2.2.2 ∧
      RouteRecorded G.graph tcLevel level p.2.2.1.toNat p.2.2.2.2.2 := by
  let v := visit (.ofGraph G.graph) level numcells st
  have hr := (h.node.visit_ready hn hl).compare v.2.1
  have hcode := refineWith_code_lt (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
  have hh := h.history.compare (by omega) hcode
  have hh' := h.route.compare (by omega) v.2.1
  exact ⟨hh.recorded hc hr.ready.scratch, route_recorded hn (by omega) hr.ready hh'.bound hc⟩

end Hex.GraphIso.Nauty.Sparse
