/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SubtreeMap
public import HexGraphIso.Nauty.Sparse.ChildFrame
public import HexGraphIso.Nauty.Sparse.Stabilize
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The unpruned sparse child maximum indexed by its literal chosen vertex. -/
@[expose] def vertexKey (G : Hex.SparseGraph n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (tc numcells v : Nat) : Key n :=
  let child := breakout n lab ptn (level + 1) tc v
  subtreeKey G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2 (numcells + 1)

/-- A full parent cell is a valid target for each of its native children. -/
theorem Ready.window_target {G : GraphIso.Sparse.Colored n k} {level numcells tc len : Nat}
    {st : State n} (_h : Ready G level numcells st) (hc : IsCell st.ptn level tc len)
    (hlen : 1 < len) (hr : tc + len ≤ n) :
    Generic.Target State.frame level tc (windowSet n st.lab tc len) st :=
  ⟨len, fun _ => ⟨hc, by omega, hr⟩, fun _ hv => (mem_windowSet.mp hv).2⟩

/-- A checked automorphism stabilizing the current cells identifies the
entire native child maxima at the vertices it carries. The proof transports
every unpruned leaf through the actual individualization and sparse dispatch. -/
theorem Ready.vertex_key {G : GraphIso.Sparse.Colored n k}
    {level numcells tc len v fuel : Nat} {st : State n} {gamma : Array Nat}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ha : checkAutom (Graph.context G.graph).g gamma = true)
    (hstab : CellStab st.ptn level st.lab gamma)
    (hc : IsCell st.ptn level tc len) (hlen : 1 < len) (hr : tc + len ≤ n)
    (hv : (windowSet n st.lab tc len).mem v = true)
    (hf : n < fuel + (numcells + 1)) (tcLevel : Nat) :
    vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells v =
      vertexKey G.graph tcLevel fuel level st.lab st.ptn tc numcells gamma[v]! := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound (by simp [Graph.context]) ha
  have hok : LabOk st.lab n := labOk_of_reach h.ok.labSize h.ok.reach
  have hs : st.lab.size = n := h.ok.labSize
  have hptn : st.ptn.size = n := h.ok.ptnSize
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn h.ok hl
    simpa only [State.frame, hptn] using he
  have hrename (v : Nat) (hv : v < n) : (renamingOf σ.toPerm) v = gamma[v]! :=
    (renamingOf_lt σ.toPerm hv).trans ((Renaming.get_toPerm σ ⟨v, hv⟩).trans (hσ v hv))
  have hmap : st.lab.map (renamingOf σ.toPerm).toFun = st.lab.map (fun v => gamma[v]!) :=
    map_congr_of_labOk hok hrename
  have hcells : cellsPerm st.ptn level st.lab (st.lab.map (renamingOf σ.toPerm).toFun) := by
    rw [hmap]
    exact hstab
  have hvals : ∀ q, q < n → st.ptn[q]! ≤ level ∨ level + 1 < st.ptn[q]! := by
    have hlev : level ≤ n := Nat.le_trans h.ok.bc (bcount_le _ _ _)
    intro q hq
    rcases h.ok.vals q hq with hv | hv
    · exact Or.inl hv
    · right
      change st.ptn[q]! = n + 2 at hv
      omega
  have hw := windowSet_carry hstab hc (by rw [hs]; exact hr) hok hv
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  obtain ⟨j, hj, hat, hchild⟩ := breakout_match (renamingOf σ.toPerm) level tc len o
    st.lab st.lab st.ptn hs hs hptn hend hvals hc hr hlen ho hcells
  rw [he, hrename v (windowSet_lt hv)] at hat
  rw [he, hat] at hchild
  have ht := h.window_target hc hlen hr
  have hleft := (h.child hn hl false ht hv).spec
  have hright := (h.child hn hl false ht hw).spec
  exact subtreeKey_map G.graph G.graph σ.toPerm (Graph.context_iso G.graph G.graph σ hrows)
    tcLevel fuel (level + 1)
    (breakout n st.lab st.ptn (level + 1) tc v).1
    (breakout n st.lab st.ptn (level + 1) tc gamma[v]!).1
    (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1)
    hleft hright hchild hf

end Hex.GraphIso.Nauty.Sparse
