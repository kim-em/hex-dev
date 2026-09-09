/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Contract
public import HexGraphIso.Nauty.Policy.Cheap.Key
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Frame
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

/-- Two valid states at the same sweep level agree on their whole partition
when their search effect preserves every closed boundary. -/
theorem SearchOut.ptn_eq {n k level numcells : Nat} {G : Colored n k}
    {st out : Search n} (h : SearchOut G level level st out)
    (hs : SearchOk G level numcells st) (ho : SearchOk G level numcells out) :
    out.ptn = st.ptn := by
  apply Array.ext h.ptnSize
  intro i hi ho'
  rw [← getElem!_pos out.ptn i hi, ← getElem!_pos st.ptn i ho']
  have hin : i < n := by rwa [hs.ptnSize] at ho'
  rcases hs.vals i hin with hc | hc
  · exact h.low i (Or.inl hc)
  · rcases ho.vals i hin with hd | hd
    · exact h.low i (Or.inr hd)
    · exact hd.trans hc.symm

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A valid frozen node prepares a valid sweep partition. -/
theorem Loop.prepare_ok {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {l : Loop n} (h : l.node.Valid G) :
    SearchOk G l.node.level (l.prepare ctx tcLevel).1
      (l.prepare ctx tcLevel).2.2.2.2 := by
  have hn0 : 0 < n := by have := h.positive; have := h.depth; omega
  let R := reachPolicy G ctx tcLevel hn0
  let v := visit ctx l.node.level l.node.numcells l.node.entry
  let c := if l.first then recordFirst l.node.level v.2.1 v.2.2
    else compareCodes l.node.level v.2.1 v.2.2
  have hv : SearchOk G l.node.level v.1 v.2.2 :=
    (R.visit _ _ _ h.positive h.partition).1
  have hc : SearchOk G l.node.level v.1 c := by
    dsimp only [c]
    split
    · exact (R.record _ _ _ _ hv).ok
    · exact (R.compare _ _ _ _ hv).ok
  exact (R.cheap l.first _ _ _ (R.target l.first _ _ _ h.positive hc).1.ok).ok

/-- Preparing a sweep retains the refined partition and cell count. -/
theorem Loop.prepare_frame (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) :
    let r := l.node.entry.refined ctx l.node.level l.node.numcells
    let p := l.prepare ctx tcLevel
    p.1 = r.numcells ∧ p.2.2.2.2.lab = r.lab ∧ p.2.2.2.2.ptn = r.ptn := by
  dsimp only [Loop.prepare]
  have ht := chooseTarget_frame l.first ctx tcLevel l.node.level
    (visit ctx l.node.level l.node.numcells l.node.entry).1
    (if l.first then recordFirst l.node.level
      (visit ctx l.node.level l.node.numcells l.node.entry).2.1
      (visit ctx l.node.level l.node.numcells l.node.entry).2.2
    else compareCodes l.node.level
      (visit ctx l.node.level l.node.numcells l.node.entry).2.1
      (visit ctx l.node.level l.node.numcells l.node.entry).2.2)
  simp only [cheapCheck, apply_ite Search.lab, apply_ite Search.ptn, ite_self]
  rw [ht.1, ht.2.1]
  all_goals cases hf : l.first
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact ⟨rfl, rfl, rfl⟩
    | exact ⟨rfl, (compareCodes_frame _ _ _).1, (compareCodes_frame _ _ _).2.1⟩

/-- A cheap suspended parent's current shape supplies the small-cell
invariant at its frozen refined entry. -/
theorem Parent.small {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel)
    (hbase : SearchOk G p.loop.node.level (p.loop.prepare ctx tcLevel).1
      (p.loop.prepare ctx tcLevel).2.2.2.2)
    (hcheap : p.state.noncheaplevel ≤ p.loop.node.level) :
    SubtreeOk ctx p.loop.node.level
      (p.loop.node.entry.refined ctx p.loop.node.level p.loop.node.numcells) := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  obtain ⟨hnc, hl, hp⟩ := p.loop.prepare_frame ctx tcLevel
  have he := h.effect.ptn_eq hbase h.partition
  change p.state.ptn = (p.loop.prepare ctx tcLevel).2.2.2.2.ptn at he
  have hperm := h.effect.perm

  have heq := h.equitable
  have hshape := (h.small hcheap).shape
  rw [he] at heq hshape
  have hback := heq.reorder (cellsPerm_symm hperm) hbase.ptnSize
    (searchOk_end hn0 hbase h.node.positive)
  exact hbase.subtree hn0 h.node.positive hl.symm hp.symm hnc.symm hback hshape

/-- A small-cell parent with the specification target has exactly the
key of its actual selected child, even after the parent was reordered. -/
theorem Parent.cheap_key {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel)
    (hbase : SearchOk G p.loop.node.level (p.loop.prepare ctx tcLevel).1
      (p.loop.prepare ctx tcLevel).2.2.2.2)
    (hsmall : SubtreeOk ctx p.loop.node.level
      (p.loop.node.entry.refined ctx p.loop.node.level p.loop.node.numcells))
    (hselected : specTargetcell ctx
      (p.loop.node.entry.refined ctx p.loop.node.level p.loop.node.numcells).lab
      (p.loop.node.entry.refined ctx p.loop.node.level p.loop.node.numcells).ptn
      p.loop.node.level tcLevel = (p.loop.prepare ctx tcLevel).2.1.toNat)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    p.loop.node.key ctx tcLevel = (p.child ctx tcLevel).key ctx tcLevel := by
  let r := p.loop.node.entry.refined ctx p.loop.node.level p.loop.node.numcells
  let q := p.loop.prepare ctx tcLevel
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  obtain ⟨hnc, hl, hp⟩ := p.loop.prepare_frame ctx tcLevel
  change q.1 = r.numcells at hnc
  change q.2.2.2.2.lab = r.lab at hl
  change q.2.2.2.2.ptn = r.ptn at hp
  change specTargetcell ctx r.lab r.ptn p.loop.node.level tcLevel = q.2.1.toNat at hselected
  have hL : 2 ≤ q.2.2.2.1 := h.len
  have hR : q.2.1.toNat + q.2.2.2.1 ≤ n := h.range
  have hc : IsCell r.ptn p.loop.node.level q.2.1.toNat q.2.2.2.1 := by
    rw [← hp]; exact h.cell
  have hend := cellEnd_of_isCell hc (by have := h.len; omega)
    (by rw [hsmall.it.ok.ptnSize]; exact h.range)
  have htarget : (specMaketargetcell ctx r.lab r.ptn p.loop.node.level tcLevel).1 =
      q.2.1.toNat := hselected
  have hlen : (specMaketargetcell ctx r.lab r.ptn p.loop.node.level tcLevel).2.2 =
      q.2.2.2.1 := by
    simp only [specMaketargetcell, hselected, hend]
    omega
  have hdisc : discreteAt r.ptn p.loop.node.level n = false := by
    rw [discreteAt, List.all_eq_false]
    refine ⟨(q.2.1.toNat, q.2.1.toNat + q.2.2.2.1 - 1),
      isCell_mem_cells hc (Nat.le_of_eq hsmall.it.ok.ptnSize.symm) hsmall.it.ok.ptnEnd
        (by omega), ?_⟩
    simpa using (Nat.ne_of_lt (show q.2.1.toNat < q.2.1.toNat + q.2.2.2.1 - 1 by omega))
  have hv : (windowSet n q.2.2.2.2.lab q.2.1.toNat q.2.2.2.1).mem p.chosen = true := by
    have hw := h.effect.window_eq h.cell
    change windowSet n q.2.2.2.2.lab q.2.1.toNat q.2.2.2.1 =
      windowSet n p.state.lab q.2.1.toNat q.2.2.2.1 at hw
    rw [hw]
    exact h.chosen
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  have hdepth := h.node.depth
  have hm := hsmall.node_key hgsz hsymm hloop hdisc
    (o := o) (tcLevel := tcLevel) (fuel := n - p.loop.node.level)
    (by change o < (specMaketargetcell ctx r.lab r.ptn p.loop.node.level tcLevel).2.2
        rw [hlen]; exact ho) (by omega) p.loop.node.codes
  have hnode : p.loop.node.key ctx tcLevel = p.loop.key ctx tcLevel p.chosen := by
    rw [Frame.key, show n + 1 - p.loop.node.level = n - p.loop.node.level + 1 by omega]
    rw [hm]
    change prefixKey (p.loop.codes ctx)
      (childKey ctx tcLevel (n - p.loop.node.level) p.loop.node.level r.lab r.ptn
        (specMaketargetcell ctx r.lab r.ptn p.loop.node.level tcLevel).1 r.numcells o) = _
    rw [htarget]
    rw [Loop.key, ← he, vertexKey_offset]
    rw [hl, hp, hnc]
  have hkey := h.effect.vertex_key (ctx := ctx) (tcLevel := tcLevel)
    hbase h.partition hn0 h.node.positive h.cell h.len h.range hv
    (fuel := n - p.loop.node.level) (by omega)

  rw [hnode, Loop.key, hkey]
  unfold Frame.key Parent.child
  simp only [show n + 1 - (p.loop.node.level + 1) = n - p.loop.node.level by omega]
  cases hf : p.loop.first <;> rfl

end Hex.GraphIso.Nauty.Max
