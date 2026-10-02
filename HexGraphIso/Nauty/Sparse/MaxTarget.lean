/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SmallKey
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native cached target coordinates delimit a complete nonsingleton cell. -/
theorem Ready.cached_cell {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {st : State n} (h : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : numcells < n) (tcLevel : Nat) (hint : Int) :
    let t := maketargetCached (.ofGraph G.graph) st.lab st.ptn level tcLevel hint st.canong.scratch
    IsCell st.ptn level t.1 t.2.2.1 ∧ 1 < t.2.2.1 ∧ t.1 + t.2.2.1 ≤ n := by
  have hsize : st.ptn.size = n := h.ok.ptnSize
  have hcount : numcells = bcount st.ptn level n := h.ok.count
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn h.ok hl
    change st.ptn[st.ptn.size - 1]! ≤ level at he
    rwa [hsize] at he
  have hperm := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  obtain ⟨label, hlabel⟩ := Label.ofArray?_exists hperm
  have he := maketargetCached_eq G.graph st.lab st.ptn level tcLevel hint st.canong.scratch
    label hlabel hsize hend h.scratch (Target.nonempty hsize hend (by rw [← hcount]; exact hc))
  have ht := congrArg (fun t : Nat × VSet n × Nat =>
    IsCell st.ptn level t.1 t.2.2 ∧ 1 < t.2.2 ∧ t.1 + t.2.2 ≤ n) he
  rw [ht]
  exact maketargetcell_valid G.graph st.lab st.ptn level tcLevel hint
    hperm hsize hend (by rw [← hcount]; exact hc)

namespace Max

/-- The complete unhinted target computed from the frozen entry's actual
cached visit, before mutable target filtering or sibling reordering. -/
def Frame.target (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) : Cell n :=
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  let t := maketargetCached (.ofGraph G) v.2.2.lab v.2.2.ptn f.level tcLevel (-1) v.2.2.canong.scratch
  ⟨f.level, v.1, t.1, t.2.2.1, f.codes ++ [v.2.1], v.2.2⟩

theorem Frame.Valid.target {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {f : Frame n}
    (h : f.Valid G) (hc : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n) :
    (f.target G.graph tcLevel).Valid G := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hv := h.node.visit_ready hn h.positive
  obtain ⟨hw, hs, hr⟩ := hv.cached_cell hn h.positive hc tcLevel (-1)
  refine ⟨h.positive, ?_, hv, hw, hs, hr⟩
  change (f.codes ++ [_]).length = f.level
  simp only [List.length_append, List.length_singleton, h.length]

/-- Frozen node coverage is precisely coverage of its complete actual
cached target's vertex keys. Both sides include every ancestor code. -/
theorem Frame.Valid.target_cover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {best : Option (Key n)} (h : f.Valid G)
    (hc : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n) :
    Covers (f.key G.graph tcLevel) best ↔
      ∀ v, (f.target G.graph tcLevel).vertices.mem v = true →
        Covers ((f.target G.graph tcLevel).key G.graph tcLevel v) best := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hd := h.depth
  have hcount := h.node.spec.depth
  have hf : n + 1 - f.level = n - f.level + 1 := by omega
  have hcover := h.node.visit_cover (tcLevel := tcLevel) (fuel := n - f.level) (cs := f.codes)
    (best := best) hn h.positive (by omega) hc
  have hw := (h.node.visit_ready hn h.positive).target_window hn h.positive hc tcLevel (-1)
  rw [hw] at hcover
  simpa only [Frame.key, hf, Frame.target, Cell.vertices, Cell.key] using hcover

/-- With the cheap shape, any complete native target child attains the
whole frozen node maximum. This supplies the coverage step needed when
a return skips the remaining children of a cheap ancestor. -/
theorem Frame.Valid.small_key {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {v : Nat} (h : f.Valid G)
    (hc : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hshape : NodeShape n f.level (visit (.ofGraph G.graph) f.level f.numcells f.entry).2.2.ptn)
    (hv : (f.target G.graph tcLevel).vertices.mem v = true) :
    f.key G.graph tcLevel = (f.target G.graph tcLevel).key G.graph tcLevel v := by
  let c := f.target G.graph tcLevel
  have hvalid := h.target (tcLevel := tcLevel) hc
  have hp : Covers (f.key G.graph tcLevel) (some (c.key G.graph tcLevel v)) := by
    apply (h.target_cover hc).mpr
    intro w hw
    rw [hvalid.uniform hshape hw hv tcLevel]
    exact ⟨_, rfl, Key.le_refl _⟩
  have hchild : Covers (c.key G.graph tcLevel v) (some (f.key G.graph tcLevel)) :=
    (h.target_cover hc).mp ⟨_, rfl, Key.le_refl _⟩ v hv
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨b, hb, hcb⟩ := hchild
  cases ha
  cases hb
  exact Key.le_antisymm hpa hcb

/-- A passing native cheap guard makes an actual individualized child
attain its parent's whole key, including after sibling reordering. -/
theorem Frame.Valid.cheap_child {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {st : State n} {v : Nat} (h : f.Valid G)
    (hc : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hguard : cheapautom (visit (.ofGraph G.graph) f.level f.numcells f.entry).2.2.ptn f.level n = true)
    (he : FrameOut G f.level f.level (f.target G.graph tcLevel).entry st)
    (hs : Ready G f.level (f.target G.graph tcLevel).numcells st)
    (hv : (f.target G.graph tcLevel).vertices.mem v = true) (first : Bool) :
    f.key G.graph tcLevel = ((f.target G.graph tcLevel).child first st v).key G.graph tcLevel := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hshape := ((h.node.visit_ready hn h.positive).small hn h.positive hguard).shape
  exact (h.small_key hc hshape hv).trans ((h.target hc).child_key he hs first hv tcLevel).symm

end Max
end Hex.GraphIso.Nauty.Sparse
