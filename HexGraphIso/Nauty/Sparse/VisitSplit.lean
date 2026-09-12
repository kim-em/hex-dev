/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VisitTarget
public import HexGraphIso.Nauty.Sparse.SubtreeSplit
public import HexGraphIso.Nauty.Invariant.Cursor
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The native target bitset is exactly its length-indexed label window. -/
theorem maketargetcell_window (g : Graph n) (lab ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) :
    let t := maketargetcell g lab ptn level tcLevel hint
    t.2.1 = windowSet n lab t.1 t.2.2 := by
  dsimp only [maketargetcell]
  have he : targetcell g lab ptn level tcLevel hint ≤
      cellEnd ptn level (targetcell g lab ptn level tcLevel hint) := cellEnd_ge
  have hw := worksetOf_eq_windowSet (n := n) lab
    (targetcell g lab ptn level tcLevel hint)
    (cellEnd ptn level (targetcell g lab ptn level tcLevel hint) -
      targetcell g lab ptn level tcLevel hint + 1) (by omega)
  rw [show targetcell g lab ptn level tcLevel hint +
      (cellEnd ptn level (targetcell g lab ptn level tcLevel hint) -
        targetcell g lab ptn level tcLevel hint + 1) - 1 =
      cellEnd ptn level (targetcell g lab ptn level tcLevel hint) by omega] at hw
  exact hw

/-- A cached target's fields denote the current label window; this uses
cache validity to identify all three fields with fresh native dispatch. -/
theorem Ready.target_window {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {st : State n} (h : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : numcells < n) (tcLevel : Nat) (hint : Int) :
    let t := maketargetCached (.ofGraph G.graph) st.lab st.ptn level tcLevel hint st.canong.scratch
    t.2.1 = windowSet n st.lab t.1 t.2.2.1 := by
  have hsize : st.ptn.size = n := h.ok.ptnSize
  have hcount : numcells = bcount st.ptn level n := h.ok.count
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn h.ok hl
    change st.ptn[st.ptn.size - 1]! ≤ level at he
    rwa [hsize] at he
  obtain ⟨label, hlabel⟩ := Label.ofArray?_exists (isPerm_of_cellsReach h.ok.labSize hn h.ok.reach)
  have he := maketargetCached_eq G.graph st.lab st.ptn level tcLevel hint st.canong.scratch
    label hlabel hsize hend h.scratch (Target.nonempty hsize hend (by rw [← hcount]; exact hc))
  have hw := congrArg (fun t : Nat × VSet n × Nat =>
    t.2.1 = windowSet n st.lab t.1 t.2.2) he
  rw [hw]
  exact maketargetcell_window _ _ _ _ _ _

/-- Each complete child maximum is unchanged when the specification's
fresh visit is replaced by the actual cached visit. -/
theorem NodeInv.visit_vertex {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells v : Nat} {st : State n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := visit (.ofGraph G.graph) level numcells st
    let f := refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells
    let t := maketargetcell (.ofGraph G.graph) f.lab f.ptn level tcLevel (-1)
    r.1 < n → n < fuel + (r.1 + 1) → t.2.1.mem v = true →
      vertexKey G.graph tcLevel fuel level f.lab f.ptn t.1 f.numcells v =
        vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn t.1 r.1 v := by
  intro r f t hc hf hv
  obtain ⟨hcount, _, _, hframe, hleft, hright⟩ := h.visit_equiv hn hl
  have hnum : f.numcells = r.1 := hcount
  have hfresh := h.spec.refined.1
  have hend : f.ptn[n - 1]! ≤ level := by
    simpa only [hfresh.node.ptnSize] using hfresh.node.ptnEnd
  have hbc : bcount f.ptn level n < n := by rw [← hfresh.count, hnum]; exact hc
  obtain ⟨hcell, hlen, hbound⟩ := maketargetcell_valid G.graph f.lab f.ptn level tcLevel (-1)
    hfresh.label hfresh.node.ptnSize hend hbc
  have hready : Ready G level f.numcells r.2.2 := by rw [hnum]; exact hright
  have hmem : (windowSet n f.lab t.1 t.2.2).mem v = true := by
    rw [← maketargetcell_window (.ofGraph G.graph) f.lab f.ptn level tcLevel (-1)]
    exact hv
  have he := hframe.vertex_key hleft hready hn hl hcell hlen hbound hmem
    (fuel := fuel) (tcLevel := tcLevel) (by rw [hcount]; exact hf)
  change vertexKey G.graph tcLevel fuel level f.lab f.ptn t.1 f.numcells v =
    vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn t.1 f.numcells v at he
  rw [hnum] at he
  rw [hnum]
  exact he

/-- An internal node is bounded exactly when all children of its actual
cached target are bounded. The keys use the actual visit's code, labels and
count; sufficient fuel prevents either enumeration from being truncated. -/
theorem NodeInv.visit_bound {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {st : State n} {bound : Key n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hf : n < (fuel + 1) + numcells) :
    let r := visit (.ofGraph G.graph) level numcells st
    let t := maketargetCached (.ofGraph G.graph) r.2.2.lab r.2.2.ptn level tcLevel (-1)
      r.2.2.canong.scratch
    r.1 < n →
      (Key.Le (subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells) bound ↔
        ∀ v, t.2.1.mem v = true → Key.Le (prefixKey [r.2.1]
          (vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn t.1 r.1 v)) bound) := by
  intro r t hc
  let f := refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells
  let target := maketargetcell (.ofGraph G.graph) f.lab f.ptn level tcLevel (-1)
  have hnum : f.numcells = r.1 := (h.visit_equiv hn hl).1
  have hcode : f.longcode = r.2.1 := (h.visit_equiv hn hl).2.1
  have hr : SpecNode G.graph level f.lab f.ptn f.active f.numcells := h.spec.refined.1
  have hmono : numcells ≤ f.numcells :=
    (refine_node G.graph level st.lab st.ptn st.active numcells h.spec.label h.spec.node h.spec.count).2.2.2
  have hchildfuel : n < fuel + (r.1 + 1) := by omega
  have hbc : bcount f.ptn level n < n := by rw [← hr.count, hnum]; exact hc
  have hd : discreteAt f.ptn level n = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hb := (discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mp he
    omega
  have hend : f.ptn[n - 1]! ≤ level := by simpa only [hr.node.ptnSize] using hr.node.ptnEnd
  obtain ⟨_, _, hbound⟩ := maketargetcell_valid G.graph f.lab f.ptn level tcLevel (-1)
    hr.label hr.node.ptnSize hend hbc
  change target.1 + target.2.2 ≤ n at hbound
  have htarget : (t.1, t.2.1, t.2.2.1) = target := h.visit_target hn hl tcLevel (-1) hc
  have hpos : t.1 = target.1 := congrArg Prod.fst htarget
  have hset : t.2.1 = target.2.1 := congrArg (fun x : Nat × VSet n × Nat => x.2.1) htarget
  rw [hpos, hset]
  have hkey (v : Nat) (hv : target.2.1.mem v = true) :
      prefixKey [r.2.1] (vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn target.1 r.1 v) =
      prefixKey [f.longcode] (vertexKey G.graph tcLevel fuel level f.lab f.ptn target.1 f.numcells v) := by
    rw [← h.visit_vertex hn hl hc hchildfuel hv, ← hcode]
  have hwindow : target.2.1 = windowSet n f.lab target.1 target.2.2 :=
    maketargetcell_window _ _ _ _ _ _
  constructor
  · intro hparent v hv
    rw [hkey v hv]
    rw [hwindow] at hv
    obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
    have hb := h.spec.child_le hf hd o ho
    change Key.Le (prefixKey [f.longcode]
      (vertexKey G.graph tcLevel fuel level f.lab f.ptn target.1 f.numcells f.lab[target.1 + o]!)) _ at hb
    rw [hat] at hb
    exact Key.le_trans hb hparent
  · intro hchildren
    apply h.spec.key_le hf hd
    intro o ho
    change o < target.2.2 at ho
    have hv : target.2.1.mem f.lab[target.1 + o]! = true := by
      rw [hwindow]
      exact mem_windowSet.mpr ⟨hr.node.labOk _ (by rw [hr.node.labSize]; omega),
        mem_segN_iff.mpr ⟨o, ho, rfl⟩⟩
    have hb := hchildren _ hv
    rw [hkey _ hv] at hb
    exact hb

/-- Some vertex of the actual cached target attains the complete node
maximum, with the actual visit's code prefixed to its child maximum. -/
theorem NodeInv.visit_attains {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hf : n < (fuel + 1) + numcells) :
    let r := visit (.ofGraph G.graph) level numcells st
    let t := maketargetCached (.ofGraph G.graph) r.2.2.lab r.2.2.ptn level tcLevel (-1)
      r.2.2.canong.scratch
    r.1 < n → ∃ v, t.2.1.mem v = true ∧ prefixKey [r.2.1]
      (vertexKey G.graph tcLevel fuel level r.2.2.lab r.2.2.ptn t.1 r.1 v) =
      subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells := by
  intro r t hc
  let f := refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells
  let target := maketargetcell (.ofGraph G.graph) f.lab f.ptn level tcLevel (-1)
  have hnum : f.numcells = r.1 := (h.visit_equiv hn hl).1
  have hcode : f.longcode = r.2.1 := (h.visit_equiv hn hl).2.1
  have hr : SpecNode G.graph level f.lab f.ptn f.active f.numcells := h.spec.refined.1
  have hmono : numcells ≤ f.numcells :=
    (refine_node G.graph level st.lab st.ptn st.active numcells h.spec.label h.spec.node h.spec.count).2.2.2
  have hchildfuel : n < fuel + (r.1 + 1) := by omega
  have hbc : bcount f.ptn level n < n := by rw [← hr.count, hnum]; exact hc
  have hd : discreteAt f.ptn level n = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hb := (discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mp he
    omega
  have hend : f.ptn[n - 1]! ≤ level := by simpa only [hr.node.ptnSize] using hr.node.ptnEnd
  obtain ⟨_, _, hbound⟩ := maketargetcell_valid G.graph f.lab f.ptn level tcLevel (-1)
    hr.label hr.node.ptnSize hend hbc
  change target.1 + target.2.2 ≤ n at hbound
  obtain ⟨o, ho, hkey⟩ := h.spec.child_attains (tcLevel := tcLevel) hf hd
  change o < target.2.2 at ho
  have hv : target.2.1.mem f.lab[target.1 + o]! = true := by
    rw [maketargetcell_window (.ofGraph G.graph) f.lab f.ptn level tcLevel (-1)]
    exact mem_windowSet.mpr ⟨hr.node.labOk _ (by rw [hr.node.labSize]; omega),
      mem_segN_iff.mpr ⟨o, ho, rfl⟩⟩
  have htarget : (t.1, t.2.1, t.2.2.1) = target := h.visit_target hn hl tcLevel (-1) hc
  have hpos : t.1 = target.1 := congrArg Prod.fst htarget
  have hset : t.2.1 = target.2.1 := congrArg (fun x : Nat × VSet n × Nat => x.2.1) htarget
  refine ⟨f.lab[target.1 + o]!, by rw [hset]; exact hv, ?_⟩
  rw [hpos, ← h.visit_vertex hn hl hc hchildfuel hv, ← hcode]
  exact hkey

/-- A discrete actual visit attains exactly the specification's node key,
using the literal parsed label and emitted terminal code. -/
theorem NodeInv.visit_leaf {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells : Nat} {st : State n} {label : Label n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := visit (.ofGraph G.graph) level numcells st
    r.1 = n → Label.ofArray? n r.2.2.lab = some label →
      subtreeKey G.graph tcLevel (fuel + 1) level st.lab st.ptn st.active numcells =
        ⟨[r.2.1, codeSentinel], G.graph.relabel label.perm⟩ := by
  intro r hc hp
  let f := refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells
  obtain ⟨hcount, hcode, _, hframe, _, hright⟩ := h.visit_equiv hn hl
  have hnum : f.numcells = r.1 := hcount
  have hlong : f.longcode = r.2.1 := hcode
  have hr : SpecNode G.graph level f.lab f.ptn f.active f.numcells := h.spec.refined.1
  have hd : discreteAt f.ptn level n = true :=
    (discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mpr
      (hr.count.symm.trans (hnum.trans hc))
  have hperm : cellsPerm f.ptn level f.lab r.2.2.lab := hframe.effect.perm
  have he := discrete_pointwise hperm (Nat.le_of_eq hr.node.ptnSize.symm) hr.node.ptnEnd hd
  have hsize : r.2.2.lab.size = n := hright.ok.labSize
  have harray : f.lab = r.2.2.lab := by
    apply Array.ext (hr.node.labSize.trans hsize.symm)
    intro i hi hj
    have hget := he i (by rw [hr.node.labSize] at hi; exact hi)
    simpa only [getElem!_pos f.lab i hi, getElem!_pos r.2.2.lab i hj] using hget
  have hparse : Label.ofArray? n f.lab = some label := by rw [harray]; exact hp
  rw [subtreeKey_discrete hd hparse, hlong]

end Hex.GraphIso.Nauty.Sparse
