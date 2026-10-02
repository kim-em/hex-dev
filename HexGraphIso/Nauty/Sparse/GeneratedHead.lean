/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GeneratedTail
public import HexGraphIso.Nauty.Sparse.FirstContains
public import HexGraphIso.Nauty.Sparse.FirstWitness
public import HexGraphIso.Nauty.Sparse.ReferenceOrbit
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxControl
import all HexGraphIso.Nauty.Sparse.ChildPath
import all HexGraphIso.Nauty.Sparse.PathState
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Nauty.Generation.Frame
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual guiding child and its complete sibling suffix generate
the guide's whole point-stabilizer orbit. The stored reference, its orbit
transport, and every suffix invariant are derived from the first descent. -/
theorem FirstInput.orbit {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    {base : List (Fin n)} {gs : List (Perm n)}
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
    (htrace : Generation.Realizes G gs
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1)
        f.level f.numcells f.entry).2.genTrace.toList) :
    let guide : Fin n := ⟨tv, VSet.mem_lt (VSet.nextElem_mem htv)⟩
    ∀ v, Aut.Orbit G.toDense base guide v → Nauty.Generation.Carries G.toDense gs base guide v := by
  intro guide
  let g := Graph.ofGraph G.graph
  let r := Generic.prepareFirst g tcLevel f.level f.numcells f.entry
  let R := State.refined g f.level f.numcells f.entry
  let l : Loop n := ⟨f, true⟩
  let c := l.cell G.graph tcLevel
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let raw := Generic.node true g (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw.2)
  let back := p.firstBack G.graph tcLevel fuel
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi (VSet.nextElem_mem htv) []
  have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
  have hcell : c.Valid G := hselected.1
  have hset : p.cell = c.vertices := hselected.2
  have hr : RefineSt.Ready G.graph f.level R := h.entry.frame.node.refined
  have hfields : p.state.lab = R.lab ∧ p.state.ptn = R.ptn := by
    have hh := prepareFirst_partition g tcLevel f.level f.numcells f.entry
    change (cheapCheck true f.level r.2.2.2.2).lab = R.lab ∧
      (cheapCheck true f.level r.2.2.2.2).ptn = R.ptn
    unfold cheapCheck
    split <;> exact ⟨hh.1, hh.2.1⟩
  have hfixed : p.state.fixedpts = f.entry.fixedpts := by
    change (cheapCheck true f.level r.2.2.2.2).fixedpts = f.entry.fixedpts
    rw [cheap_fixed]
    exact target_fixed true g tcLevel f.level r.1
      (recordFirst f.level (f.code G.graph) (visit g f.level f.numcells f.entry).2.2)
  have hbaseReady : ∀ b : Fin n, p.state.fixedpts.mem b.val = true ↔ b ∈ base := by
    intro b
    rw [hfixed]
    exact hbase b
  have hpath : PathInv G f.level p.state :=
    ((((h.path.visit h.entry.frame.node).record (f.code G.graph)).target true tcLevel r.1).cheap true)
  have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
  obtain ⟨bs, fs, hs, heq, hsame, hsuffix⟩ := h.suffix hi htv horbit path hf
  change SweepInput G tcLevel l bs fs (p.cell.nextElem (some tv)) p.cell back parents at hs
  obtain ⟨targets, key, href, hm⟩ := hch.witness path (by change n + 1 ≤ f.level + 1 + fuel; omega)
  have hreference : back.reference = raw.2.reference :=
    (referencePolicy g (n + 2) tcLevel).recover f.level left
  have hboundary : raw.2.allsamelevel ≤ back.allsamelevel := by
    have he := recover_same (n + 2) f.level left
    change back.allsamelevel = raw.2.allsamelevel at he
    exact Nat.le_of_eq he.symm
  have hfloor : f.level < raw.2.allsamelevel := by
    have hh := firstPath_floor (inf := n + 2) path
    change f.level + 1 ≤ raw.2.allsamelevel ∧ _ at hh
    omega
  have hmem : c.vertices.mem tv = true := hset ▸ VSet.nextElem_mem htv
  obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp hmem).2
  change R.lab[c.tc + o]! = tv at hat
  have hrefChild : Generation.RefPath G.graph tcLevel raw.2.allsamelevel (f.level + 1)
      (R.child g f.level c.tc R.lab[c.tc + o]! ch.entry.canong.scratch) targets key := by
    change Generation.RefPath G.graph tcLevel raw.2.allsamelevel (f.level + 1)
      (State.refined g (f.level + 1) (r.1 + 1)
        ((policy (n := n)).child true f.level r.2.1.toNat tv (cheapCheck true f.level r.2.2.2.2))) targets key at href
    rw [firstChild_refined] at href
    rw [hat]
    exact href
  have hmove : ∀ v : Fin n, Aut.Orbit G.toDense base guide v → ∀ j, j < c.len →
      R.lab[c.tc + j]! = v.val →
      Generation.ChildPath G.graph tcLevel raw.2.allsamelevel f.level R c.tc targets key j := by
    intro v hv j hj hjv
    exact Generation.RefPath.orbit hr hpath hfields.1 hfields.2
      (fun b hb => (hbaseReady b).mp hb) hcell.window hcell.range hcell.size ho hj
      hch.entry.frame.node.scratch (Scratch.fresh_valid n R.lab R.ptn (f.level + 1)).toBounded hat hjv hv hrefChild
  have hfixFrame : ∀ gamma, CellStab R.ptn f.level R.lab gamma → ∀ b ∈ base, gamma[b.val]! = b.val := by
    intro gamma hg
    apply Nauty.Generation.frame_fixes hpath.fixed hp.ready.ok.labSize
      (fun b hb => (hbaseReady b).mpr hb)
    change CellStab p.state.ptn f.level p.state.lab gamma
    rwa [hfields.1, hfields.2]
  have hwindow : Nauty.Generation.Cover G.toDense gs base guide p.cell none := by
    apply Nauty.Generation.Cover.start
    intro v hv
    obtain ⟨q, hq, hfix, rfl⟩ := hv
    have he : p.cell = windowSet n p.state.lab c.tc c.len := by
      rw [hfields.1]
      exact hset
    rw [he]
    apply Generation.window_stable hpath (labOk_of_reach hp.ready.ok.labSize hp.ready.ok.reach)
      (by rw [hfields.2]; exact hcell.window)
      (by change c.tc + c.len ≤ p.state.frame.lab.size; rw [hp.ready.ok.labSize]; exact hcell.range)
      ((GraphIso.Sparse.isIso_toDense G G q).mp hq)
      (fun b hb => hfix b ((hbaseReady b).mp hb)) guide
    rw [← he]
    exact VSet.nextElem_mem htv
  have hcover := hwindow.advance (tv := guide) htv (fun _ => Nauty.Generation.Carries.refl G.toDense gs base guide)
  have hcanon : Nauty.Generation.CanonPast f.level c.tc (some tv) back := by
    have hpast : Nauty.Generation.CanonPast f.level p.tc none p.state :=
      Nauty.Generation.CanonPast.start (by
        have hh := (f.firstParent_refs G.graph tcLevel [] tv).2.2.2
        change p.state.gcaCanon = f.entry.gcaCanon at hh
        rw [hh, h.canon]
        exact h.entry.frame.positive)
    exact hp.ready.canon_past hn h.entry.frame.positive true true hp.target hpast htv
  have hfirst : back.firstlab[c.tc]! = guide.val := by
    have hh := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2) hreference
    change back.firstlab = raw.2.firstlab at hh
    rw [hh]
    exact (child_first_store hp.ready hn h.entry.frame.positive true hp.target (VSet.nextElem_mem htv) path).2.2
  have htraceTail : Generation.Realizes G gs
      (Generic.sweep true g (n + 2) tcLevel fuel n f.level c.numcells p.tc tv
        (p.cell.nextElem (some tv)) p.cell (if back.orbits[tv]! == tv then 1 else 0) back).2.2.genTrace.toList := by
    rw [← hsuffix]
    apply htrace.mono
    intro gamma hg
    exact Array.mem_toList_iff.mpr (f.first_contains (by change r.1 ≠ n; change r.1 < n at hi; omega)
      htv (Array.mem_toList_iff.mp hg))
  apply hs.generated_tail (cfuel := n) (tv1 := tv)
    (index := if back.orbits[tv]! == tv then 1 else 0) rfl hf (fun _ _ => by omega) (by
    intro _ v hv
    have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hh
    omega) (hm.congr hreference) heq hfloor hboundary hmove hfixFrame rfl hcanon hcover hfirst
  exact htraceTail

end Hex.GraphIso.Nauty.Sparse.Max
