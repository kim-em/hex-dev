/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxDescent
import all HexGraphIso.Nauty.Sparse.MaxControl
import all HexGraphIso.Nauty.Sparse.MaxCosetState
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- An internal off-path node establishes the complete initial sweep
context from its literal native preparation. The selected bitset is the
whole frozen cell, so ranked coverage starts with every child live. -/
theorem NodeInput.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G tcLevel f bs fs parents)
    (hi : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .internal) :
    let l : Loop n := ⟨f, false⟩
    let p := l.prepare G.graph tcLevel
    SweepInput G tcLevel l bs fs (p.2.2.1.nextElem none) p.2.2.1 p.2.2.2.2 parents := by
  let l : Loop n := ⟨f, false⟩
  let p := l.prepare G.graph tcLevel
  let c := l.cell G.graph tcLevel
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  let prepared := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have ht := h.codes.prepare (tcLevel := tcLevel) hn h.frame.positive
  have hc : v.1 < n := by
    have hcount : prepared.1 = bcount prepared.2.2.2.2.2.ptn f.level n := ht.ready.ok.count
    have hb := bcount_le prepared.2.2.2.2.2.ptn f.level n
    have hne := classify_open hi
    change prepared.1 ≠ n at hne
    change prepared.1 < n
    omega
  have hselected := l.selected h.frame hc (fun _ => hi)
  have hcell : c.Valid G := hselected.1
  have hset : p.2.2.1 = c.vertices := hselected.2
  have hmember : c.vertices.mem c.entry.lab[c.tc]! = true := by
    apply mem_windowSet.mpr
    refine ⟨?_, mem_segN_iff.mpr ⟨0, hcell.window.1, by simp⟩⟩
    have hrange : c.tc + c.len ≤ n := hcell.range
    have hlen : 1 < c.len := hcell.size
    have hsize : c.entry.lab.size = n := hcell.ready.ok.labSize
    exact (labOk_of_reach hcell.ready.ok.labSize hcell.ready.ok.reach) _ (by
      change c.tc < c.entry.lab.size
      rw [hsize]
      omega)
  have hparent : (f.otherParent G.graph tcLevel bs c.entry.lab[c.tc]!).Valid G tcLevel :=
    h.frame.other_parent h.machine hc (by change p.2.2.1.mem _ = true; rw [hset]; exact hmember)
  have hparts := h.pairs.prepare hn h.frame.positive
  have hpairs : PairsReady G tcLevel f.level c.numcells p.2.2.2.2 :=
    ⟨hparts.1.cheap false, hparts.2.1.cheap false, hparts.2.2.1.cheap false f.level,
      hparts.2.2.2.1.cheap hn h.frame.positive ht.ready false, cheap_bound false hparts.2.2.2.2⟩
  have hm := h.machine.prepare tcLevel f.numcells (by have := h.frame.length; have := h.frame.depth; omega)
  rw [h.frame.length] at hm
  have hmachine : Comparison G.graph c.codes bs fs p.2.2.2.2 := hm.1.cheap false f.level
  have hkey : State.key G.graph bs p.2.2.2.2 = State.key G.graph bs f.entry :=
    f.otherParent_key G.graph tcLevel bs 0
  have hscope : Scope G tcLevel f bs p.2.2.2.2 parents := h.scope.change
    (by rw [hkey]; exact Grows.refl _) (f.otherParent_boundary G.graph tcLevel bs 0)
  obtain ⟨hrecord, hroute⟩ := h.codes.recorded hn h.frame.positive hc
  have href := f.otherParent_refs G.graph tcLevel bs 0
  have hgc : p.2.2.2.2.gcaFirst = f.entry.gcaFirst := href.2.1
  have hga : p.2.2.2.2.gcaCanon = f.entry.gcaCanon := href.2.2.2
  have hcap : p.2.2.2.2.wsCap = f.entry.wsCap :=
    l.preserve (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel f.entry.wsCap) rfl
  change SweepInput G tcLevel l bs fs (p.2.2.1.nextElem none) p.2.2.1 p.2.2.2.2 parents
  refine ⟨h.frame, hc, hcell, ht.cheap false, hpairs, hmachine, ?_,
    ?_, ?_, fun _ hv => VSet.nextElem_mem hv, ?_, ?_,
    hscope, ?_, ?_, h.ranked,
    ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hparent.effect
  · exact hparent.target
  · intro w hw
    change p.2.2.1.mem w = true at hw
    rwa [hset] at hw
  · exact hparent.choice
  · exact hparent.small
  · exact h.guides.other_prepare bs 0
  · exact h.cosets.other_prepare bs 0
  · exact h.traces.prepare h.scope h.frame 0
  · exact l.preserve (orbitPolicy G (n + 2) tcLevel) h.orbits
  · intro he
    cases he
  · intro tv
    exact f.otherParent_guided (by have := h.counters; omega) h.counters.2.2 bs tv
  · change 0 < p.2.2.2.2.gcaFirst ∧ p.2.2.2.2.gcaFirst ≤ p.2.2.2.2.gcaCanon ∧
      p.2.2.2.2.gcaCanon ≤ f.level
    rw [hgc, hga]
    exact ⟨h.counters.1, h.counters.2.1, Nat.le_of_lt h.counters.2.2⟩
  · intro he
    cases he
  · intro _
    change p.2.2.2.2.gcaFirst < f.level
    rw [hgc]
    have := h.counters
    omega
  · change 0 < p.2.2.2.2.wsCap
    rw [hcap]
    exact h.capacity
  · simpa only [l, p, Loop.cell, Loop.prepare, prepareOther, Bool.false_eq_true, ite_false]
      using hrecord.cheap false ht.ancestor
  · simpa only [l, p, Loop.cell, Loop.prepare, prepareOther, Bool.false_eq_true, ite_false]
      using hroute.cheap false
  · change c.Cover G.graph tcLevel (Remaining (p.2.2.1.nextElem none) p.2.2.1)
      (State.key G.graph bs p.2.2.2.2)
    rw [hset]
    exact Cell.Cover.initial G.graph tcLevel c _
  · have hcomp := (h.frame.node.visit_ready hn h.frame.positive).compare v.2.1
    have hphase := hcomp.ready.target_phase (tcLevel := tcLevel) hn h.frame.positive hc
    rcases hphase with hnonpos | hcursor
    · left
      change (cheapCheck false f.level prepared.2.2.2.2.2).compCanon ≤ 0
      unfold cheapCheck
      split <;> exact hnonpos
    · exact Or.inr ⟨rfl, hcursor⟩

end Hex.GraphIso.Nauty.Sparse.Max
