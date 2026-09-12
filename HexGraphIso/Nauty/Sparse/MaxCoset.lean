/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxCosetState
public import HexGraphIso.Nauty.Sparse.MaxRank
public import HexGraphIso.Nauty.Sparse.MaxAutoCanon
import all HexGraphIso.Nauty.Sparse.MaxCosetState
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Native preparation, classification and leaf action retain the
selected first-path coset index. -/
theorem Frame.emit_coset (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) :
    (f.emit G tcLevel).2.cosetindex = f.entry.cosetindex := by
  unfold Frame.emit
  rw [leafExit_coset, classify_coset]
  dsimp only [prepareOther]
  rw [chooseTarget_coset, compare_coset]
  rfl

theorem Frame.emit_first (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) :
    (f.emit G tcLevel).2.gcaFirst = f.entry.gcaFirst := by
  unfold Frame.emit
  rw [leafExit_gca, (classify_controls ..).1]
  dsimp only [prepareOther]
  rw [(chooseTarget_controls ..).1]
  exact (gcaPolicy (.ofGraph G) (n + 2) tcLevel).compare f.level
    (visit (.ofGraph G) f.level f.numcells f.entry).2.1 _

/-- The actual canonical-admission branch returns to its canonical
ancestor, or returns to the first ancestor after acquiring a smaller
representative for the selected coset index. -/
theorem canon_exit (level : Nat) (st : State n) :
    let out := leafExit .autoCanon level st
    (∃ short, out.1 = .unwind st.gcaCanon short) ∨
      (out.1 = .unwind st.gcaFirst false ∧ out.2.orbits[out.2.cosetindex]! < out.2.cosetindex) := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals simp only [admit_gca, admit_canon]
  all_goals first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨trivial, by assumption⟩

/-- The coset return satisfies the full maximum contract. Its selected
ancestor comes from the saved-index invariant, and native trace words
transport its interrupted child to an already covered smaller child. -/
theorem Frame.Valid.coset_return {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry) (hs : Scope G tcLevel f bs f.entry parents)
    (hcoset : Cosets f.entry parents)
    (hrank : ∀ t p, parents t = some p → p.Ranked G.graph tcLevel)
    (hframes : ∀ t p, parents t = some p → p.first = true → TraceFrame G p.node.level p.state f.entry)
    (ho : OrbitTrace G f.entry) (hpos : 0 < f.entry.gcaFirst) (hlt : f.entry.gcaFirst < f.level)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoCanon)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind f.entry.gcaFirst false)
    (hsmall : (f.emit G.graph tcLevel).2.orbits[(f.emit G.graph tcLevel).2.cosetindex]! <
      (f.emit G.graph tcLevel).2.cosetindex) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let out := (f.emit G.graph tcLevel).2
  have hdone : (f.emit G.graph tcLevel).1 ≠ .done := by rw [hexit]; intro he; cases he
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  obtain ⟨_, _, hbound, hcover⟩ := h.leaf_bound hi hc (canon_discrete ha)
  refine ⟨hbound, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hcover
  · rename_i hne
    obtain ⟨p, hp⟩ := hs.complete f.entry.gcaFirst hpos hlt
    obtain ⟨_, _, hlevel, hv⟩ := hs.valid f.entry.gcaFirst p hp
    obtain ⟨hfirst, hindex⟩ := hcoset _ p hp rfl
    have hframe := (hframes _ p hp hfirst).node hv.ready hn hv.node.positive
      (by omega) h.node false tcLevel 1
    have horbit := node_orbitTrace G false (n + 2) tcLevel 1 f.level f.numcells f.entry ho
    have htrace := node_trace G hn tcLevel 1 f.level f.numcells f.entry h.positive hi.toTraceEntry
    rw [Generic.node, f.emit_step _ hdone] at hframe horbit htrace
    have hsm : out.orbits[p.chosen]! < p.chosen := by
      rwa [f.emit_coset, hindex] at hsmall
    have hd := (hrank _ p hp).orbit_cover hv horbit htrace hframe.trace hsm
      ((hs.grows _ p hp).trans hbound.grows)
    exact hs.child_witness hp (by omega) hd

/-- Every native canonical-reference admission satisfies the maximum
return rule, including the earlier first-ancestor coset branch. All
reference, rank, index and trace premises are local traversal invariants. -/
theorem Frame.Valid.canonical {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry) (hs : Scope G tcLevel f bs f.entry parents)
    (hg : Guides G.graph tcLevel f.entry parents) (hcoset : Cosets f.entry parents)
    (hrank : ∀ t p, parents t = some p → p.Ranked G.graph tcLevel)
    (hframes : ∀ t p, parents t = some p → p.first = true → TraceFrame G p.node.level p.state f.entry)
    (ho : OrbitTrace G f.entry)
    (hcounter : 0 < f.entry.gcaFirst ∧ f.entry.gcaFirst ≤ f.entry.gcaCanon ∧ f.entry.gcaCanon < f.level)
    (ha : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .autoCanon) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hclass : c.1 = .autoCanon := ha
  have hx := canon_exit f.level c.2
  rw [← hclass] at hx
  have hf : c.2.gcaFirst = f.entry.gcaFirst :=
    (leafExit_gca c.1 f.level c.2).symm.trans (f.emit_first G.graph tcLevel)
  have hh : (leafExit c.1 f.level c.2).2.gcaCanon = c.2.gcaCanon := by
    rw [hclass, autoCanon_ancestor]
  have hcanon : c.2.gcaCanon = f.entry.gcaCanon := hh.symm.trans (f.emit_canon ha).2
  change (∃ short, (f.emit G.graph tcLevel).1 = .unwind c.2.gcaCanon short) ∨
    ((f.emit G.graph tcLevel).1 = .unwind c.2.gcaFirst false ∧
      (f.emit G.graph tcLevel).2.orbits[(f.emit G.graph tcLevel).2.cosetindex]! <
        (f.emit G.graph tcLevel).2.cosetindex) at hx
  rw [hf, hcanon] at hx
  rcases hx with ⟨short, he⟩ | ⟨he, hsmall⟩
  · exact h.auto_canon hi hc hs hg (by omega) hcounter.2.2 ha he
  · exact h.coset_return hi hc hs hcoset hrank hframes ho hcounter.1 (by omega) ha he hsmall

end Hex.GraphIso.Nauty.Sparse.Max
