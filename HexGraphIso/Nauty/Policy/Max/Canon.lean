/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Auto
import all HexGraphIso.Nauty.Policy.Max.Auto
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Emit
import all HexGraphIso.Nauty.Policy.Max.Control
import all HexGraphIso.Nauty.Policy.Max.Leaf
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Canon.Scatter
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Code two occurs only after refinement reaches a discrete partition. -/
theorem canon_discrete {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (h : (classify ctx level numcells st).1 = .autoCanon) : numcells = n := by
  by_cases hn : numcells = n
  · exact hn
  rw [classify_eq] at h
  split at h
  · cases h
  · simp only [bne_iff_ne.mpr hn, ite_true] at h
    cases h

/-- A canonical admission retains its reference labelling and ancestor. -/
theorem Frame.emit_canon {ctx : Ctx n} {tcLevel : Nat} {f : Frame n}
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoCanon) :
    (f.emit ctx tcLevel).2.canonlab = f.entry.canonlab ∧
      (f.emit ctx tcLevel).2.gcaCanon = f.entry.gcaCanon := by
  unfold Frame.emit
  dsimp only at hauto ⊢
  rw [hauto, autoCanon_ref, autoCanon_ancestor, (classify_frame ..).2.2.2, classify_canon]
  dsimp only [prepareOther]
  rw [chooseTarget_fields]
  exact ⟨(compareCodes_frame ..).2.2.2, compare_canon _ _ _⟩

/-- The actual canonical verdict supplies its checked scatter, including
classification after a failed first-reference scan. -/
theorem NodeInput.canon_scatter {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoCanon) :
    let out := (f.emit ctx tcLevel).2
    checkAutom ctx.g out.workperm = true ∧ out.canonlab.size = n ∧
      ∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]! := by
  intro out
  let p := prepareOther ctx tcLevel f.level f.numcells f.entry
  let c := classify ctx f.level p.1 p.2.2.2.2.2
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  obtain ⟨hok, hi, hh, _, _⟩ := h.entry.1.prepare hn0 hgsz hsymm hloop
  have hc : c.1 = .autoCanon := hauto
  have hchecked := hh.checked hi hn0 hok hgsz hsymm hloop (Or.inr hc)
  have hw : out.workperm = c.2.workperm := leafExit_workperm c.1 f.level c.2
  have href : out.canonlab = p.2.2.2.2.2.canonlab := by
    change (leafExit c.1 f.level c.2).2.canonlab = _
    rw [hc, autoCanon_ref]
    exact (classify_frame ctx f.level p.1 _).2.2.2
  have hl : out.lab = p.2.2.2.2.2.lab :=
    (leafExit_frame c.1 f.level c.2).1.trans (classify_frame ctx f.level p.1 _).1
  refine ⟨hw ▸ hchecked, href ▸ hi.canonical.1, ?_⟩
  intro i hiN
  rw [hw, href, hl]
  exact classify_canon_map hc hi.scratch hi.canonical.1
    (isPerm_of_cellsReach hi.canonical.1 hn0 hi.canonical.2) i hiN

/-- A canonical-ancestor return covers the interrupted child using its
already covered reference child and the actual emitting scatter. -/
theorem NodeInput.canon_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoCanon)
    {t : Nat} {p : Parent n} (hp : parents t = some p) (ht : f.entry.gcaCanon = t)
    (hg : Generic.Grows (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)) :
    Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) ((f.emit ctx tcLevel).2.best ctx) := by
  obtain ⟨_, _, he, hv⟩ := h.scope.valid t p hp
  have hf := h.scope.canonical t p hp (by omega)
  have hparent : p.state.gcaCanon = p.loop.node.level := hf.1.symm.trans (ht.trans he.symm)
  obtain ⟨v, hc, hat, hr⟩ := hv.canonical hparent
  have href : (f.emit ctx tcLevel).2.canonlab = p.state.canonlab := (f.emit_canon hauto).1.trans hf.2
  have hsc := h.canon_scatter hgsz hsymm hloop hauto
  apply Parent.scatter_cover hv hgsz hsc.2.1 hsc.1
  · rw [href]; exact hr
  · exact h.emit_parent hp
  · exact hsc.2.2
  · exact h.emit_chosen hp
  · rw [href, hat]
    exact hc.grow ((h.scope.grows t p hp).trans hg)

/-- Both short flags and both orbit-count outcomes are covered when code
two selects the canonical ancestor as its return target. -/
theorem NodeInput.canon_return {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoCanon)
    (he : (f.emit ctx tcLevel).1 = .unwind f.entry.gcaCanon short) :
    Generic.Result (f.key ctx tcLevel) (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)
      (f.level - 1) (Witness ctx tcLevel (parents.frames ctx tcLevel)) (f.emit ctx tcLevel).1 := by
  have hb := h.leaf_best (canon_discrete hauto) hgsz hsymm hloop
  change (f.emit ctx tcLevel).2.best ctx = some (incMax (f.entry.key ctx bs) (f.key ctx tcLevel)) at hb
  have hg : Generic.Grows (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx) := by
    rw [hb]; exact Generic.Grows.incMax _ _
  refine ⟨Generic.Bounded.of_eq hb, ?_⟩
  rw [he]
  have ht := h.entry.1.canonAncestor
  refine ⟨by omega, ?_⟩
  split
  · rw [hb]; exact Generic.Covers.incMax _ _
  · rename_i hne
    have hcounts := h.counters (comparison_positive h.entry.2)
    have hp : 0 < f.entry.gcaCanon := by omega
    obtain ⟨p, hp⟩ := h.scope.complete f.entry.gcaCanon hp ht
    obtain ⟨_, _, hl, hv⟩ := h.scope.valid f.entry.gcaCanon p hp
    have hc := h.canon_cover hgsz hsymm hloop hauto hp rfl hg
    refine ⟨p.child ctx tcLevel, ?_, ?_, Or.inl hc⟩
    · simp only [Parents.frames, show f.entry.gcaCanon ≠ 0 by omega, ↓reduceIte, hp, Option.map_some]
    · change p.loop.node.level + 1 ≤ n
      have := h.frame.depth
      omega

end Hex.GraphIso.Nauty.Max
