/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Policy.Target
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A frozen target justification survives incumbent growth. -/
theorem Loop.Choice.grow {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    {before after : Option (Key n)} (h : l.Choice ctx tcLevel before)
    (hg : Generic.Grows before after) : l.Choice ctx tcLevel after := by
  rcases h with hs | hd
  · exact Or.inl hs
  · exact Or.inr (hd.grow hg)

/-- Sweep preparation retains the semantic incumbent, including when its
code array is being overwritten by a better path. -/
theorem Loop.prepare_key (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) (bs : List Nat) :
    (l.prepare ctx tcLevel).2.2.2.2.key ctx bs = l.node.entry.key ctx bs := by
  have hc : (l.prepare ctx tcLevel).2.2.2.2.canonlab = l.node.entry.canonlab := by
    dsimp only [Loop.prepare]
    simp only [cheapCheck, apply_ite Search.canonlab, ite_self]
    rw [(chooseTarget_frame ..).2.2.2]
    split
    · rfl
    · exact (compareCodes_frame ..).2.2.2
  simp only [Search.key, hc]

/-- Actual node preparation chooses the specification target or has
already proved the whole node dominated by its incoming incumbent. -/
theorem Loop.choice {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {l : Loop n} {bs fs : List Nat} (hf : l.node.Valid G)
    (h : Entry G ctx tcLevel l.first l.node bs fs)
    (hnc : (l.prepare ctx tcLevel).1 < n) :
    l.Choice ctx tcLevel (l.node.entry.key ctx bs) := by
  let v := visit ctx l.node.level l.node.numcells l.node.entry
  let r := l.node.entry.refined ctx l.node.level l.node.numcells
  have hn0 : 0 < n := by have := hf.positive; have := hf.depth; omega
  have hv := (reachPolicy G ctx tcLevel hn0).visit _ _ _ hf.positive hf.partition |>.1
  have hit := refined_iter (ctx := ctx) hn0 hf.positive hf.partition
  have hcount : v.1 < n := hnc
  have hlen := hf.length
  have hdepth := hf.depth
  cases he : l.first with
  | true =>
    have hin : FirstPre G ctx l.node.level l.node.numcells l.node.entry := by
      simp only [Entry, he, ↓reduceIte] at h
      exact h.1
    left
    have hm := maketargetcell_eq_spec (tcLevel := tcLevel) hin.equitable
      hit.ok.labOk hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd
    change maketargetcell ctx (visit ctx l.node.level l.node.numcells l.node.entry).2.2.lab
      (visit ctx l.node.level l.node.numcells l.node.entry).2.2.ptn l.node.level tcLevel (-1) = _ at hm
    have hne : (visit ctx l.node.level l.node.numcells l.node.entry).1 ≠ n := Nat.ne_of_lt hcount
    dsimp only [Loop.prepare]
    simp only [he, ↓reduceIte, chooseTarget, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, bne_iff_ne.mpr hne,
      Id.run_pure, recordFirst]
    rw [hm]
    rfl
  | false =>
    have hin : Nauty.NodePre G ctx tcLevel l.node.level l.node.numcells l.node.entry ∧
        Comparison ctx l.node.codes bs fs l.node.entry := by
      simpa only [Entry, he, Bool.false_eq_true, ↓reduceIte] using h
    let c := compareCodes l.node.level v.2.1 v.2.2
    have hm := (hin.2.visit l.node.level l.node.numcells).compare
      (refine_longcode_lt ctx l.node.level l.node.entry.lab l.node.entry.ptn
        l.node.entry.active l.node.numcells) (by omega)
    rw [hlen] at hm
    have hc : Comparison ctx (l.node.codes ++ [v.2.1]) bs fs c := hm
    have hl : c.lab = r.lab := (compareCodes_frame _ _ _).1
    have hp : c.ptn = r.ptn := (compareCodes_frame _ _ _).2.1
    have hcan : c.canonlab = l.node.entry.canonlab := (compareCodes_frame _ _ _).2.2.2
    by_cases hneg : c.compCanon < 0
    · right
      have hk := hc.canonical.subtree_le (ctx := ctx) hneg tcLevel (n - l.node.level)
      refine ⟨incKey ctx bs c.canonlab, ?_, ?_⟩
      · simp only [Search.key, hin.2.nonempty, ↓reduceIte, hcan]
      · rw [Frame.key, show n + 1 - l.node.level = n - l.node.level + 1 by omega]
        exact hk
    · left
      have hs := chooseTarget_unhinted (ctx := ctx) (tcLevel := tcLevel)
        (st := c) hcount (by omega) (by rw [hl, hp]; exact hin.1.equitable)
        (by rw [hl]; exact hit.ok.labOk) (by rw [hl]; exact hit.ok.labSize)
        (by rw [hp]; exact hit.ok.ptnSize) (by rw [hp]; exact hit.ok.ptnEnd)
      dsimp only [Loop.prepare]
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      change specTargetcell ctx r.lab r.ptn l.node.level tcLevel =
        (chooseTarget false ctx tcLevel l.node.level v.1 c).1.toNat
      rw [hs, hl, hp]
      rfl

/-- The target justification is initialized at the actual prepared sweep,
with its current semantic incumbent rather than an assumed parent bound. -/
theorem Loop.choice_prepared {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {l : Loop n} {bs fs : List Nat} (hf : l.node.Valid G)
    (h : Entry G ctx tcLevel l.first l.node bs fs)
    (hnc : (l.prepare ctx tcLevel).1 < n) :
    l.Choice ctx tcLevel ((l.prepare ctx tcLevel).2.2.2.2.key ctx bs) := by
  rw [l.prepare_key]
  exact l.choice hf h hnc

/-- A cheap parent's entire specification is already covered or is exactly
the subtree of its actual chosen child. -/
theorem Parent.collapse {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel)
    (hcheap : p.state.noncheaplevel ≤ p.loop.node.level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.Covers (p.loop.node.key ctx tcLevel) (p.state.key ctx p.bs) ∨
      p.loop.node.key ctx tcLevel = (p.child ctx tcLevel).key ctx tcLevel := by
  rcases h.choice with hs | hd
  · right
    have hb := p.loop.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.node
    exact p.cheap_key h hb (p.small h hb hcheap) hs hgsz hsymm hloop
  · exact Or.inl hd

end Hex.GraphIso.Nauty.Max
