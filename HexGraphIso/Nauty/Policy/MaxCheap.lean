/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxChoice
public import HexGraphIso.Nauty.Policy.MaxLeaf
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.Boundary
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- The actual off-path leaf action after refinement and classification. -/
def Frame.emit (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) : Exit × Search n :=
  let p := prepareOther ctx tcLevel f.level f.numcells f.entry
  let c := classify ctx f.level p.1 p.2.2.2.2.2
  leafExit c.1 f.level c.2

/-- The emitting action retains the node entry's noncheap boundary. -/
theorem Frame.emit_noncheap (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) :
    (f.emit ctx tcLevel).2.noncheaplevel = f.entry.noncheaplevel := by
  unfold Frame.emit
  rw [leafExit_noncheap, classify_noncheap]
  dsimp only [prepareOther]
  rw [target_noncheap, compare_noncheap]
  rfl

/-- At any depth below a cheap boundary, coverage of the emitting node
extends through the saved parents to the entire interrupted ancestor. -/
theorem NodeInput.cheap_witness {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    {target : Nat} {best : Option (Key n)}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (hbelow : target < f.level - 1) (hcheap : f.entry.noncheaplevel ≤ target + 1)
    (hcover : Generic.Covers (f.key ctx tcLevel) best)
    (hgrows : Generic.Grows (f.entry.key ctx bs) best)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Witness ctx tcLevel (parents.frames ctx tcLevel) target best := by
  have covered : ∀ d t p, f.level - t = d → parents t = some p →
      f.entry.noncheaplevel ≤ t → Generic.Covers (p.loop.node.key ctx tcLevel) best := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t p hd hp ht
      obtain ⟨ht1, htl, hpl, hpv⟩ := h.scope.valid t p hp
      have hb := h.scope.boundary t p hp
      have hpc : p.state.noncheaplevel ≤ p.loop.node.level := by omega
      rcases p.collapse hpv hpc hgsz hsymm hloop with hdom | heq
      · exact hdom.grow ((h.scope.grows t p hp).trans hgrows)
      · rw [heq]
        by_cases hlast : t = f.level - 1
        · obtain ⟨last, hl, hc⟩ := h.parent (by omega)
          have hpLast : p = last := Option.some.inj (hp.symm.trans (hlast ▸ hl))
          rw [hpLast, hc]
          exact hcover
        · obtain ⟨q, hq⟩ := h.scope.complete (t + 1) (by omega) (by omega)
          obtain ⟨prev, hv, hchild⟩ := h.scope.chain (t + 1) q hq (by omega)
          simp only [Nat.add_sub_cancel] at hv
          have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
          rw [hprev] at hchild
          rw [hchild]
          exact ih (f.level - (t + 1)) (by omega) (t + 1) q rfl hq (by omega)
  obtain ⟨p, hp⟩ := h.scope.complete (target + 1) (by omega) (by omega)
  have hc := covered (f.level - (target + 1)) (target + 1) p rfl hp hcheap
  have hv := (h.scope.valid (target + 1) p hp).2.2.2
  refine ⟨p.loop.node, ?_, hv.node.depth, Or.inl hc⟩
  by_cases ht0 : target = 0
  · subst target
    simp only [Parents.frames, ↓reduceIte, Nat.zero_add] at hp ⊢
    rw [hp]
    rfl
  · obtain ⟨prev, hprev, hchild⟩ := h.scope.chain (target + 1) p hp (by omega)
    simp only [Nat.add_sub_cancel] at hprev
    simp only [Parents.frames, ht0, ↓reduceIte, hprev, Option.map_some, hchild]

/-- An actual discrete emission returning to its cheap boundary satisfies
the maximum contract at arbitrary depth, for either short-prune flag. -/
theorem NodeInput.cheap_leaf {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {target : Nat} {short : Bool}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hd : (prepareOther ctx tcLevel f.level f.numcells f.entry).1 = n)
    (hexit : (f.emit ctx tcLevel).1 = .unwind target short)
    (hcheap : target = (f.emit ctx tcLevel).2.noncheaplevel - 1)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.Result (f.key ctx tcLevel) (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)
      (f.level - 1) (Witness ctx tcLevel (parents.frames ctx tcLevel)) (f.emit ctx tcLevel).1 := by
  have hb := h.leaf_best hd hgsz hsymm hloop
  change (f.emit ctx tcLevel).2.best ctx = some (incMax (f.entry.key ctx bs) (f.key ctx tcLevel)) at hb
  have hin : Engine.NodePre G ctx tcLevel f.level f.numcells f.entry := h.entry.1
  have ht := hin.leaf_bound hexit
  have hc : Generic.Covers (f.key ctx tcLevel) ((f.emit ctx tcLevel).2.best ctx) := by
    rw [hb]
    exact Generic.Covers.incMax _ _
  have hg : Generic.Grows (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx) := by
    rw [hb]
    exact Generic.Grows.incMax _ _
  refine ⟨Generic.Bounded.of_eq hb, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hc
  · have hn := f.emit_noncheap ctx tcLevel
    apply h.cheap_witness (by omega) (by omega) hc hg hgsz hsymm hloop

end Hex.GraphIso.Nauty.Engine.Max
