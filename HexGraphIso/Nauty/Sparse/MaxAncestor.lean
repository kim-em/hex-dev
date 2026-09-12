/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxScope
public import HexGraphIso.Nauty.Sparse.MaxEmit
public import HexGraphIso.Nauty.Sparse.CanonSource
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A returned effect inside the actual selected child composes with its
native individualization to retain the suspended parent. -/
theorem Parent.Valid.return_frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {out : State n} (h : p.Valid G tcLevel)
    (hx : FrameOut G (p.node.level) (p.node.level + 1) (p.child G.graph tcLevel).entry out) :
    FrameOut G p.node.level p.node.level p.state out := by
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  exact h.ready.child_frame hn h.node.positive p.first h.target h.chosen hx

/-- The established ancestor chain determines the current entry's effect
inside every suspended selected child. No separate ancestor-frame premise
is needed in the maximum-coverage recursion. -/
theorem Scope.child_frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) (hf : f.Valid G) {t : Nat} {p : Parent n}
    (hp : parents t = some p) :
    FrameOut G p.node.level (p.node.level + 1) (p.child G.graph tcLevel).entry f.entry := by
  have frames : ∀ d t p, f.level - t = d → parents t = some p →
      FrameOut G p.node.level (p.node.level + 1) (p.child G.graph tcLevel).entry f.entry := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t p hd hp
      obtain ⟨ht1, htl, hpl, hpv⟩ := h.valid t p hp
      by_cases hlast : t = f.level - 1
      · obtain ⟨last, hl, hc⟩ := h.parent (by omega)
        have he : p = last := Option.some.inj (hp.symm.trans (hlast ▸ hl))
        rw [← he] at hc
        have hlevel : p.node.level + 1 = f.level := by have := hf.positive; omega
        rw [hc, hlevel]
        exact FrameOut.refl hf.node
      · obtain ⟨q, hq⟩ := h.complete (t + 1) (by omega) (by omega)
        obtain ⟨prev, hv, hchild⟩ := h.chain (t + 1) q hq (by omega)
        simp only [Nat.add_sub_cancel] at hv
        have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
        rw [hprev] at hchild
        have hqv := (h.valid (t + 1) q hq).2.2.2
        have hx := ih (f.level - (t + 1)) (by omega) (t + 1) q rfl hq
        have hout := hqv.return_frame hx
        have hvisit := hqv.node.node.visit_frame hqv.node.positive (hqv.effect.trans hout)
        rw [← hchild] at hvisit
        simpa only [Parent.child, Nat.add_sub_cancel] using hvisit
  exact frames (f.level - t) t p rfl hp

/-- Every suspended parent's cells contain the current entry, as a
consequence of its actual child chain and native frame effects. -/
theorem Scope.frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) (hf : f.Valid G) {t : Nat} {p : Parent n}
    (hp : parents t = some p) : FrameOut G p.node.level p.node.level p.state f.entry :=
  ((h.valid t p hp).2.2.2).return_frame (h.child_frame hf hp)

/-- The native leaf dispatcher preserves the current node's complete
entry frame, including either reference-store alternative. -/
theorem Frame.Valid.emit_frame {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} (h : f.Valid G) :
    FrameOut G (f.level - 1) f.level f.entry (f.emit G.graph tcLevel).2 := by
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  have hc := (h.node.visit_ready hn h.positive).compare v.2.1
  have ht := hc.ready.target_frame false tcLevel
  have ha := ht.ready.classify
  have hl := ha.ready.leaf (classify (.ofGraph G.graph) f.level v.1
    (chooseTarget false (.ofGraph G.graph) tcLevel f.level v.1
      (compareCodes f.level v.2.1 v.2.2)).2.2.2).1
  exact h.node.visit_frame h.positive (((hc.trans ht).trans ha).trans hl).frame

end Hex.GraphIso.Nauty.Sparse.Max
