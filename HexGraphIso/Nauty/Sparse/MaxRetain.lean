/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxAncestor
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Native refinement retains every boundary already closed on entry. -/
theorem Frame.Valid.visit_closed {G : GraphIso.Sparse.Colored n k} {f : Frame n}
    (h : f.Valid G) {q : Nat} (hq : f.entry.ptn[q]! ≤ f.level) :
    (visit (.ofGraph G.graph) f.level f.numcells f.entry).2.2.ptn[q]! = f.entry.ptn[q]! := by
  have hend : f.entry.ptn[n - 1]! ≤ f.level := by
    simpa only [h.node.spec.node.ptnSize] using h.node.spec.node.ptnEnd
  have hr := refineWith_state G.graph f.level f.entry.lab f.entry.ptn f.entry.active f.numcells
    f.entry.canong.scratch h.node.spec.label h.node.spec.node.ptnSize hend h.node.spec.node.starts h.node.scratch
  exact hr.2.2.1.closed q hq

/-- Native preparation and all completed sibling reorderings retain the
incoming node's closed partition values literally. -/
theorem Parent.Valid.prepare_closed {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) {q : Nat} (hq : p.node.entry.ptn[q]! ≤ p.node.level) :
    p.state.ptn[q]! = p.node.entry.ptn[q]! := by
  have hv := h.node.visit_closed hq
  exact (h.effect.effect.low q (Or.inl (by
    change (visit (.ofGraph G.graph) p.node.level p.node.numcells p.node.entry).2.2.ptn[q]! ≤ p.node.level
    rw [hv]
    exact hq))).trans hv

/-- Individualization writes inside the selected nonsingleton cell and
therefore leaves every already closed boundary unchanged. -/
theorem Parent.Valid.child_closed {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) {q : Nat} (hq : p.state.ptn[q]! ≤ p.node.level) :
    (p.child G.graph tcLevel).entry.ptn[q]! = p.state.ptn[q]! := by
  obtain ⟨len, ht, _⟩ := h.target
  obtain ⟨hc, hlen, _⟩ := ht (mem_ne_empty h.chosen)
  have hopen : p.node.level < p.state.ptn[p.tc]! := hc.2.2.1 p.tc (Nat.le_refl _) (by omega)
  have he : q ≠ p.tc := by intro he; rw [he] at hq; omega
  dsimp only [Parent.child]
  cases p.first <;> exact Array.getElem!_set!_ne _ _ _ _ he.symm

/-- The actual ancestor chain retains every closed value from a suspended
node's entry through the current entry, including new child singletons. -/
theorem Scope.closed {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) {t : Nat} {p : Parent n}
    (hp : parents t = some p) {q : Nat} (hq : p.node.entry.ptn[q]! ≤ p.node.level) :
    f.entry.ptn[q]! = p.node.entry.ptn[q]! := by
  have retained : ∀ (d t : Nat) (p : Parent n), f.level - t = d → parents t = some p →
      ∀ q : Nat, p.node.entry.ptn[q]! ≤ p.node.level → f.entry.ptn[q]! = p.node.entry.ptn[q]! := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t p hd hp q hq
      obtain ⟨ht1, htl, hpl, hpv⟩ := h.valid t p hp
      have hprepare := hpv.prepare_closed hq
      have hchild := hpv.child_closed (by rw [hprepare]; exact hq)
      have he : (p.child G.graph tcLevel).entry.ptn[q]! = p.node.entry.ptn[q]! := hchild.trans hprepare
      by_cases hlast : t = f.level - 1
      · obtain ⟨last, hl, hc⟩ := h.parent (by omega)
        have heq : p = last := Option.some.inj (hp.symm.trans (hlast ▸ hl))
        rw [← heq] at hc
        rwa [hc] at he
      · obtain ⟨next, hnext⟩ := h.complete (t + 1) (by omega) (by omega)
        obtain ⟨prev, hv, hnextChild⟩ := h.chain (t + 1) next hnext (by omega)
        simp only [Nat.add_sub_cancel] at hv
        have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
        rw [hprev] at hnextChild
        have hsmall : next.node.entry.ptn[q]! ≤ next.node.level := by
          rw [← hnextChild, he]
          change p.node.entry.ptn[q]! ≤ p.node.level + 1
          omega
        have hout := ih (f.level - (t + 1)) (by omega) (t + 1) next rfl hnext q hsmall
        rw [← hnextChild] at hout
        exact hout.trans he
  exact retained (f.level - t) t p rfl hp q hq

/-- The individualized child boundaries remain closed at every later
entry, even when the selected child has since prepared and reordered siblings. -/
theorem Scope.child_closed {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Scope G tcLevel f bs st parents) {t : Nat} {p : Parent n}
    (hp : parents t = some p) {q : Nat}
    (hq : (p.child G.graph tcLevel).entry.ptn[q]! ≤ p.node.level + 1) :
    f.entry.ptn[q]! = (p.child G.graph tcLevel).entry.ptn[q]! := by
  obtain ⟨ht1, htl, hpl, hpv⟩ := h.valid t p hp
  by_cases hlast : t = f.level - 1
  · obtain ⟨last, hl, hc⟩ := h.parent (by omega)
    have heq : p = last := Option.some.inj (hp.symm.trans (hlast ▸ hl))
    rw [← heq] at hc
    rw [hc]
  · obtain ⟨next, hnext⟩ := h.complete (t + 1) (by omega) (by omega)
    obtain ⟨prev, hv, hchild⟩ := h.chain (t + 1) next hnext (by omega)
    simp only [Nat.add_sub_cancel] at hv
    have hprev : prev = p := Option.some.inj (hv.symm.trans hp)
    rw [hprev] at hchild
    have he := h.closed hnext (q := q) (by rw [← hchild]; exact hq)
    rwa [← hchild] at he

end Hex.GraphIso.Nauty.Sparse.Max
