/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Codes
import all HexGraphIso.Nauty.Policy.Max.Codes
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Boundary
import all HexGraphIso.Nauty.Policy.First.Path
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.First.Return
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Returning from either sweep phase establishes the common off-path
state used by all remaining siblings. -/
theorem SweepInput.restore {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hvisit : (!first || st.orbits[tv]! == tv) = true) :
    let raw := (Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    Nauty.SweepPre G ctx tcLevel first level numcells tc tv1 none cell
      (Nauty.recover (n + 2) level left) := by
  intro raw middle left
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hi := (h.push hgsz hsymm hloop).stored hgsz hsymm hloop
  dsimp only [Parent.child] at hi
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hi
  rcases h.phase with ⟨hf, _, _, hst, hcell, hcursor, _⟩ | ⟨hp, _, _⟩
  · subst first
    have hlf : l.first = true := h.first_eq.symm
    let r := Generic.prepareFirst ctx tcLevel l.node.level l.node.numcells l.node.entry
    have hr := l.first_prepare (ctx := ctx) (tcLevel := tcLevel) hlf
    have htv : r.2.2.1.nextElem none = some tv := by
      rw [hcell, hr] at hcursor
      exact hcursor.symm
    have htv1 : tv1 = tv := by rw [h.tv1_eq, hr, htv]; rfl
    have hst' : st = cheapCheck true l.node.level r.2.2.2.2 := by rw [hst, hr]
    have hnc : numcells = r.1 := by rw [h.numcells_eq, hr]
    have htc : tc = r.2.1.toNat := by rw [h.tc_eq, hr]
    have hcell' : cell = r.2.2.1 := by rw [hcell, hr]
    have horbit : (cheapCheck true l.node.level r.2.2.2.2).orbits[tv]! = tv := by
      simpa only [hst', Bool.not_true, Bool.false_or, beq_iff_eq] using hvisit
    obtain ⟨bs₀, fs₀, hentry⟩ := h.origin
    obtain ⟨hpre, _, _, _, ht, _⟩ := hentry
    have hentryChild := hpre.child hn0 hsymm htv hgsz hloop
    have htrace : (Nauty.child true l.node.level r.2.1.toNat tv
        (cheapCheck true l.node.level r.2.2.2.2)).genTrace = #[] := by
      change (cheapCheck true l.node.level r.2.2.2.2).genTrace = #[]
      unfold cheapCheck
      split <;> exact (prepareFirst_stores ctx tcLevel _ _ _).2.2.2.2.trans ht
    have hlength : n + 1 ≤ l.node.level + 1 + fuel := by
      have hh := h.fuel
      rw [h.level_eq] at hh
      omega
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 hentryChild.positive hentryChild.partition (empty_orbits hentryChild.orbits htrace) hlength
    have hopen : r.1 ≠ n := by
      have hh : r.1 + 1 ≤ n :=
        Nat.le_trans (Nat.le_of_eq hentryChild.partition.count) (bcount_le _ _ _)
      omega
    rw [htv1, Bool.true_and, beq_self_eq_true] at hi
    rw [h.level_eq, hnc, htc, hst'] at hi
    have hready := firstChild_ready hpre hn0 hsymm hopen htv horbit path hi hgsz hloop
    dsimp only [left, middle, raw]
    rw [htv1, Bool.true_and, beq_self_eq_true, ite_eq_left rfl, h.level_eq, hnc, htc, hst', hcell']
    exact hready
  · have hfalse : (first && tv == tv1) = false := by
      cases hf : first with
      | false => rfl
      | true =>
        have ht := hp.past hf tv rfl
        simp only [Bool.true_and, beq_eq_false_iff_ne]
        omega
    rw [hfalse] at hi
    have hr := hp.restore hn0 hgsz hsymm hi
    dsimp only [left, middle, raw]
    rw [hfalse, ite_eq_right Bool.false_ne_true]
    exact ⟨(by intro _ v hv; cases hv), hr.positive, hr.partition, hr.target,
      (by intro v hv; cases hv), hr.stored, hr.ancestor, hr.canonAncestor,
      hr.history, hr.recorded, hr.equitable, hr.boundary, hr.cheapBound, hr.path, hr.small⟩

end Hex.GraphIso.Nauty.Max
