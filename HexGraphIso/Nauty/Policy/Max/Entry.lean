/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Push
import all HexGraphIso.Nauty.Policy.Max.Push
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Suspend
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.First.Compare
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.First.Run
import all HexGraphIso.Nauty.Policy.First.Path
import all HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The frozen first sweep uses exactly the first-path preparation. -/
theorem Loop.first_prepare {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    (hf : l.first = true) :
    l.prepare ctx tcLevel =
      let r := Generic.prepareFirst ctx tcLevel l.node.level l.node.numcells l.node.entry
      (r.1, r.2.1, r.2.2.1, r.2.2.2.1, cheapCheck true l.node.level r.2.2.2.2) := by
  simp only [Loop.prepare, hf, ↓reduceIte]
  rfl

/-- Both sweep phases establish the actual child's first-path or
off-path entry conditions, including its full stored code prefix. -/
theorem SweepInput.child_entry {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Entry G ctx tcLevel (first && tv == tv1)
      ⟨level + 1, numcells + 1, l.codes ctx, Nauty.child first level tc tv st⟩ bs fs := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  rcases h.phase with hphase | ⟨hp, hcmp, _⟩
  · obtain ⟨hf, hbs, hfs, hst, hcell, hcursor, _⟩ := hphase
    subst first
    have hlf : l.first = true := h.first_eq.symm
    let r := Generic.prepareFirst ctx tcLevel l.node.level l.node.numcells l.node.entry
    have hr := l.first_prepare (ctx := ctx) (tcLevel := tcLevel) hlf
    have htv : r.2.2.1.nextElem none = some tv := by
      rw [hcell, hr] at hcursor
      exact hcursor.symm
    have htv1 : tv1 = tv := by
      rw [h.tv1_eq, hr, htv]
      rfl
    rw [htv1, beq_self_eq_true, Bool.and_self]
    obtain ⟨bs₀, fs₀, hentry⟩ := h.origin
    obtain ⟨hpre, _, _, hcanon, htrace, hsize, hcodes, hlt, hgf, hgc⟩ := hentry
    have hnext := hpre.child (tcLevel := tcLevel) hn0 hsymm htv hgsz hloop
    have hst' : st = cheapCheck true l.node.level r.2.2.2.2 := by
      rw [hst, hr]
    have hnc : numcells = r.1 := by rw [h.numcells_eq, hr]
    have htc : tc = r.2.1.toNat := by rw [h.tc_eq, hr]
    rw [h.level_eq, hnc, htc, hst']
    change FirstPre G ctx _ _ _ ∧ _
    refine ⟨hnext, hbs, hfs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (cheapCheck true l.node.level r.2.2.2.2).canonlevel = 0
      unfold cheapCheck
      split <;> change r.2.2.2.2.canonlevel = 0
      all_goals
        dsimp only [r, Generic.prepareFirst]
        change (chooseTarget true ctx tcLevel l.node.level _ _).2.2.2.canonlevel = 0
        rw [chooseFirst_fields]
        exact hcanon
    · change (cheapCheck true l.node.level r.2.2.2.2).genTrace = #[]
      unfold cheapCheck
      split <;> change r.2.2.2.2.genTrace = #[]
      all_goals exact (prepareFirst_stores ctx tcLevel _ _ _).2.2.2.2.trans htrace
    · change (cheapCheck true l.node.level r.2.2.2.2).canoncode.size = n + 2
      unfold cheapCheck
      split <;> change r.2.2.2.2.canoncode.size = n + 2
      all_goals rw [prepareFirst_canoncode, hsize]
    · change StoredCodes (cheapCheck true l.node.level r.2.2.2.2).firstcode 1 (l.codes ctx)
      unfold cheapCheck
      split <;> exact hpre.code_prefix h.node.length hcodes
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hlt c hc
      · have he := List.mem_singleton.mp hc
        subst c
        exact refine_longcode_lt ctx _ _ _ _ _
    · change (cheapCheck true l.node.level r.2.2.2.2).gcaFirst < l.node.level + 1
      unfold cheapCheck
      split <;> change r.2.2.2.2.gcaFirst < l.node.level + 1
      all_goals
        dsimp only [r, Generic.prepareFirst]
        change (chooseTarget true ctx tcLevel l.node.level _ _).2.2.2.gcaFirst < l.node.level + 1
        rw [chooseFirst_fields]
        exact Nat.lt_succ_of_lt hgf
    · change (cheapCheck true l.node.level r.2.2.2.2).gcaCanon < l.node.level + 1
      unfold cheapCheck
      split <;> change r.2.2.2.2.gcaCanon < l.node.level + 1
      all_goals
        dsimp only [r, Generic.prepareFirst]
        change (chooseTarget true ctx tcLevel l.node.level _ _).2.2.2.gcaCanon < l.node.level + 1
        rw [chooseFirst_fields]
        exact Nat.lt_succ_of_lt hgc
  · have hfalse : (first && tv == tv1) = false := by
      cases hf : first with
      | false => rfl
      | true =>
        have ht := hp.past hf tv rfl
        simp only [Bool.true_and, beq_eq_false_iff_ne]
        omega
    rw [hfalse]
    exact ⟨hp.child hn0 hgsz hsymm, hcmp.child first level tc tv⟩

/-- Every actual visited child satisfies the complete maximum input.
All ancestor facts are constructed from the suspended sweep. -/
theorem SweepInput.push {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    NodeInput G ctx tcLevel fuel (first && tv == tv1)
      (p.child ctx tcLevel) bs fs (parents.push p) := by
  intro p
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hl h.partition h.target (h.cursor_mem tv rfl)
  dsimp only [policy, Generic.Policy.child] at hch
  have hchild : p.child ctx tcLevel =
      ⟨level + 1, numcells + 1, l.codes ctx, Nauty.child first level tc tv st⟩ := by
    simp only [p, Parent.child, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq]
  rw [hchild]
  refine ⟨⟨by dsimp; omega, ?_, ?_, hch.1⟩, ?_,
    h.child_entry hgsz hsymm hloop, h.child_scope, ?_, ?_⟩
  · have hb := hch.1.bc
    have hh := bcount_le (Nauty.child first level tc tv st).ptn (level + 1) n
    dsimp
    omega
  · dsimp only [Loop.codes]
    simp only [List.length_append, List.length_singleton]
    rw [h.node.length, ← h.level_eq]
  · dsimp
    have := h.fuel
    omega
  · intro _
    refine ⟨p, ?_, hchild⟩
    simp only [Nat.add_sub_cancel, Parents.push, p, ← h.level_eq, ↓reduceIte]
  · intro hc
    cases first <;> exact h.counters hc

/-- Actual node calls establish the checked store needed by receiving
filters, on both the first path and later sibling paths. -/
theorem NodeInput.stored {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    RunInv G ctx (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2 := by
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  cases first with
  | false => exact node_safe hn0 hgsz hsymm hloop h.entry.1
  | true =>
    obtain ⟨hp, _, _, _, ht, _⟩ := h.entry
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 h.frame.positive h.frame.partition (empty_orbits hp.orbits ht) h.fuel
    exact firstPath_safe hn0 hgsz hsymm hloop path hp

end Hex.GraphIso.Nauty.Max
