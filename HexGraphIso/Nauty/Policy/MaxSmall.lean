/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.FirstCheap
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.CheapShape
import all HexGraphIso.Nauty.Policy.EquitableState
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.CanonRef
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Internal preparation preserves both saved ancestor counters. -/
theorem Loop.ancestors (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) :
    (l.prepare ctx tcLevel).2.2.2.2.gcaFirst = l.node.entry.gcaFirst ∧
      (l.prepare ctx tcLevel).2.2.2.2.gcaCanon = l.node.entry.gcaCanon := by
  unfold Loop.prepare
  dsimp only
  constructor
  · have hcheap : ∀ first level (st : Search n),
        (cheapCheck first level st).gcaFirst = st.gcaFirst := (gcaPolicy ctx 0 tcLevel).cheap
    rw [hcheap]
    cases hf : l.first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [chooseTarget_fields]
      exact (gcaPolicy ctx 0 tcLevel).compare _ _ _
    · simp only [↓reduceIte]
      rw [chooseFirst_fields]
      rfl
  · rw [cheap_canon, target_canon]
    cases hf : l.first
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact compare_canon _ _ _
    · simp only [↓reduceIte]
      rfl

/-- At sweep initialization both reference-coverage conditions are
vacuous; the entry bounds hold at the actual root and are preserved at
every first-child descent. -/
theorem NodeInput.references {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) :
    let l : Loop n := ⟨f, first⟩
    let p := l.prepare ctx tcLevel
    p.2.2.2.2.gcaFirst < f.level ∧
      CanonGuide f.level p.2.1.toNat p.2.2.2.2 (l.key ctx tcLevel)
        (p.2.2.2.2.key ctx bs) p.2.2.2.2 := by
  intro l p
  have hb : f.entry.gcaFirst < f.level ∧ f.entry.gcaCanon < f.level := by
    cases first with
    | false => exact ⟨h.entry.1.ancestor, h.entry.1.canonAncestor⟩
    | true => exact h.entry.2.2.2.2.2.2.2.2
  have he := l.ancestors ctx tcLevel
  refine ⟨he.1 ▸ hb.1, CanonGuide.vacuous ?_⟩
  rw [he.2]
  exact hb.2

/-- The actual internal preparation initializes the sweep's small-cell
premise on both first-path and off-path entries. -/
theorem NodeInput.small {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hinternal : first = false →
      let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .internal) :
    let l : Loop n := ⟨f, first⟩
    let p := l.prepare ctx tcLevel
    p.2.2.2.2.noncheaplevel ≤ f.level →
      SubtreeOk ctx f.level ⟨p.2.2.2.2.lab, p.2.2.2.2.ptn, p.2.2.2.2.active, p.1, 0, 0, 0⟩ := by
  intro l p hc
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  cases first with
  | false =>
    have hs := (h.entry.1.prepare hn0 hgsz hsymm hloop).2.2.2.2 (hinternal rfl)
    exact hs.subtree hn0 hc
  | true =>
    obtain ⟨hp, _⟩ := h.entry
    have hr := l.first_prepare (ctx := ctx) (tcLevel := tcLevel) rfl
    have hcheap := hc
    change (l.prepare ctx tcLevel).2.2.2.2.noncheaplevel ≤ f.level at hcheap
    rw [hr] at hcheap
    have hs := firstCheap_small hn0 h.frame.positive h.frame.partition hp.equitable hp.small hcheap
    have heq := hp.equitable
    have hshape := hs.shape
    obtain ⟨_, hl, ht⟩ := l.prepare_frame ctx tcLevel
    change p.2.2.2.2.lab = (f.entry.refined ctx f.level f.numcells).lab at hl
    change p.2.2.2.2.ptn = (f.entry.refined ctx f.level f.numcells).ptn at ht
    rw [← hl, ← ht] at heq
    rw [← ht] at hshape
    exact (l.prepare_ok h.frame).subtree hn0 h.frame.positive rfl rfl rfl heq hshape

/-- An actual child return preserves the receiving sweep's small-cell
premise through first-child cleanup and partition recovery. -/
theorem SweepInput.recovered_small {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let raw := (Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Engine.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := recoverLevels level (recoverPtn (n + 2) level left)
    ready.noncheaplevel ≤ level →
      SubtreeOk ctx level ⟨ready.lab, ready.ptn, ready.active, numcells, 0, 0, 0⟩ := by
  intro raw middle left ready hc
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hf := child_frame (first := first) h.partition hn0 hl h.path.fixed h.target
    (h.cursor_mem tv rfl) (first && tv == tv1) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  have hout : SearchOut G level level st.view left.view := by
    dsimp only [left, middle]
    split <;> exact hf.1.congr rfl rfl rfl rfl
  have hb := (h.push hgsz hsymm hloop).boundary
  dsimp only [Parent.child] at hb
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hb
  have hboundary : left.noncheaplevel = st.noncheaplevel ∨ level + 1 ≤ left.noncheaplevel := by
    have hn : left.noncheaplevel = raw.noncheaplevel := by dsimp only [left, middle]; split <;> rfl
    rw [hn]
    cases first <;> exact hb
  have hshape := recover_shape h.partition hout (fun hc => (h.small hc).shape) hboundary hc
  have heq := recover_equitable hn0 hl h.partition h.equitable hout
  have hok := (reachPolicy G ctx tcLevel hn0).recover level numcells st left hl h.partition hout
  exact hok.ok.subtree hn0 hl rfl rfl rfl heq hshape

end Hex.GraphIso.Nauty.Engine.Max
