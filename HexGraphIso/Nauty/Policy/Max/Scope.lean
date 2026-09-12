/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Restore
import all HexGraphIso.Nauty.Policy.Max.Restore
import all HexGraphIso.Nauty.Policy.Max.Position
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Boundary
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A received child preserves every saved ancestor field except for
the explicit generator-stabilization obligation. Incumbent growth comes
from the child's maximum result and settled-code receipt. -/
theorem SweepInput.restore_scope {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs bs' fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let raw := (Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := Nauty.recover (n + 2) level left
    Generic.Grows (st.key ctx bs) (ready.key ctx bs') →
    (∀ t p, parents t = some p → p.loop.first = true →
      ∀ γ ∈ ready.genTrace, CellStab p.state.ptn t p.state.lab γ) →
    Scope G ctx tcLevel level (l.codes ctx) bs' ready parents := by
  intro raw middle left ready hg hgenerators
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hf := child_frame (first := first) h.partition hn0 hl h.path.fixed h.target
    (h.cursor_mem tv rfl) (first && tv == tv1) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  have hout : SearchOut G level level st left := by
    dsimp only [left, middle]
    split <;> exact hf.1.congr rfl rfl rfl rfl
  have he := (reachPolicy G ctx tcLevel hn0).recover level numcells st left hl h.partition hout
  have hgc : ready.gcaCanon = min level raw.gcaCanon := by
    rw [recover_canon]
    dsimp only [left, middle]
    split <;> rfl
  have hcanon : ready.canonlab = raw.canonlab := by
    dsimp only [ready]
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canonlab, ite_self]
    dsimp only [left, middle]
    split <;> rfl
  have hfirst : ready.firstlab = left.firstlab :=
    congrArg (fun r => r.2.2) ((referencePolicy ctx (n + 2) tcLevel).recover level left)
  have hgf : ready.gcaFirst = left.gcaFirst := (gcaPolicy ctx (n + 2) tcLevel).recover level left
  have hb := (h.push hgsz hsymm hloop).boundary
  dsimp only [Parent.child] at hb
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hb
  have hraw : raw.noncheaplevel = st.noncheaplevel ∨ level + 1 ≤ raw.noncheaplevel := by
    cases first <;> exact hb
  refine ⟨h.scope.complete, h.scope.valid, h.scope.codes, h.scope.code,
    ?_, ?_, ?_, ?_, ?_, ?_, hgenerators, ?_, h.scope.chain⟩
  · intro t p hp
    exact (h.scope.grows t p hp).trans hg
  · intro t p hp
    obtain ⟨ht, htl, hpl, hv⟩ := h.scope.valid t p hp
    have hok := hv.partition
    rw [hpl] at hok
    exact extend_effect ht (Nat.le_of_lt htl) hok h.partition (h.scope.effect t p hp) he.effect
  · intro t p hp
    exact (he.effect.atSingleton (h.singletons hp)).trans (h.scope.chosen t p hp)
  · intro t p hp htarget
    have ht := (h.scope.valid t p hp).2.1
    have hlo : raw.gcaCanon ≤ t := by omega
    have hc := child_canon_old (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) (first := first)
      h.partition hn0 hl h.target (h.cursor_mem tv rfl) (first && tv == tv1) (by omega : raw.gcaCanon ≤ level)
    have hrawgc : raw.gcaCanon = st.gcaCanon := hc.1
    have hpast := h.scope.canonical t p hp (by omega : st.gcaCanon ≤ t)
    refine ⟨?_, ?_⟩
    · rw [hgc, Nat.min_eq_right (by omega), hrawgc, hpast.1]
    · exact hcanon.trans (hc.2.trans hpast.2)
  · intro t p hp htarget
    have ht := (h.scope.valid t p hp).2.1
    rw [hgf] at htarget ⊢
    rw [hfirst]
    by_cases hleft : (first && tv == tv1) = true
    · have hh : left.gcaFirst = level := by simp only [left, middle, hleft, ↓reduceIte]; rfl
      omega
    · have hfalse : (first && tv == tv1) = false := Bool.eq_false_iff.mpr hleft
      have hh : raw.firstlab = st.firstlab := by
        dsimp only [raw]
        rw [hfalse]
        have hr := congrArg (fun r => r.2.2)
          (node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (Nauty.child first level tc tv st))
        cases first <;> exact hr
      have hhg : raw.gcaFirst = st.gcaFirst := by
        dsimp only [raw]
        rw [hfalse, node_gca]
        cases first <;> rfl
      have hlg : left.gcaFirst = raw.gcaFirst := by
        dsimp only [left, middle]
        rw [ite_eq_right hleft]
      have hll : left.firstlab = raw.firstlab := by
        dsimp only [left, middle]
        rw [ite_eq_right hleft]
      rw [hlg, hhg] at htarget
      have hs := h.scope.first t p hp htarget
      exact ⟨hlg.trans (hhg.trans hs.1), hll.trans (hh.trans hs.2)⟩
  · intro t p hp
    have ht := (h.scope.valid t p hp).2.1
    have ha := h.scope.boundary t p hp
    have hh : left.noncheaplevel = raw.noncheaplevel := by dsimp only [left, middle]; split <;> rfl
    dsimp only [ready]
    rw [recover_noncheap, hh]
    split <;> omega
  · intro t p hp _ htarget
    have ht := (h.scope.valid t p hp).2.1
    rw [hgf] at htarget
    by_cases hleft : (first && tv == tv1) = true
    · have hh : left.gcaFirst = level := by simp only [left, middle, hleft, ↓reduceIte]; rfl
      omega
    · have hfalse : (first && tv == tv1) = false := Bool.eq_false_iff.mpr hleft
      have hhg : left.gcaFirst = st.gcaFirst := by
        dsimp only [left, middle]
        rw [ite_eq_right hleft]
        dsimp only [raw]
        rw [hfalse, node_gca]
        cases first <;> rfl
      rw [hhg] at htarget
      have hpos : 0 < st.canonlevel := by
        rcases h.phase with ⟨hf, _, _, _, hcell, hcursor, _⟩ | ⟨_, hcmp, _⟩
        · have he : tv1 = tv := by rw [h.tv1_eq, ← hcell, ← hcursor]; rfl
          simp [hf, he] at hleft
        · rw [hcmp.canonical.blen]
          exact List.length_pos_iff.mpr hcmp.nonempty
      have hf : first = false := by
        cases hf : first with
        | false => rfl
        | true => have hh := (h.control hpos).1 hf; omega
      have hh := h.scope.coset t p hp hpos htarget
      refine ⟨hh.1, ?_⟩
      dsimp only [ready]
      rw [recover_coset]
      dsimp only [left, middle]
      rw [ite_eq_right hleft]
      dsimp only [raw]
      rw [hfalse, node_coset]
      rw [hf]
      exact hh.2

end Hex.GraphIso.Nauty.Max
