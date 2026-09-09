/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEntry
public import HexGraphIso.Nauty.Policy.MaxAncestors
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxAncestors
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Preparation retains the installed incumbent's depth. -/
theorem Loop.canonlevel (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) :
    (l.prepare ctx tcLevel).2.2.2.2.canonlevel = l.node.entry.canonlevel := by
  unfold Loop.prepare
  dsimp only
  simp only [cheapCheck, apply_ite Search.canonlevel, ite_self]
  cases hf : l.first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [chooseTarget_fields]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.canonlevel, ite_self]
    rfl
  · simp only [↓reduceIte]
    rw [chooseFirst_fields]
    rfl

/-- Preparation preserves the first-path child's coset index. -/
theorem Loop.coset (ctx : Ctx n) (tcLevel : Nat) (l : Loop n) :
    (l.prepare ctx tcLevel).2.2.2.2.cosetindex = l.node.entry.cosetindex := by
  unfold Loop.prepare
  dsimp only
  simp only [cheapCheck, apply_ite Search.cosetindex, ite_self]
  cases hf : l.first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [chooseTarget_fields]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.cosetindex, ite_self]
    rfl
  · simp only [↓reduceIte]
    rw [chooseFirst_fields]
    rfl

/-- Both comparison machines require an installed incumbent. -/
theorem comparison_positive {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) : 0 < st.canonlevel := by
  rw [h.canonical.blen]
  exact List.length_pos_iff.mpr h.nonempty

/-- First-child cleanup and canonical recovery establish the same ordered
positive counters as a later child's ordinary return. -/
theorem SweepInput.recovered_counters {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcounter : 0 < st.canonlevel → 0 < st.gcaFirst ∧ st.gcaFirst ≤ st.gcaCanon) :
    let raw := (Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := recoverLevels level (recoverPtn (n + 2) level left)
    0 < ready.gcaFirst ∧ ready.gcaFirst ≤ ready.gcaCanon := by
  intro raw middle left ready
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hgc : ready.gcaCanon = min level raw.gcaCanon := by
    rw [recover_canon]
    change min level left.gcaCanon = _
    dsimp only [left, middle]
    split <;> rfl
  have hgf : ready.gcaFirst = left.gcaFirst := (gcaPolicy ctx (n + 2) tcLevel).recover level left
  by_cases hcf : (first && tv == tv1) = true
  · have hi := h.push hgsz hsymm hloop
    rw [hcf] at hi
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 hi.frame.positive hi.frame.partition
      (empty_orbits hi.entry.1.orbits hi.entry.2.2.2.2.1) hi.fuel
    have hc := firstPath_canon (inf := n + 2) path (bound := level)
      (by dsimp only [Parent.child]; rw [← h.level_eq]; omega)
    dsimp only [Parent.child] at hc
    rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hc
    change level ≤ (Nauty.node true ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)).2.gcaCanon at hc
    have hr : level ≤ raw.gcaCanon := by dsimp only [raw]; rwa [hcf]
    have hleft : left.gcaFirst = level := by simp only [left, middle, hcf, ↓reduceIte]; rfl
    rw [hgf, hleft, hgc]
    exact ⟨hl, by omega⟩
  · have hfalse : (first && tv == tv1) = false := Bool.eq_false_iff.mpr hcf
    have hp : Nauty.SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st ∧
        Comparison ctx (l.codes ctx) bs fs st := by
      rcases h.phase with ⟨hf, _, _, _, hcell, hcursor, _⟩ | ⟨hp, hc, _⟩
      · have he : tv1 = tv := by rw [h.tv1_eq, ← hcell, ← hcursor]; rfl
        simp [hf, he] at hcf
      · exact ⟨hp, hc⟩
    obtain ⟨hgpos, horder⟩ := hcounter (comparison_positive hp.2)
    have hi := h.push hgsz hsymm hloop
    rw [hfalse] at hi
    have ho := node_order (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
      hn0 hi.frame.positive hi.frame.partition hi.entry.1.ancestor
      (by dsimp only [Parent.child]; cases hf : l.first <;> exact horder)
    dsimp only [Parent.child] at ho
    rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at ho
    have hraw : raw.gcaFirst = st.gcaFirst ∧ raw.gcaFirst ≤ raw.gcaCanon := by
      dsimp only [raw]
      rw [hfalse]
      cases first <;> exact ho
    have hleft : left.gcaFirst = raw.gcaFirst := by dsimp only [left, middle]; rw [ite_eq_right hcf]
    rw [hgf, hleft, hgc]
    have hb := hp.1.ancestor
    exact ⟨by rw [hraw.1]; exact hgpos, by omega⟩

/-- After receipt, a first sweep names itself as first ancestor and an
ordinary sweep retains its strict first ancestor. -/
theorem SweepInput.recovered_control {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents) :
    let raw := (Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := recoverLevels level (recoverPtn (n + 2) level left)
    (first = true → ready.gcaFirst = level) ∧ (first = false → ready.gcaFirst < level) := by
  intro raw middle left ready
  have hg : ready.gcaFirst = left.gcaFirst := (gcaPolicy ctx (n + 2) tcLevel).recover level left
  rw [hg]
  by_cases hc : (first && tv == tv1) = true
  · have hl : left.gcaFirst = level := by simp only [left, middle, hc, ↓reduceIte]; rfl
    refine ⟨fun _ => hl, ?_⟩
    intro hf
    simp [hf] at hc
  · have hfalse : (first && tv == tv1) = false := Bool.eq_false_iff.mpr hc
    have he : left.gcaFirst = st.gcaFirst := by
      dsimp only [left, middle]
      rw [ite_eq_right hc]
      dsimp only [raw]
      rw [hfalse, node_gca]
      cases first <;> rfl
    rw [he]
    rcases h.phase with ⟨hf, _, _, _, hcell, hcursor, _⟩ | ⟨_, hcmp, _⟩
    · have ht : tv1 = tv := by rw [h.tv1_eq, ← hcell, ← hcursor]; rfl
      simp [hf, ht] at hc
    · exact h.control (comparison_positive hcmp)

end Hex.GraphIso.Nauty.Max
