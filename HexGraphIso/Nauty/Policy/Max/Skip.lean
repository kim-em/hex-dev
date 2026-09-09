/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Receive
public import HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Boundary
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.First.Path
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- An orbit skip occurs only after the first leaf has initialized the
persistent state and settled the comparison. -/
theorem SweepInput.skip_phase {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    first = true ∧ Nauty.SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st ∧
      Comparison ctx (l.codes ctx) bs fs st ∧ st.compCanon ≤ 0 := by
  have hf : first = true := by cases first <;> simp_all
  have hne : st.orbits[tv]! ≠ tv := by simpa only [hf, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne] using hskip
  rcases h.phase with ⟨_, _, _, hst, _⟩ | ⟨hp, hc, hle⟩
  · obtain ⟨bs₀, fs₀, he⟩ := h.origin
    rw [hf] at he
    obtain ⟨hp, _, _, _, ht, _⟩ := he
    have horb : st.orbits = l.node.entry.orbits := by
      rw [hst, l.first_prepare (h.first_eq.symm.trans hf)]
      dsimp only
      unfold cheapCheck
      split <;> exact prepareFirst_orbits ctx tcLevel _ _ _
    have hv := VSet.mem_lt (h.cursor_mem tv rfl)
    exact False.elim (hne (horb ▸ empty_orbits hp.orbits ht tv hv))
  · exact ⟨hf, hp, hc, hle.elim id (fun he => by simp [hf] at he)⟩

/-- The consulted orbit pointer has a checked carrier stabilizing the
frozen target partition, with a strictly smaller endpoint. -/
theorem SweepInput.skip_carrier {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    ∃ γ, checkAutom ctx.g γ = true ∧
      CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level
        (l.prepare ctx tcLevel).2.2.2.2.lab γ ∧
      γ[tv]! = st.orbits[tv]! ∧ st.orbits[tv]! < tv := by
  obtain ⟨hf, hp, _, _⟩ := h.skip_phase hskip
  have hv := VSet.mem_lt (h.cursor_mem tv rfl)
  obtain ⟨_, _, w, hw, he⟩ := (hp.stored.orbits.2 tv hv).2
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  obtain ⟨ha, hs, hvw⟩ := wordPerm_spec
    (labOk_of_reach h.base.labSize h.base.reach) h.base.ptnSize h.base.labSize
    (searchOk_end hn0 h.base hl)
    (fun γ hγ => hp.stored.trace γ (by simpa using hγ))
    (fun γ hγ => h.generators hf γ (by simpa using hγ)) w hw
  refine ⟨wordPerm n w, ha, hs, (hvw tv hv).trans he, ?_⟩
  have hle := (hp.stored.orbits.2 tv hv).1
  have hne : st.orbits[tv]! ≠ tv := by simpa only [hf, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne] using hskip
  omega

/-- The carrier supplied by the actual orbit test removes the current
vertex from ranked coverage, even after earlier filters. -/
theorem SweepInput.skip_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (Remaining (cell.nextElem (some tv)) cell) (st.key ctx bs) := by
  obtain ⟨γ, ha, hs, he, hlt⟩ := h.skip_carrier hskip
  have hv := h.subset tv (h.cursor_mem tv rfl)
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hd : level ≤ n := by rw [h.level_eq]; exact h.node.depth
  have hr : tc + (l.prepare ctx tcLevel).2.2.2.1 ≤ (l.prepare ctx tcLevel).2.2.2.2.lab.size := by
    rw [show (l.prepare ctx tcLevel).2.2.2.2.lab.size = n from h.base.labSize]
    exact h.range
  have hm := windowSet_carry hs h.window hr (labOk_of_reach h.base.labSize h.base.reach) hv
  have hk := h.base.vertex_key hn0 hl hgsz ha hs h.window h.range hv (by omega : level + 1 + (n - level) ≤ n + 1) tcLevel
  have hc := h.coverage.skip (tv := tv) (rep := γ[tv]!)
    (fun v hv => by obtain ⟨_, w, hw, hle⟩ := hv; cases hw; exact hle)
    hm (by rw [he]; exact hlt) hk
  intro v hv
  rcases hc v hv with hd | ⟨w, hw, hk, hr⟩
  · exact Or.inl hd
  · exact Or.inr ⟨w, Remaining.next.mpr ⟨hw.1.1, hw.2⟩, hk, hr⟩

/-- Advancing past an orbit skip supplies the complete unchanged-state
input to the smaller suffix contract. -/
theorem SweepInput.skip_input {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hskip : (!first || st.orbits[tv]! == tv) = false) :
    SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1
      (cell.nextElem (some tv)) cell
      (if first && st.orbits[tv]! == tv1 then index + 1 else index) st l bs fs parents := by
  obtain ⟨_, hp, hc, hle⟩ := h.skip_phase hskip
  exact ⟨h.node, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq, h.tv1_eq, h.origin,
    h.base, h.partition, h.effect, h.equitable, h.target, h.window, h.len, h.range,
    h.subset, (fun _ hv => VSet.nextElem_mem hv), h.fuel,
    Generic.CursorFuel.next (h.cursor_fuel tv rfl), h.path, h.choice, h.small,
    Or.inr ⟨hp.next (fun _ hv => hv), hc, Or.inl hle⟩,
    h.skip_cover hgsz hskip, h.canonical, h.first_ref, h.generators, h.scope, h.parent, h.counters, h.control⟩

/-- Every actual orbit skip satisfies the full local maximum rule. -/
theorem skip (G : Colored n k) (tcLevel : Nat) : SweepRule G tcLevel false := by
  intro fuel cfuel _ hs first level numcells tc tv1 tv cell index st hskip l bs fs parents hi
  have hn := hi.skip_input (size_rowsOf G) hskip
  have hr := (hs first level numcells tc tv1 (cell.nextElem (some tv)) cell
    (if first && st.orbits[tv]! == tv1 then index + 1 else index) st trivial).1 l bs fs parents hn
  change Generic.Result _ _ _ _ _ _ at hr ⊢
  simpa only [Generic.sweepStep, policy, Generic.Policy.orbit, hskip,
    Bool.false_eq_true, ↓reduceIte, Id.run_pure] using hr

end Hex.GraphIso.Nauty.Max
