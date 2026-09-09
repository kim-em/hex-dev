/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Stab
public import HexGraphIso.Nauty.Policy.Max.Carry
import all HexGraphIso.Nauty.Policy.Max.Stab
import all HexGraphIso.Nauty.Policy.Max.Carry
import all HexGraphIso.Nauty.Policy.Max.Auto
import all HexGraphIso.Nauty.Policy.Max.Canon
import all HexGraphIso.Nauty.Policy.Max.Emit
import all HexGraphIso.Nauty.Policy.Max.Control
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A leaf action either retains the entry trace or appends precisely
its checked scratch permutation. -/
theorem Frame.emit_trace (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) :
    let p := prepareOther ctx tcLevel f.level f.numcells f.entry
    let leaf := (classify ctx f.level p.1 p.2.2.2.2.2).1
    (f.emit ctx tcLevel).2.genTrace = match leaf with
      | .autoFirst | .autoCanon => f.entry.genTrace.push (f.emit ctx tcLevel).2.workperm
      | _ => f.entry.genTrace := by
  intro p leaf
  let c := classify ctx f.level p.1 p.2.2.2.2.2
  have ht : c.2.genTrace = f.entry.genTrace := by
    dsimp only [c]
    rw [classify_trace]
    dsimp only [p, prepareOther]
    rw [chooseTarget_fields]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.genTrace, ite_self]
    rfl
  have hw : (f.emit ctx tcLevel).2.workperm = c.2.workperm := leafExit_workperm c.1 f.level c.2
  change (leafExit c.1 f.level c.2).2.genTrace = _
  rw [leafExit_trace, hw, ht]
  rfl

/-- Every code-two exit names either the first or canonical ancestor. -/
theorem canon_target {level target : Nat} {short : Bool} {st : Search n}
    (he : (leafExit .autoCanon level st).1 = .unwind target short) :
    target = st.gcaFirst ∨ target = st.gcaCanon := by
  unfold leafExit at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  repeat' split at he
  all_goals simp only [admit_gca, admit_canon] at he
  all_goals cases he
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

/-- Every actual emission preserves the accumulated generator carriers
at all surviving first ancestors, including the code-two coset exit. -/
theorem NodeInput.emit_keeps {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Keeps parents (f.emit ctx tcLevel).1 (f.emit ctx tcLevel).2 := by
  intro t p hp hf ht γ hγ
  let prep := prepareOther ctx tcLevel f.level f.numcells f.entry
  let c := classify ctx f.level prep.1 prep.2.2.2.2.2
  have hcounters := h.counters (comparison_positive h.entry.2)
  rw [f.emit_trace] at hγ
  change γ ∈ (match c.1 with
    | .autoFirst | .autoCanon => f.entry.genTrace.push (f.emit ctx tcLevel).2.workperm
    | _ => f.entry.genTrace) at hγ
  cases hc : c.1 with
  | internal =>
    simp only [hc] at hγ
    exact h.scope.generators t p hp hf γ hγ
  | better sr =>
    simp only [hc] at hγ
    exact h.scope.generators t p hp hf γ hγ
  | bad =>
    simp only [hc] at hγ
    exact h.scope.generators t p hp hf γ hγ
  | autoFirst =>
    simp only [hc, Array.mem_push] at hγ
    rcases hγ with hγ | rfl
    · exact h.scope.generators t p hp hf γ hγ
    · have hx := first_exit f.level c.2
      rw [← hc] at hx
      change (f.emit ctx tcLevel).1 = .unwind (f.emit ctx tcLevel).2.gcaFirst false at hx
      rw [(f.emit_first ctx tcLevel).2] at hx
      rw [hx] at ht
      obtain ⟨q, hq⟩ := h.scope.complete f.entry.gcaFirst hcounters.1 h.entry.1.ancestor
      exact h.scope.stab_below hp hq ht (h.first_stab hgsz hsymm hloop hc hq)
  | autoCanon =>
    simp only [hc, Array.mem_push] at hγ
    rcases hγ with hγ | rfl
    · exact h.scope.generators t p hp hf γ hγ
    · have hdone : (f.emit ctx tcLevel).1 ≠ .done := by
        intro he
        have hh := (leafExit_done c.1 f.level c.2).mp he
        rw [hc] at hh
        cases hh
      have hnf : (f.emit ctx tcLevel).1 ≠ .fuel := leafExit_noFuel c.1 f.level c.2
      obtain ⟨target, short, he⟩ : ∃ target short, (f.emit ctx tcLevel).1 = .unwind target short := by
        cases he : (f.emit ctx tcLevel).1 with
        | done => exact (hdone he).elim
        | fuel => exact (hnf he).elim
        | unwind target short => exact ⟨target, short, rfl⟩
      have htarget := canon_target (st := c.2) (level := f.level)
        (by change (leafExit c.1 f.level c.2).1 = _ at he; rwa [hc] at he)
      have hgf : c.2.gcaFirst = f.entry.gcaFirst := by
        have heq : (leafExit c.1 f.level c.2).2.gcaFirst = c.2.gcaFirst := leafExit_gca ..
        exact heq.symm.trans (f.emit_first ctx tcLevel).2
      have hgc : c.2.gcaCanon = f.entry.gcaCanon := by
        have heq : (leafExit c.1 f.level c.2).2.gcaCanon = c.2.gcaCanon := by rw [hc, autoCanon_ancestor]
        exact heq.symm.trans (f.emit_canon hc).2
      rw [hgf, hgc] at htarget
      rw [he] at ht
      have hle : t ≤ f.entry.gcaCanon := by rcases htarget with htarget | htarget <;> omega
      obtain ⟨q, hq⟩ := h.scope.complete f.entry.gcaCanon (by omega) h.entry.1.canonAncestor
      exact h.scope.stab_below hp hq hle (h.canon_stab hgsz hsymm hloop hc hq)

end Hex.GraphIso.Nauty.Max
