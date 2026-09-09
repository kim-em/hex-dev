/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.ReturnTrace
public import HexGraphIso.Nauty.Policy.Max.Skip
public import HexGraphIso.Nauty.Generation.Counted
import all HexGraphIso.Nauty.Generation.Counted
import all HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Max.Restore
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.Resume
import all HexGraphIso.Nauty.Policy.Max.ReturnTrace
import all HexGraphIso.Nauty.Policy.Max.Skip
import all HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Policy.Max.Unwind
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The counter records checked carriers to the guiding vertex in the
original target partition, independently of the mutable surviving set. -/
def Loop.Count (ctx : Ctx n) (tcLevel guide : Nat) (l : Loop n)
    (previous : Option Nat) (index : Nat) : Prop :=
  let p := l.prepare ctx tcLevel
  Generation.Counted (segN p.2.2.2.2.lab p.2.1.toNat p.2.2.2.1)
    (fun v => ∃ γ, checkAutom ctx.g γ = true ∧
      CellStab p.2.2.2.2.ptn l.node.level p.2.2.2.2.lab γ ∧ γ[v]! = guide)
    previous index

/-- The actual orbit-counter test supplies a checked carrier for the
vertex counted, using the current trace in the frozen parent partition. -/
theorem SweepInput.mark {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st ready : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n} {previous : Option Nat}
    (h : SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hc : l.Count ctx tcLevel tv1 previous index) (ha : After previous tv)
    (ho : OrbitsOk ready) (ht : TraceOk ctx ready)
    (hg : ∀ γ ∈ ready.genTrace, CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn
      level (l.prepare ctx tcLevel).2.2.2.2.lab γ) :
    l.Count ctx tcLevel tv1 (some tv)
      (if ready.orbits[tv]! == tv1 then index + 1 else index) := by
  unfold Loop.Count at hc ⊢
  dsimp only at hc ⊢
  rw [← h.level_eq, ← h.tc_eq] at hc ⊢
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  apply hc.cellStep ha
    ((mem_windowSet.mp (h.subset tv (h.cursor_mem tv rfl))).2)
    (VSet.mem_lt (h.cursor_mem tv rfl))
    (labOk_of_reach h.base.labSize h.base.reach) h.base.ptnSize h.base.labSize
    (searchOk_end hn0 h.base (by rw [h.level_eq]; exact h.node.positive)) ho
  · exact fun γ hγ => ht γ (by simpa using hγ)
  · exact fun γ hγ => hg γ (by simpa using hγ)

/-- The first sweep's counter has witnesses for distinct original
vertices. Child contracts provide the accumulated cell stabilizers at
actual returns; neither key equality nor transitivity is assumed. -/
theorem SweepInput.counted {G : Colored n k} {tcLevel fuel : Nat}
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)) :
    ∀ cfuel level numcells tc tv1 cursor cell index st l bs fs parents previous,
      SweepInput G { g := rowsOf G } tcLevel fuel cfuel true level numcells tc tv1 cursor
        cell index st l bs fs parents →
      l.Count { g := rowsOf G } tcLevel tv1 previous index →
      (∀ tv, cursor = some tv → After previous tv) →
      ∃ last, l.Count { g := rowsOf G } tcLevel tv1 last
        (Nauty.sweep true { g := rowsOf G } (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st).2.1 := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor cell index st l bs fs parents previous h hc _
    cases cursor <;> simp only [Nauty.sweep] <;> exact ⟨previous, hc⟩
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor cell index st l bs fs parents previous h hc ha
    cases cursor with
    | none => simp only [Nauty.sweep]; exact ⟨previous, hc⟩
    | some tv =>
      have hafter : ∀ cell : VSet n, ∀ v, cell.nextElem (some tv) = some v → After (some tv) v := by
        intro cell v hv
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        change tv < v
        omega
      by_cases hv : (!true || st.orbits[tv]! == tv) = true
      · obtain ⟨target, short, out, hcall⟩ := h.child_exit
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        have hr := h.child_result hn
        dsimp only at hr
        rw [hcall] at hr
        have ht : target ≤ level := hr.coverage.1
        by_cases hlt : target < level
        · rw [Nauty.sweep]
          simp only [hv, ↓reduceIte, hcall, hlt, Id.run_pure, apply_ite Id.run]
          split <;> exact ⟨previous, hc⟩
        · have he : target = level := by omega
          subst target
          let ctx : Ctx n := { g := rowsOf G }
          let middle := if true && tv == tv1 then afterChildFirst level tv1 out else out
          let left := { middle with fixedpts := middle.fixedpts.erase tv }
          let ready := Nauty.recover (n + 2) level left
          let filtered := if short then shortprune cell left else cell
          obtain ⟨hgen, hanc⟩ := h.received_generators hn hcall
          obtain ⟨bs', fs', hi, _, _⟩ := h.received_input hn hv hcall hgen hanc
          have hp := h.restore (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hv
          rw [hcall] at hp
          change Nauty.SweepPre G ctx tcLevel true level numcells tc tv1 none cell ready at hp
          have hc' := h.mark hc (ha tv rfl) hp.stored.orbits hp.stored.trace (hgen rfl)
          have hh := ih level numcells tc tv1 (filtered.nextElem (some tv)) filtered
            (if ready.orbits[tv]! == tv1 then index + 1 else index) ready l bs' fs' parents
            (some tv) hi hc' (hafter filtered)
          have he := (h.receive_call hn hv hcall
            (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).1
          unfold Generic.nodeCall Generic.sweepCall at he
          rw [sweep_eq_generic, Generic.sweep, he]
          simpa only [ctx, filtered, ready, left, middle, Generic.sweepCall, ← sweep_eq_generic, Bool.not_true, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Bool.true_and] using hh
      · have hskip : (!true || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hv
        obtain ⟨_, hp, _, _⟩ := h.skip_phase hskip
        have hc' := h.mark hc (ha tv rfl) hp.stored.orbits hp.stored.trace (h.generators rfl)
        have hi := h.skip_input (size_rowsOf G) hskip
        have hh := ih level numcells tc tv1 (cell.nextElem (some tv)) cell
          (if st.orbits[tv]! == tv1 then index + 1 else index) st l bs fs parents
          (some tv) hi hc' (hafter cell)
        rw [Nauty.sweep]
        simpa only [hskip, Bool.false_eq_true, ↓reduceIte, Id.run_pure, Bool.true_and] using hh

/-- A complete orbit count supplies a checked frozen-cell carrier for
every original target vertex, even if filters removed it from the sweep. -/
theorem SweepInput.full {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {level numcells tc tv1 : Nat} {cursor : Option Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel true level numcells tc tv1 cursor
      cell 0 st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hcount : (l.prepare { g := rowsOf G } tcLevel).2.2.2.1 ≤
      (Nauty.sweep true { g := rowsOf G } (n + 2) tcLevel fuel cfuel
        level numcells tc tv1 cursor cell 0 st).2.1) :
    ∀ v ∈ segN (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.lab tc
      (l.prepare { g := rowsOf G } tcLevel).2.2.2.1,
      ∃ γ, checkAutom (rowsOf G) γ = true ∧
        CellStab (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.ptn level
          (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.lab γ ∧ γ[v]! = tv1 := by
  have hs : l.Count { g := rowsOf G } tcLevel tv1 none 0 :=
    Generation.Counted.start _ _
  obtain ⟨last, hc⟩ := SweepInput.counted hn cfuel level numcells tc tv1 cursor cell 0 st
    l bs fs parents none h hs (by intros; trivial)
  unfold Loop.Count at hc
  dsimp only at hc
  rw [← h.tc_eq, ← h.level_eq] at hc
  exact hc.full (by rw [segN_length]; exact hcount)

end Hex.GraphIso.Nauty.Max
