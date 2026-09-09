/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Control
public import HexGraphIso.Nauty.Policy.Max.Scope
public import HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.First
import all HexGraphIso.Nauty.Policy.Max.Scope
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.Codes
import all HexGraphIso.Nauty.Policy.Max.Restore
import all HexGraphIso.Nauty.Policy.Max.Small
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Choice
import all HexGraphIso.Nauty.Policy.Max.Suspend
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Reception constructs the complete suffix input from the actual child
contract and return-local generator premises. -/
theorem SweepInput.received_input {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel (cfuel + 1) first level numcells tc tv1
      (some tv) cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : Nauty.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind level short, out)) :
    let ctx : Ctx n := { g := rowsOf G }
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let small := if short then shortprune cell left else cell
    let filtered := if !first && tv == tv1 then
      Nauty.longprune small left.fixedpts left.autos else small
    let ready := Nauty.recover (n + 2) level left
    let nextIndex := if first && ready.orbits[tv]! == tv1 then index + 1 else index
    (first = true → ∀ γ ∈ ready.genTrace,
      CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level
        (l.prepare ctx tcLevel).2.2.2.2.lab γ) →
    (∀ t p, parents t = some p → p.loop.first = true →
      ∀ γ ∈ ready.genTrace, CellStab p.state.ptn t p.state.lab γ) →
    ∃ bs' fs', SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1
      (filtered.nextElem (some tv)) filtered nextIndex ready l bs' fs' parents ∧
      ready.best ctx = ready.key ctx bs' ∧ out.best ctx = ready.key ctx bs' := by
  intro ctx middle left small filtered ready nextIndex hgen hanc
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hi := h.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  have hr := h.child_result hn
  dsimp only at hr
  rw [hcall] at hr
  have hb : (p.child ctx tcLevel).entry.key ctx bs = st.key ctx bs := by
    dsimp only [p, Parent.child]
    cases hf : l.first <;> rfl
  have hg := hr.bounded.grows
  change Generic.Grows ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) at hg
  rw [hb] at hg
  have hc : Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) (out.best ctx) := by
    simpa only [Generic.ExitCover, ↓reduceIte] using hr.coverage.2
  rw [p.key h.suspend] at hc
  have hlen : (l.codes ctx).length = level := by
    have hh := h.node.length
    have he := h.level_eq
    simp only [Loop.codes, List.length_append, List.length_singleton]
    omega
  have hcodes := hi.recovered_codes (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
    (first && tv == tv1) tv1 tv
  dsimp only [Parent.child] at hcodes
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq, hlen, Nat.add_sub_cancel,
    hcall] at hcodes
  obtain ⟨bs', fs', hcomp, hnonpos, hread, hout⟩ := hcodes
  change Comparison ctx (l.codes ctx) bs' fs' ready at hcomp
  change ready.compCanon ≤ 0 at hnonpos
  change ready.best ctx = ready.key ctx bs' at hread
  change out.best ctx = ready.key ctx bs' at hout
  have hg' : Generic.Grows (st.key ctx bs) (ready.key ctx bs') := hout ▸ hg
  have hpre := h.restore (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hvisit
  rw [hcall] at hpre
  change Nauty.SweepPre G ctx tcLevel first level numcells tc tv1 none cell ready at hpre
  have hsub : ∀ v, filtered.mem v = true → cell.mem v = true := by
    intro v hv
    have hs : small.mem v = true := by
      dsimp only [filtered] at hv
      split at hv
      · exact Nauty.longprune_subset hv
      · exact hv
    dsimp only [small] at hs
    split at hs
    · exact Nauty.shortprune_subset (st := left) hs
    · exact hs
  have hpast : Generic.Past first tv1 (filtered.nextElem (some tv)) := by
    intro hf v hv
    have hnext := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hnext
    rcases h.phase with ⟨_, _, _, _, hcell, hcursor, _⟩ | ⟨hp, _⟩
    · have he : tv1 = tv := by rw [h.tv1_eq, ← hcell, ← hcursor]; rfl
      omega
    · have hh := hp.past hf tv rfl
      omega
  have hnext : Nauty.SweepPre G ctx tcLevel first level numcells tc tv1
      (filtered.nextElem (some tv)) filtered ready :=
    ⟨hpast, hpre.positive, hpre.partition, hpre.target.subset hsub,
      (fun _ hv => VSet.nextElem_mem hv), hpre.stored, hpre.ancestor, hpre.canonAncestor,
      hpre.history, hpre.recorded, hpre.equitable, hpre.boundary, hpre.cheapBound,
      hpre.path, hpre.small⟩
  have hframe := child_frame (first := first) h.partition hn0 hl h.path.fixed h.target
    (h.cursor_mem tv rfl) (first && tv == tv1) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  rw [hcall] at hframe
  have hleft : SearchOut G level level st left := by
    dsimp only [left, middle]
    split <;> exact hframe.1.congr rfl rfl rfl rfl
  have he := (reachPolicy G ctx tcLevel hn0).recover level numcells st left hl h.partition hleft
  have hbound : st.gcaCanon ≤ level := by
    rcases h.phase with ⟨hf, _, _, hst, _⟩ | ⟨hp, _⟩
    · obtain ⟨bs₀, fs₀, hentry⟩ := h.origin
      rw [hf] at hentry
      have hh := hentry.2.2.2.2.2.2.2.2.2
      rw [hst, (l.ancestors ctx tcLevel).2]
      have he := h.level_eq
      omega
    · exact hp.canonAncestor
  have hcanon := child_canon_guide (first := first) (tv1 := tv1)
    (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) h.partition hn0 hl h.target
    (h.cursor_mem tv rfl) hbound h.canonical h.effect hg' (hout ▸ hc)
  dsimp only at hcanon
  rw [hcall] at hcanon
  have hfirst := h.first_reference (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  rw [hcall] at hfirst
  have hgReady : Generic.Grows (st.key ctx bs) (ready.best ctx) := hread.symm ▸ hg'
  have hcReady : Generic.Covers (l.key ctx tcLevel tv) (ready.best ctx) :=
    hread.symm ▸ (hout ▸ hc)
  have hscope := h.restore_scope (bs' := bs') (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  rw [hcall] at hscope
  have hcover := (h.receive_call hn hvisit hcall
    (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).2
  change CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
    (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
    (Remaining (filtered.nextElem (some tv)) filtered) (ready.best ctx) at hcover
  rw [hread] at hcover
  have hcounter := h.recovered_counters (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) h.counters
  rw [hcall] at hcounter
  have hcontrol := h.recovered_control
  rw [hcall] at hcontrol
  refine ⟨bs', fs', ?_, hread, hout⟩
  exact ⟨h.node, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq, h.tv1_eq,
    h.origin, h.base, hpre.partition, h.effect.trans he.effect, hpre.equitable,
    hnext.target, h.window, h.len, h.range, (fun v hv => h.subset v (hsub v hv)),
    hnext.cursor_mem, h.fuel, Generic.CursorFuel.next (h.cursor_fuel tv rfl),
    hpre.path, h.choice.grow hg', hpre.subtree hn0, Or.inr ⟨hnext, hcomp, Or.inl hnonpos⟩,
    hcover, hcanon, (fun ht => by rw [← hread]; exact hfirst hgReady hcReady ht), hgen,
    hscope hg' hanc, h.parent, (fun _ => hcounter), (fun _ => hcontrol)⟩

end Hex.GraphIso.Nauty.Max
