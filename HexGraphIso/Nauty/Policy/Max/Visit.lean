/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Resume
import all HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Policy.Max.Resume
import all HexGraphIso.Nauty.Policy.Max.Receive
import all HexGraphIso.Nauty.Policy.Max.Unwind
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Suspend
import all HexGraphIso.Nauty.Policy.Generic.Maximum
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The actual received child and suffix compose with the identical
semantic incumbent at recovery, including incumbent installation. -/
theorem SweepInput.received_result {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel (cfuel + 1) first level numcells tc tv1
      (some tv) cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hs : (contract G tcLevel).sweepValid fuel cfuel
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel))
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : Nauty.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind level short, out)) :
    let ctx : Ctx n := { g := rowsOf G }
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := Nauty.recover (n + 2) level left
    (first = true → ∀ γ ∈ ready.genTrace,
      CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level
        (l.prepare ctx tcLevel).2.2.2.2.lab γ) →
    (∀ t p, parents t = some p → p.loop.first = true →
      ∀ γ ∈ ready.genTrace, CellStab p.state.ptn t p.state.lab γ) →
    let result := Generic.sweepStep (n + 2)
      (Generic.nodeCall ctx (n + 2) tcLevel fuel)
      (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)
      first level numcells tc tv1 tv cell index st
    Generic.Result (l.bound ctx tcLevel) (st.key ctx bs) (result.2.2.best ctx) level
      (Witness ctx tcLevel ((parents.frames ctx tcLevel).insert l.node)) result.1 := by
  intro ctx middle left ready hgen hanc result
  let small := if short then shortprune cell left else cell
  let filtered := if !first && tv == tv1 then
    Nauty.longprune small left.fixedpts left.autos else small
  let nextIndex := if first && ready.orbits[tv]! == tv1 then index + 1 else index
  obtain ⟨bs', fs', hi, hread, hout⟩ := h.received_input hn hvisit hcall hgen hanc
  let next : Generic.SweepFn (Search n) n := Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel
  have hsuf := (hs first level numcells tc tv1 (filtered.nextElem (some tv)) filtered
    nextIndex ready trivial).1 l bs' fs' parents hi
  have hr := h.child_result hn
  dsimp only at hr
  rw [hcall] at hr
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hb := hr.bounded.mono (p.key_le h.suspend)
  have he : (p.child ctx tcLevel).entry.key ctx bs = st.key ctx bs := by
    dsimp only [p, Parent.child]
    cases hf : l.first <;> rfl
  change Generic.Bounded (l.bound ctx tcLevel) ((p.child ctx tcLevel).entry.key ctx bs)
    (out.best ctx) at hb
  rw [he, hout] at hb
  have hstep := (h.receive_call hn hvisit hcall next).1
  change result = next first level numcells tc tv1 (filtered.nextElem (some tv))
    filtered nextIndex ready at hstep
  rw [hstep]
  exact ⟨hb.trans hsuf.bounded, hsuf.coverage⟩

/-- Every actual visiting branch satisfies the maximum contract once
received generators stabilize the current and suspended first frames. -/
theorem SweepInput.visit {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel (cfuel + 1) first level numcells tc tv1
      (some tv) cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hs : (contract G tcLevel).sweepValid fuel cfuel
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel))
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hreturn : ∀ short out,
      Nauty.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
        (level + 1) (numcells + 1) (Nauty.child first level tc tv st) =
          (.unwind level short, out) →
      let ctx : Ctx n := { g := rowsOf G }
      let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
      let left := { middle with fixedpts := middle.fixedpts.erase tv }
      let ready := Nauty.recover (n + 2) level left
      (first = true → ∀ γ ∈ ready.genTrace,
        CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level
          (l.prepare ctx tcLevel).2.2.2.2.lab γ) ∧
      (∀ t p, parents t = some p → p.loop.first = true →
        ∀ γ ∈ ready.genTrace, CellStab p.state.ptn t p.state.lab γ)) :
    let ctx : Ctx n := { g := rowsOf G }
    let result := Generic.sweepStep (n + 2)
      (Generic.nodeCall ctx (n + 2) tcLevel fuel)
      (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)
      first level numcells tc tv1 tv cell index st
    Generic.Result (l.bound ctx tcLevel) (st.key ctx bs) (result.2.2.best ctx) level
      (Witness ctx tcLevel ((parents.frames ctx tcLevel).insert l.node)) result.1 := by
  obtain ⟨target, short, out, hcall⟩ := h.child_exit
    (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  have hr := h.child_result hn
  dsimp only at hr
  rw [hcall] at hr
  have ht : target ≤ level := hr.coverage.1
  by_cases he : target < level
  · exact visit_unwind G tcLevel fuel cfuel hn first short level numcells tc tv1 tv index target
      cell st out hvisit hcall he l bs fs parents h
  · have heq : target = level := by omega
    subst target
    obtain ⟨hgen, hanc⟩ := hreturn short out hcall
    exact h.received_result hn hs hvisit hcall hgen hanc

end Hex.GraphIso.Nauty.Max
