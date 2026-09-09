/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxReturnTrace
public import HexGraphIso.Nauty.Policy.MaxSkip
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxSkip
import all HexGraphIso.Nauty.Policy.MaxExit
import all HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxCarry
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A nonlocal child return preserves accumulated generators at exactly
the older first frames that survive its unchanged exit. -/
theorem SweepInput.unwind_keeps {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index target : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (next : Generic.SweepFn (Search n) n)
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : Nauty.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind target short, out))
    (ht : target < level) :
    let result := Generic.sweepStep (n + 2)
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel) next
      first level numcells tc tv1 tv cell index st
    Keeps parents result.1 result.2.2 := by
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
  let cleaned := { middle with fixedpts := middle.fixedpts.erase tv }
  have hc : Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel (first && tv == tv1)
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind target short, out) := by
    simpa only [Generic.nodeCall, ← node_eq_generic] using hcall
  have hstep : Generic.sweepStep (n + 2)
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel) next
      first level numcells tc tv1 tv cell index st = (.unwind target short, index, cleaned) := by
    unfold Generic.sweepStep
    dsimp only [policy, Generic.Policy.orbit, Generic.Policy.child,
      Generic.Policy.afterChildFirst, Generic.Policy.leaveChild]
    simp only [hvisit, ↓reduceIte, hc, Generic.advance, ht, Id.run_pure, apply_ite Id.run]
    dsimp only [cleaned, middle]
    split <;> rfl
  have hr := h.child_keeps hn
  dsimp only at hr
  rw [hcall] at hr
  rw [hstep]
  dsimp only
  intro t q hq hf htarget γ hγ
  have he : cleaned.genTrace = out.genTrace := by dsimp only [cleaned, middle]; split <;> rfl
  rw [he] at hγ
  have htl := (h.scope.valid t q hq).2.1
  have hp : (parents.push p) t = some q := by
    simpa only [Parents.push, p, ← h.level_eq, show t ≠ level by omega, ↓reduceIte] using hq
  exact hr t q hp hf htarget γ hγ

/-- Reception derives its generator inputs from the child contract and
then preserves the entire trace returned by the actual resumed suffix. -/
theorem SweepInput.received_keeps {G : Colored n k} {tcLevel fuel cfuel : Nat}
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
    let result := Generic.sweepStep (n + 2)
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel)
      first level numcells tc tv1 tv cell index st
    Keeps parents result.1 result.2.2 := by
  let ctx : Ctx n := { g := rowsOf G }
  let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
  let left := { middle with fixedpts := middle.fixedpts.erase tv }
  let ready := recoverLevels level (recoverPtn (n + 2) level left)
  let small := if short then shortprune cell left else cell
  let filtered := if !first && tv == tv1 then Nauty.longprune small left.fixedpts left.autos else small
  let nextIndex := if first && ready.orbits[tv]! == tv1 then index + 1 else index
  obtain ⟨hgen, hanc⟩ := h.received_generators hn hcall
  obtain ⟨bs', fs', hi, _, _⟩ := h.received_input hn hvisit hcall hgen hanc
  have hr := (hs first level numcells tc tv1 (filtered.nextElem (some tv)) filtered
    nextIndex ready trivial).2 l bs' fs' parents hi
  have he := (h.receive_call hn hvisit hcall
    (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).1
  rw [he]
  exact hr

/-- Both sweep branches preserve accumulated generators in the same
induction as their maximum result, with no additional recursive premise. -/
theorem sweep_trace (G : Colored n k) (tcLevel : Nat) : SweepTraceRule G tcLevel := by
  intro fuel cfuel hn hs first level numcells tc tv1 tv cell index st l bs fs parents h
  by_cases hv : (!first || st.orbits[tv]! == tv) = true
  · obtain ⟨target, short, out, hcall⟩ := h.child_exit
      (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
    have hr := h.child_result hn
    dsimp only at hr
    rw [hcall] at hr
    have ht : target ≤ level := hr.coverage.1
    by_cases hlt : target < level
    · exact h.unwind_keeps hn _ hv hcall hlt
    · have he : target = level := by omega
      subst target
      exact h.received_keeps hn hs hv hcall
  · have hskip : (!first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hv
    have hi := h.skip_input (size_rowsOf G) hskip
    have hr := (hs first level numcells tc tv1 (cell.nextElem (some tv)) cell
      (if first && st.orbits[tv]! == tv1 then index + 1 else index) st trivial).2 l bs fs parents hi
    simpa only [Generic.sweepStep, policy, Generic.Policy.orbit, hskip,
      Bool.false_eq_true, ↓reduceIte, Id.run_pure] using hr

end Hex.GraphIso.Nauty.Max
