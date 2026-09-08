/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic

public section

/-!
A proof may reuse independently established properties of recursive calls,
such as partition preservation, while proving their canonical bounds. These
rules retain the actual continuations alongside the induction hypotheses.
They derive from `SoundPolicy` by including the call equations in its
contract; no additional recursion or executable search is introduced.
-/

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ : Type} [Policy σ n]

/-- A node continuation at a fixed recursion bound. -/
def nodeCall (ctx : Ctx n) (inf tcLevel fuel : Nat) : NodeFn σ :=
  fun first level numcells st => node first ctx inf tcLevel fuel level numcells st

/-- A sweep continuation at fixed node and cursor bounds. -/
def sweepCall (ctx : Ctx n) (inf tcLevel fuel cfuel : Nat) : SweepFn σ n :=
  fun first level numcells tc tv1 cursor cell index st =>
    sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st

/-- Call equations are unconditional; the desired postcondition follows
when the original precondition holds. -/
def callContract (ctx : Ctx n) (inf tcLevel : Nat) (C : Contract σ n) : Contract σ n where
  nodePre _ _ _ _ _ := True
  nodePost fuel first level numcells st result :=
    result = node first ctx inf tcLevel fuel level numcells st ∧
      (C.nodePre fuel first level numcells st → C.nodePost fuel first level numcells st result)
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result :=
    result = sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st ∧
      (C.sweepPre fuel cfuel first level numcells tc tv1 cursor cell index st →
        C.sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result)

/-- Local induction rules expressed using the actual recursive calls. -/
structure CallPolicy (ctx : Ctx n) (inf tcLevel : Nat) (C : Contract σ n) : Prop where
  node_zero : ∀ first level numcells st, C.nodePre 0 first level numcells st →
    C.nodePost 0 first level numcells st (.fuel, st)
  node_step : ∀ fuel, C.sweepValid fuel (n + 1) (sweepCall ctx inf tcLevel fuel (n + 1)) →
    ∀ first level numcells st, C.nodePre (fuel + 1) first level numcells st →
      C.nodePost (fuel + 1) first level numcells st
        (nodeStep ctx tcLevel (sweepCall ctx inf tcLevel fuel (n + 1)) first level numcells st)
  sweep_none : ∀ fuel cfuel first level numcells tc tv1 cell index st,
    C.sweepPre fuel cfuel first level numcells tc tv1 none cell index st →
    C.sweepPost fuel cfuel first level numcells tc tv1 none cell index st (.done, index, st)
  sweep_zero : ∀ fuel first level numcells tc tv1 tv cell index st,
    C.sweepPre fuel 0 first level numcells tc tv1 (some tv) cell index st →
    C.sweepPost fuel 0 first level numcells tc tv1 (some tv) cell index st (.fuel, index, st)
  sweep_step : ∀ fuel cfuel,
    C.nodeValid fuel (nodeCall ctx inf tcLevel fuel) →
    C.sweepValid fuel cfuel (sweepCall ctx inf tcLevel fuel cfuel) →
    ∀ first level numcells tc tv1 tv cell index st,
      C.sweepPre fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st →
      C.sweepPost fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st
        (sweepStep inf (nodeCall ctx inf tcLevel fuel) (sweepCall ctx inf tcLevel fuel cfuel)
          first level numcells tc tv1 tv cell index st)

variable {ctx : Ctx n} {inf tcLevel : Nat} {C : Contract σ n}

/-- The call equations expose the actual node continuation and its contract. -/
theorem callContract.node_eq {fuel : Nat} {next : NodeFn σ}
    (h : (callContract ctx inf tcLevel C).nodeValid fuel next) :
    next = nodeCall ctx inf tcLevel fuel ∧ C.nodeValid fuel next := by
  constructor
  · funext first level numcells st
    exact (h first level numcells st trivial).1
  · intro first level numcells st hin
    exact (h first level numcells st trivial).2 hin

/-- The call equations expose the actual sweep continuation and its contract. -/
theorem callContract.sweep_eq {fuel cfuel : Nat} {next : SweepFn σ n}
    (h : (callContract ctx inf tcLevel C).sweepValid fuel cfuel next) :
    next = sweepCall ctx inf tcLevel fuel cfuel ∧ C.sweepValid fuel cfuel next := by
  constructor
  · funext first level numcells tc tv1 cursor cell index st
    exact (h first level numcells tc tv1 cursor cell index st trivial).1
  · intro first level numcells tc tv1 cursor cell index st hin
    exact (h first level numcells tc tv1 cursor cell index st trivial).2 hin

/-- Rules for actual calls satisfy the original generic induction principle. -/
theorem CallPolicy.sound (h : CallPolicy ctx inf tcLevel C) :
    SoundPolicy ctx inf tcLevel (callContract ctx inf tcLevel C) where
  node_zero := fun first level numcells st _ =>
    ⟨by rw [node], h.node_zero first level numcells st⟩
  node_step := by
    intro fuel next hnext first level numcells st _
    obtain ⟨rfl, hnext⟩ := callContract.sweep_eq hnext
    exact ⟨by rw [node]; rfl, h.node_step fuel hnext first level numcells st⟩
  sweep_none := fun fuel cfuel first level numcells tc tv1 cell index st _ =>
    ⟨by rw [sweep], h.sweep_none fuel cfuel first level numcells tc tv1 cell index st⟩
  sweep_zero := fun fuel first level numcells tc tv1 tv cell index st _ =>
    ⟨by rw [sweep], h.sweep_zero fuel first level numcells tc tv1 tv cell index st⟩
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st _
    obtain ⟨rfl, hdescend⟩ := callContract.node_eq hdescend
    obtain ⟨rfl, hnext⟩ := callContract.sweep_eq hnext
    exact ⟨by rw [sweep]; rfl,
      h.sweep_step fuel cfuel hdescend hnext first level numcells tc tv1 tv cell index st⟩

/-- Actual-call rules prove the node postcondition under its precondition. -/
theorem node_calls (h : CallPolicy ctx inf tcLevel C)
    (first : Bool) (fuel level numcells : Nat) (st : σ)
    (hin : C.nodePre fuel first level numcells st) :
    C.nodePost fuel first level numcells st (node first ctx inf tcLevel fuel level numcells st) :=
  (node_sound h.sound first fuel level numcells st trivial).2 hin

/-- Actual-call rules prove the sweep postcondition under its precondition. -/
theorem sweep_calls (h : CallPolicy ctx inf tcLevel C)
    (first : Bool) (fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : σ)
    (hin : C.sweepPre fuel cfuel first level numcells tc tv1 cursor cell index st) :
    C.sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st) :=
  (sweep_sound h.sound first fuel cfuel level numcells tc tv1 cursor cell index st trivial).2 hin

end Hex.GraphIso.Nauty.Generic
