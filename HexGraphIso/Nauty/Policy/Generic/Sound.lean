/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Generic

public section

/-!
Local proof rules for the policy recursion. Preconditions and
postconditions may refer to frozen ancestor frames as well as the
current partition. In particular, a generator return need not establish
coverage at an intermediate sweep: its postcondition can transport a
carrier to the ancestor where coverage is established.

The step rules quantify over arbitrary continuations satisfying their
contracts. They inspect one node or one target vertex, without assuming
the correctness of any recursive call. The mutual induction then proves
the contracts for the fuelled search.
-/

namespace Hex.GraphIso.Nauty.Generic

/-- Assertions at entry to and return from nodes and sweeps.
The fuel arguments distinguish exhaustion from completed coverage. -/
structure Contract (σ : Type) (n : Nat) where
  /-- Preconditions for a node call. -/
  nodePre : Nat → Bool → Nat → Nat → σ → Prop
  /-- Postconditions for a node call, including its exit. -/
  nodePost : Nat → Bool → Nat → Nat → σ → Exit × σ → Prop
  /-- Preconditions for a sweep call. -/
  sweepPre : Nat → Nat → Bool → Nat → Nat → Nat → Nat →
    Option Nat → VSet n → Nat → σ → Prop
  /-- Postconditions for a sweep call, including its exit and orbit index. -/
  sweepPost : Nat → Nat → Bool → Nat → Nat → Nat → Nat →
    Option Nat → VSet n → Nat → σ → Exit × Nat × σ → Prop

variable {n : Nat} {σ : Type} {γ : Type} [Policy σ n (γ := γ)]

/-- A continuation satisfies the node contract at its supplied fuel. -/
def Contract.nodeValid (C : Contract σ n) (fuel : Nat) (f : NodeFn σ) : Prop :=
  ∀ first level numcells st, C.nodePre fuel first level numcells st →
    C.nodePost fuel first level numcells st (f first level numcells st)

/-- A continuation satisfies the sweep contract at its supplied fuels. -/
def Contract.sweepValid (C : Contract σ n) (fuel cfuel : Nat)
    (f : SweepFn σ n) : Prop :=
  ∀ first level numcells tc tv1 cursor cell index st,
    C.sweepPre fuel cfuel first level numcells tc tv1 cursor cell index st →
    C.sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st
      (f first level numcells tc tv1 cursor cell index st)

/-- Local obligations sufficient for the contracts of every recursive call.
The step obligations use only the contracts of their continuations. -/
structure SoundPolicy (ctx : γ) (inf tcLevel : Nat) (C : Contract σ n) : Prop where
  /-- An exhausted node reports exhaustion without changing its state. -/
  node_zero : ∀ first level numcells st, C.nodePre 0 first level numcells st →
    C.nodePost 0 first level numcells st (.fuel, st)
  /-- The local node operations preserve the contract when the sweep does. -/
  node_step : ∀ fuel (next : SweepFn σ n), C.sweepValid fuel (n + 1) next →
    ∀ first level numcells st, C.nodePre (fuel + 1) first level numcells st →
      C.nodePost (fuel + 1) first level numcells st
        (nodeStep ctx tcLevel next first level numcells st)
  /-- No remaining vertex means a complete sweep, even with zero fuel. -/
  sweep_none : ∀ fuel cfuel first level numcells tc tv1 cell index st,
    C.sweepPre fuel cfuel first level numcells tc tv1 none cell index st →
    C.sweepPost fuel cfuel first level numcells tc tv1 none cell index st
      (.done, index, st)
  /-- A remaining vertex with zero fuel reports exhaustion. -/
  sweep_zero : ∀ fuel first level numcells tc tv1 tv cell index st,
    C.sweepPre fuel 0 first level numcells tc tv1 (some tv) cell index st →
    C.sweepPost fuel 0 first level numcells tc tv1 (some tv) cell index st
      (.fuel, index, st)
  /-- One vertex preserves the contract when its node and remaining sweep do. -/
  sweep_step : ∀ fuel cfuel (descend : NodeFn σ) (next : SweepFn σ n),
    C.nodeValid fuel descend → C.sweepValid fuel cfuel next →
    ∀ first level numcells tc tv1 tv cell index st,
      C.sweepPre fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st →
      C.sweepPost fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st
        (sweepStep inf descend next first level numcells tc tv1 tv cell index st)

variable {ctx : γ} {inf tcLevel : Nat} {C : Contract σ n}

mutual

/-- Local policy rules imply the postcondition of every node call. -/
theorem node_sound (h : SoundPolicy ctx inf tcLevel C)
    (first : Bool) (fuel level numcells : Nat) (st : σ)
    (hin : C.nodePre fuel first level numcells st) :
    C.nodePost fuel first level numcells st
      (node first ctx inf tcLevel fuel level numcells st) := by
  cases fuel with
  | zero =>
    rw [node]
    exact h.node_zero first level numcells st hin
  | succ fuel =>
    rw [node]
    apply h.node_step fuel _ ?_ first level numcells st hin
    intro first level numcells tc tv1 cursor cell index st hloop
    exact sweep_sound h first fuel (n + 1) level numcells tc tv1 cursor cell index st hloop
termination_by (fuel, 0, 0)

/-- Local policy rules imply the postcondition of every sweep call. -/
theorem sweep_sound (h : SoundPolicy ctx inf tcLevel C)
    (first : Bool) (fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : σ)
    (hin : C.sweepPre fuel cfuel first level numcells tc tv1 cursor cell index st) :
    C.sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st) := by
  cases cursor with
  | none =>
    rw [sweep]
    exact h.sweep_none fuel cfuel first level numcells tc tv1 cell index st hin
  | some tv =>
    cases cfuel with
    | zero =>
      rw [sweep]
      exact h.sweep_zero fuel first level numcells tc tv1 tv cell index st hin
    | succ cfuel =>
      rw [sweep]
      apply h.sweep_step fuel cfuel _ _ ?_ ?_ first level numcells tc tv1 tv cell index st hin
      · intro first level numcells st hnode
        exact node_sound h first fuel level numcells st hnode
      · intro first level numcells tc tv1 cursor cell index st hloop
        exact sweep_sound h first fuel cfuel level numcells tc tv1 cursor cell index st hloop
termination_by (fuel, 1, cfuel)

end

end Hex.GraphIso.Nauty.Generic
