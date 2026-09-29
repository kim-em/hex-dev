/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportReplay
public import HexSignDetMathlib.RootModel

public section

namespace Hex.RealClosure.Transport

open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} {C : Type w}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable [DecidableEq C]

/-- Distinct target roots realizing the entire ordered sign condition after
interpreting the source coefficient arrays. -/
noncomputable def roots (read : E → K) (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) (condition : List Int) : Finset K :=
  (Tarski.rootsIn (interpret (fun x : K => x) (fun _ => Iff.rfl) (polynomial read p))
    ((endpoint read a).map (fun x : K => x)) ((endpoint read b).map (fun x : K => x))).filter
    (fun x => signsAt (fun x : K => x) (fun _ => Iff.rfl) (qs.map (polynomial read)) x = condition)

/-- Finite interpretation data turns the original accepted table's sparse
lookup into an exact root cardinality, including omitted conditions. -/
theorem count_roots (read : E → K) (S : E → Prop) (closed : Closed read S)
    (sourceSign : E → Int) (context : C) (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) (t : Replay E C)
    (data : ReplayData read S sourceSign (fun x : K => (SignType.sign x : Int)) p a b qs t)
    (accepted : t.check sourceSign context p a b qs = true) (condition : List Int) :
    (t.table accepted).count condition = (roots read p a b qs condition).card := by
  classical
  have checked := replay_check read S closed (fun x : C => x) sourceSign
    (fun x : K => (SignType.sign x : Int)) context p a b qs t data accepted
  have counted := (replay read (fun x : C => x) t).count_roots (fun x : K => x)
    (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun x : K => (SignType.sign x : Int)) (fun _ => rfl) context
    (polynomial read p) (endpoint read a) (endpoint read b)
    (qs.map (polynomial read)) checked condition
  rw [Replay.table_lookup]
  rw [replay_node] at counted
  exact counted

/-- A positive source count supplies a target root realizing all signs
together under the supplied finite interpretation data. -/
theorem exists_root (read : E → K) (S : E → Prop) (closed : Closed read S)
    (sourceSign : E → Int) (context : C) (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) (t : Replay E C)
    (data : ReplayData read S sourceSign (fun x : K => (SignType.sign x : Int)) p a b qs t)
    (accepted : t.check sourceSign context p a b qs = true) (condition : List Int)
    (positive : 0 < (t.table accepted).count condition) :
    ∃ x, x ∈ roots read p a b qs condition := by
  classical
  exact Finset.card_pos.mp (lt_of_lt_of_eq positive
    (count_roots read S closed sourceSign context p a b qs t data accepted condition))

/-- An accepted count-one condition identifies exactly one target root.
This consumes a coefficient interpretation; it does not construct one. -/
theorem unique_root (read : E → K) (S : E → Prop) (closed : Closed read S)
    (sourceSign : E → Int) (context : C) (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) (t : Replay E C)
    (data : ReplayData read S sourceSign (fun x : K => (SignType.sign x : Int)) p a b qs t)
    (accepted : t.check sourceSign context p a b qs = true) (condition : List Int)
    (one : (t.table accepted).count condition = 1) :
    ∃! x, x ∈ roots read p a b qs condition := by
  classical
  have cardinal := (count_roots read S closed sourceSign context p a b qs t data accepted condition).symm.trans one
  obtain ⟨x, singleton⟩ := Finset.card_eq_one.mp cardinal
  refine ⟨x, ?_, ?_⟩
  · rw [singleton]
    exact Finset.mem_singleton_self x
  · intro y member
    rw [singleton] at member
    exact Finset.mem_singleton.mp member

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.count_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.count_roots
/-- info: 'Hex.RealClosure.Transport.exists_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.exists_root
/-- info: 'Hex.RealClosure.Transport.unique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.unique_root
