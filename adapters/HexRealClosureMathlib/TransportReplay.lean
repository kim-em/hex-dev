/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportMoment
public import HexSignDet.Replay

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} {C : Type w} {D : Type z}
variable [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Interpret literal node coefficients and context while retaining its complete
integer system, moment positions and rank certificate. -/
@[expose] def node (read : E → K) (contextMap : C → D) (n : Hex.SignDet.Node E C) :
    Hex.SignDet.Node K D :=
  { context := contextMap n.context
    head := polynomial read n.head
    lower := endpoint read n.lower
    upper := endpoint read n.upper
    queries := n.queries.map (polynomial read)
    size := n.size
    system := n.system
    moments := n.moments.map (query read contextMap)
    reductions := n.reductions.map (Option.map (reduction read))
    preparation := n.preparation.map (preparation read)
    basis := n.basis }

/-- Retained independent rows keep the native rank witness's original order. -/
theorem node_rows (read : E → K) (contextMap : C → D) (n : Hex.SignDet.Node E C) :
    (node read contextMap n).rows = n.rows := rfl

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]

/-- Finite obligations of the node's actual shared preprocessing and indexed
moments. The retained integer system and rank witness need no interpretation. -/
structure NodeData (read : E → K) (S : E → Prop) (sourceSign : E → Int) (targetSign : K → Int)
    (p : Hex.DensePoly E) (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E))
    (n : Hex.SignDet.Node E C) : Prop where
  head : Leading read p
  members : ∀ q ∈ Hex.SignDet.QueryReduction.operands qs n.preparation,
    ∀ i < q.size, S (q.coeff i)
  preparation : ∀ r, n.preparation = some r → PreparationData read sourceSign targetSign p qs r.steps
  reductions : ∀ i : Fin n.size, ∀ r, n.reductions[i] = some r →
    ReductionData read sourceSign targetSign p 1
      (Hex.SignDet.factors (Hex.SignDet.QueryReduction.operands qs n.preparation) n.system.rows[i])
      r.steps r.result
  moments : ∀ i : Fin n.size, QueryData read sourceSign targetSign p
    (Hex.SignDet.queryPoly (Hex.SignDet.QueryReduction.operands qs n.preparation)
      n.system.rows[i] n.reductions[i]) a b n.moments[i]

/-- Full node replay transports every literal binding, preprocessing step and
moment, retaining the native rank and left-inverse checks on the same integers. -/
theorem node_check [DecidableEq C] [DecidableEq D]
    (read : E → K) (S : E → Prop) (closed : Closed read S) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (p : Hex.DensePoly E) (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E))
    (n : Hex.SignDet.Node E C) (data : NodeData read S sourceSign targetSign p a b qs n)
    (accepted : n.check sourceSign context p a b qs = true) :
    (node read contextMap n).check targetSign (contextMap context) (polynomial read p)
      (endpoint read a) (endpoint read b) (qs.map (polynomial read)) = true := by
  simp only [Hex.SignDet.Node.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  simp only [Hex.SignDet.Node.check_eq, node, List.length_map, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]
  rcases accepted with ⟨contextEq, headEq, lowerEq, upperEq, queriesEq,
    system, rank, columns, matrix, inverse, prepared, moments⟩
  refine ⟨congrArg contextMap contextEq, congrArg (polynomial read) headEq,
    congrArg (endpoint read) lowerEq, congrArg (endpoint read) upperEq,
    congrArg (List.map (polynomial read)) queriesEq, system, rank, columns, matrix, inverse, ?_, ?_⟩
  · cases h : n.preparation with
    | none => rfl
    | some r =>
      have checked : r.check sourceSign p qs = true := by simpa only [h] using prepared
      exact preparation_check read closed.read_zero closed.read_one sourceSign targetSign p qs r
        data.head (data.preparation r h) checked
  · rw [List.all_eq_true] at moments ⊢
    intro i member
    have checked := moment_check read S closed contextMap sourceSign targetSign context p a b
      (Hex.SignDet.QueryReduction.operands qs n.preparation) n.system.rows[i] n.system.values[i]
      n.moments[i] n.reductions[i] data.members (data.reductions i) (data.moments i) (moments i member)
    simpa only [preparation_operands, Fin.getElem_fin, Vector.getElem_map] using checked

/-- Interpret every supplied node, retaining the finite tree's actual shape. -/
@[expose] def replay (read : E → K) (contextMap : C → D) :
    Hex.SignDet.Replay E C → Hex.SignDet.Replay K D
  | .leaf n => .leaf (node read contextMap n)
  | .split n l r => .split (node read contextMap n)
      (replay read contextMap l) (replay read contextMap r)

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] in
/-- The mapped tree's root is the mapped original root node. -/
theorem replay_node (read : E → K) (contextMap : C → D) (t : Hex.SignDet.Replay E C) :
    (replay read contextMap t).node = node read contextMap t.node := by
  cases t <;> rfl

/-- Each recursion edge uses the checker's original positional query slice. -/
@[expose] def ReplayData (read : E → K) (S : E → Prop) (sourceSign : E → Int)
    (targetSign : K → Int) (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) : Hex.SignDet.Replay E C → Prop
  | .leaf n => NodeData read S sourceSign targetSign p a b qs n
  | .split n l r => NodeData read S sourceSign targetSign p a b qs n ∧
      ReplayData read S sourceSign targetSign p a b (qs.take (qs.length / 2)) l ∧
      ReplayData read S sourceSign targetSign p a b (qs.drop (qs.length / 2)) r

/-- Complete recursive BKR replay transports both child checks, exact product
supports and retained rows, every node's integer evidence, and all moments. -/
theorem replay_check [DecidableEq C] [DecidableEq D]
    (read : E → K) (S : E → Prop) (closed : Closed read S) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (p : Hex.DensePoly E) (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E))
    (t : Hex.SignDet.Replay E C) (data : ReplayData read S sourceSign targetSign p a b qs t)
    (accepted : t.check sourceSign context p a b qs = true) :
    (replay read contextMap t).check targetSign (contextMap context) (polynomial read p)
      (endpoint read a) (endpoint read b) (qs.map (polynomial read)) = true := by
  induction t generalizing qs with
  | leaf n =>
    simp only [Hex.SignDet.Replay.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [replay, Hex.SignDet.Replay.check, node, List.length_map,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact ⟨accepted.1, accepted.2.1, accepted.2.2.1,
      node_check read S closed contextMap sourceSign targetSign context p a b qs n data accepted.2.2.2⟩
  | split n l r ihl ihr =>
    simp only [Hex.SignDet.Replay.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [replay, Hex.SignDet.Replay.check, replay_node, node, List.length_map,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    refine ⟨accepted.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.map_take] using ihl _ data.2.1 accepted.2.1
    · simpa only [List.map_drop] using ihr _ data.2.2 accepted.2.2.1
    · rw [replay_node, replay_node]
      exact accepted.2.2.2.1
    · exact accepted.2.2.2.2.1
    · exact node_check read S closed contextMap sourceSign targetSign context p a b qs n
        data.1 accepted.2.2.2.2.2

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.node_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.node_rows
/-- info: 'Hex.RealClosure.Transport.node_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.node_check
/-- info: 'Hex.RealClosure.Transport.replay_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.replay_node
/-- info: 'Hex.RealClosure.Transport.replay_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.replay_check
