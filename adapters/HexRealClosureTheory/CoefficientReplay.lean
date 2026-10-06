/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientMoment
public import HexSignDet.Table

public section

namespace Hex.SignDet.Node
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u}

/-- Substitute a node's actual coefficient data, retaining its literal integer
system, rank certificate, row positions and query values. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (n : Node F Ctx) : Node G Ctx := by
  classical
  exact {
    context := n.context
    head := interpretation.polynomial n.head
    lower := n.lower.substitute interpretation
    upper := n.upper.substitute interpretation
    queries := n.queries.map (fun p => interpretation.polynomial p)
    size := n.size
    system := n.system
    moments := n.moments.map (TarskiCertificate.substitute interpretation)
    reductions := n.reductions.map (fun r => r.map (Reduction.substitute interpretation))
    preparation := n.preparation.map (QueryReduction.substitute interpretation)
    basis := n.basis }

/-- Finite guards for every literal moment row and optional shared preprocessing. -/
@[expose] noncomputable def coefficients (n : Node F Ctx)
    (p : DensePoly F) (a b : Endpoint F)
    (qs : List (DensePoly F)) : Finset F := by
  classical
  exact (n.preparation.toList.flatMap (fun r => (r.coefficients p qs).toList)).toFinset ∪
    ((List.finRange n.size).flatMap (fun i =>
      (momentCoefficients p a b (QueryReduction.operands qs n.preparation)
        n.system.rows[i] n.moments[i] n.reductions[i]).toList)).toFinset

private theorem map_entry {α : Type v} {β : Type w} {m : Nat}
    (f : α → β) (xs : Vector α m) (i : Fin m) : (xs.map f)[i] = f xs[i] := by
  simpa only [Fin.getElem_fin] using (_root_.Vector.getElem_map (xs := xs) f i.isLt)

/-- Preserve every local node clause: bindings, integer matrix evidence,
shared query reductions and complete moment replays. -/
theorem check_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx) (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F))
    (n : Node F Ctx)
    (data : ∀ x ∈ n.coefficients p a b qs,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : n.check sign context p a b qs = true) :
    (n.substitute interpretation).check targetSign context
      (interpretation.polynomial p) (a.substitute interpretation) (b.substitute interpretation)
      (qs.map (fun q => interpretation.polynomial q)) = true := by
  classical
  rcases n with ⟨nc, np, na, nb, nqs, ns, sys, certs, reds, pre, basis⟩
  let n : Node F Ctx := ⟨nc, np, na, nb, nqs, ns, sys, certs, reds, pre, basis⟩
  change n.check sign context p a b qs = true at accepted
  change ∀ x ∈ n.coefficients p a b qs,
    x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
    targetSign (interpretation.map x) = sign x at data
  change (n.substitute interpretation).check targetSign context
    (interpretation.polynomial p) (a.substitute interpretation) (b.substitute interpretation)
    (qs.map (fun q => interpretation.polynomial q)) = true
  simp only [check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  rw [check_eq]
  dsimp (config := { instances := true }) only [substitute]
  simp only [Bool.and_eq_true, and_assoc]
  obtain ⟨hctx, hp, ha, hb, hqs, system, rank, cols, checked, inverse, prep, moments⟩ := accepted
  refine ⟨?_, ?_, ?_, ?_, checked, ?_, ?_, ?_⟩
  · exact decide_eq_true (by simp only [hctx, hp, ha, hb, hqs, and_self])
  · simpa only [List.length_map] using system
  · exact decide_eq_true rank
  · exact decide_eq_true cols
  · exact decide_eq_true inverse
  · cases h : n.preparation with
    | none => rfl
    | some r =>
      simp only [h] at prep
      apply r.check_map interpretation sign targetSign p qs _ prep
      intro x hx
      exact data x (Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, by simp [h], Finset.mem_toList.mpr hx⟩)))
  · apply List.all_eq_true.mpr
    intro i hi
    rw (config := { transparency := .all }) [map_entry, map_entry]
    rw [QueryReduction.operands_map]
    apply checkMoment_map interpretation sign targetSign context p a b
      (QueryReduction.operands qs n.preparation) n.system.rows[i] n.system.values[i]
      n.moments[i] n.reductions[i] _ (List.all_eq_true.mp moments i hi)
    intro x hx
    exact data x (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨i, hi, Finset.mem_toList.mpr hx⟩)))

end Hex.SignDet.Node

namespace Hex.SignDet.Replay
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u}

/-- Substitute every supplied node without changing the literal tree. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G) :
    Replay F Ctx → Replay G Ctx
  | .leaf n => .leaf (n.substitute interpretation)
  | .split n l r => .split (n.substitute interpretation)
      (l.substitute interpretation) (r.substitute interpretation)

/-- Actual root-node data after substitution. -/
theorem node_map (interpretation : RealClosure.CoefficientMap F G)
    (r : Replay F Ctx) :
    (r.substitute interpretation).node = r.node.substitute interpretation := by
  cases r <;> rfl

/-- One finite inventory follows the actual child query slices. -/
@[expose] noncomputable def coefficients (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F)) :
    Replay F Ctx → Finset F
  | .leaf n => n.coefficients p a b qs
  | .split n l r => n.coefficients p a b qs ∪
      coefficients p a b (qs.take (qs.length / 2)) l ∪
      coefficients p a b (qs.drop (qs.length / 2)) r

/-- Preserve the entire accepted recursive BKR tree, its exact query slices
and every literal integer-system witness. -/
theorem check_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx) (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F))
    (r : Replay F Ctx)
    (data : ∀ x ∈ r.coefficients p a b qs,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : r.check sign context p a b qs = true) :
    (r.substitute interpretation).check targetSign context
      (interpretation.polynomial p) (a.substitute interpretation) (b.substitute interpretation)
      (qs.map (fun q => interpretation.polynomial q)) = true := by
  classical
  induction r generalizing qs with
  | leaf n =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [substitute, check, List.length_map, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact ⟨accepted.1, accepted.2.1, accepted.2.2.1,
      n.check_map interpretation sign targetSign context p a b qs data accepted.2.2.2⟩
  | split n l r ihl ihr =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [substitute, check, List.length_map, ← List.map_take, ← List.map_drop,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    refine ⟨accepted.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact ihl _ (fun x hx => data x (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
        accepted.2.1
    · exact ihr _ (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2.2.1
    · rw [node_map, node_map]
      exact accepted.2.2.2.1
    · rw [node_map, node_map]
      exact accepted.2.2.2.2.1
    · exact n.check_map interpretation sign targetSign context p a b qs
        (fun x hx => data x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))) accepted.2.2.2.2.2

/-- Specialization retains every extracted table row literally. -/
theorem table_rows_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx) (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F))
    (r : Replay F Ctx)
    (data : ∀ x ∈ r.coefficients p a b qs,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : r.check sign context p a b qs = true) :
    ((r.substitute interpretation).table
      (r.check_map interpretation sign targetSign context p a b qs data accepted)).rows =
      (r.table accepted).rows := by
  rw [table_rows, table_rows, node_map]
  rfl

/-- Every sparse lookup, including omitted sign conditions, is retained. -/
theorem table_count_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx) (p : DensePoly F)
    (a b : Endpoint F) (qs : List (DensePoly F))
    (r : Replay F Ctx)
    (data : ∀ x ∈ r.coefficients p a b qs,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : r.check sign context p a b qs = true) (condition : List Int) :
    ((r.substitute interpretation).table
      (r.check_map interpretation sign targetSign context p a b qs data accepted)).count condition =
      (r.table accepted).count condition := by
  rw [table_lookup, table_lookup, node_map]
  rfl

end Hex.SignDet.Replay

namespace Hex.SignDet.Replay

/-- A single positive first-parameter neighborhood preserves the supplied
recursive BKR replay, its literal integer evidence and every query slice. -/
theorem firstMap_near {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p : DensePoly (RationalFn (RationalFn ℝ)))
    (a b : Endpoint (RationalFn (RationalFn ℝ)))
    (qs : List (DensePoly (RationalFn (RationalFn ℝ))))
    (replay : Replay (RationalFn (RationalFn ℝ)) Ctx)
    (accepted : replay.check
      (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign))
      context p a b qs = true) :
    ∀ᶠ first in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (replay.substitute (RealClosure.Specialize.firstMap first)).check
        (OrderedFn.Infinitesimal.sign OrderedFn.orderSign) context
        ((RealClosure.Specialize.firstMap first).polynomial p)
        (a.substitute (RealClosure.Specialize.firstMap first))
        (b.substitute (RealClosure.Specialize.firstMap first))
        (qs.map (fun q => (RealClosure.Specialize.firstMap first).polynomial q)) = true := by
  filter_upwards [RealClosure.Specialize.firstMap_near (replay.coefficients p a b qs)] with first data
  exact replay.check_map (RealClosure.Specialize.firstMap first) _ _ context p a b qs data accepted

/-- info: 'Hex.SignDet.Replay.firstMap_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.firstMap_near

end Hex.SignDet.Replay
