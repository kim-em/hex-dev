/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeMoment
public import HexSignDet.Table

public section

namespace Hex.SignDet.Node
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u}

/-- Substitute a node's actual coefficient data, retaining its literal integer
system, rank certificate, row positions and query values. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (n : Node (RationalFn F) Ctx) : Node ℝ Ctx := by
  classical
  exact {
    context := n.context
    head := polynomial embedding n.head t
    lower := n.lower.specialize embedding t
    upper := n.upper.specialize embedding t
    queries := n.queries.map (fun p => polynomial embedding p t)
    size := n.size
    system := n.system
    moments := n.moments.map (TarskiCertificate.specialize embedding t)
    reductions := n.reductions.map (fun r => r.map (Reduction.specialize embedding t))
    preparation := n.preparation.map (QueryReduction.specialize embedding t)
    basis := n.basis }

/-- Finite guards for every literal moment row and optional shared preprocessing. -/
@[expose] noncomputable def fractions (n : Node (RationalFn F) Ctx)
    (p : DensePoly (RationalFn F)) (a b : Endpoint (RationalFn F))
    (qs : List (DensePoly (RationalFn F))) : Finset (RationalFn F) := by
  classical
  exact (n.preparation.toList.flatMap (fun r => (r.fractions p qs).toList)).toFinset ∪
    ((List.finRange n.size).flatMap (fun i =>
      (momentFractions p a b (QueryReduction.operands qs n.preparation)
        n.system.rows[i] n.moments[i] n.reductions[i]).toList)).toFinset

private theorem map_entry {α : Type v} {β : Type w} {m : Nat}
    (f : α → β) (xs : Vector α m) (i : Fin m) : (xs.map f)[i] = f xs[i] := by
  simpa only [Fin.getElem_fin] using (_root_.Vector.getElem_map (xs := xs) f i.isLt)

/-- Preserve every local node clause: bindings, integer matrix evidence,
shared query reductions and complete moment replays. -/
theorem check_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (n : Node (RationalFn F) Ctx)
    (data : ∀ x ∈ n.fractions p a b qs,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : n.check sign context p a b qs = true) :
    (n.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
      (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
      (qs.map (fun q => polynomial embedding q t)) = true := by
  classical
  rcases n with ⟨nc, np, na, nb, nqs, ns, sys, certs, reds, pre, basis⟩
  let n : Node (RationalFn F) Ctx := ⟨nc, np, na, nb, nqs, ns, sys, certs, reds, pre, basis⟩
  change n.check sign context p a b qs = true at accepted
  change ∀ x ∈ n.fractions p a b qs,
    Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
    (SignType.sign (evalMapped embedding x t) : Int) = sign x at data
  change (n.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
    (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
    (qs.map (fun q => polynomial embedding q t)) = true
  simp only [check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  rw [check_eq]
  dsimp (config := { instances := true }) only [specialize]
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
      apply r.check_specialize embedding t sign p qs _ prep
      intro x hx
      exact data x (Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, by simp [h], Finset.mem_toList.mpr hx⟩)))
  · apply List.all_eq_true.mpr
    intro i hi
    rw (config := { transparency := .all }) [map_entry, map_entry]
    rw [QueryReduction.operands_specialize]
    apply checkMoment_specialize embedding t sign context p a b
      (QueryReduction.operands qs n.preparation) n.system.rows[i] n.system.values[i]
      n.moments[i] n.reductions[i] _ (List.all_eq_true.mp moments i hi)
    intro x hx
    exact data x (Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨i, hi, Finset.mem_toList.mpr hx⟩)))

end Hex.SignDet.Node

namespace Hex.SignDet.Replay
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u}

/-- Substitute every supplied node without changing the literal tree. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ) :
    Replay (RationalFn F) Ctx → Replay ℝ Ctx
  | .leaf n => .leaf (n.specialize embedding t)
  | .split n l r => .split (n.specialize embedding t)
      (l.specialize embedding t) (r.specialize embedding t)

/-- Actual root-node data after substitution. -/
theorem node_specialize (embedding : F →+* ℝ) (t : ℝ)
    (r : Replay (RationalFn F) Ctx) :
    (r.specialize embedding t).node = r.node.specialize embedding t := by
  cases r <;> rfl

/-- One finite inventory follows the actual child query slices. -/
@[expose] noncomputable def fractions (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F))) :
    Replay (RationalFn F) Ctx → Finset (RationalFn F)
  | .leaf n => n.fractions p a b qs
  | .split n l r => n.fractions p a b qs ∪
      fractions p a b (qs.take (qs.length / 2)) l ∪
      fractions p a b (qs.drop (qs.length / 2)) r

/-- Preserve the entire accepted recursive BKR tree, its exact query slices
and every literal integer-system witness. -/
theorem check_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : Replay (RationalFn F) Ctx)
    (data : ∀ x ∈ r.fractions p a b qs,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : r.check sign context p a b qs = true) :
    (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
      (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
      (qs.map (fun q => polynomial embedding q t)) = true := by
  classical
  induction r generalizing qs with
  | leaf n =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [specialize, check, List.length_map, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact ⟨accepted.1, accepted.2.1, accepted.2.2.1,
      n.check_specialize embedding t sign context p a b qs data accepted.2.2.2⟩
  | split n l r ihl ihr =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
    simp only [specialize, check, List.length_map, ← List.map_take, ← List.map_drop,
      Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    refine ⟨accepted.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact ihl _ (fun x hx => data x (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
        accepted.2.1
    · exact ihr _ (fun x hx => data x (Finset.mem_union_right _ hx)) accepted.2.2.1
    · rw [node_specialize, node_specialize]
      exact accepted.2.2.2.1
    · rw [node_specialize, node_specialize]
      exact accepted.2.2.2.2.1
    · exact n.check_specialize embedding t sign context p a b qs
        (fun x hx => data x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))) accepted.2.2.2.2.2

/-- Specialization retains every extracted table row literally. -/
theorem table_rows_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : Replay (RationalFn F) Ctx)
    (data : ∀ x ∈ r.fractions p a b qs,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : r.check sign context p a b qs = true) :
    ((r.specialize embedding t).table
      (r.check_specialize embedding t sign context p a b qs data accepted)).rows =
      (r.table accepted).rows := by
  rw [table_rows, table_rows, node_specialize]
  rfl

/-- Every sparse lookup, including omitted sign conditions, is retained. -/
theorem table_count_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : Replay (RationalFn F) Ctx)
    (data : ∀ x ∈ r.fractions p a b qs,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : r.check sign context p a b qs = true) (condition : List Int) :
    ((r.specialize embedding t).table
      (r.check_specialize embedding t sign context p a b qs data accepted)).count condition =
      (r.table accepted).count condition := by
  rw [table_lookup, table_lookup, node_specialize]
  rfl

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One positive neighborhood preserves all nodes of the complete accepted
BKR tree together, retaining all its table rows and counts. -/
theorem specialize_near [DecidableEq Ctx] (embedding : F →+* ℝ)
    (ordered : StrictMono embedding) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : Replay (RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
        (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
        (qs.map (fun q => polynomial embedding q t)) = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (r.fractions p a b qs)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ context p a b qs r _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- All real parameters in one positive neighborhood have an accepted replay
with exactly the original sparse table counts, for every sign condition. -/
theorem table_near [DecidableEq Ctx] (embedding : F →+* ℝ)
    (ordered : StrictMono embedding) (context : Ctx) (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F)) (qs : List (DensePoly (RationalFn F)))
    (r : Replay (RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      ∃ checked : (r.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
        (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
        (qs.map (fun q => polynomial embedding q t)) = true,
        ∀ condition, ((r.specialize embedding t).table checked).count condition =
          (r.table accepted).count condition := by
  obtain ⟨η, positive, preserved⟩ := specialize_near embedding ordered context p a b qs r accepted
  refine ⟨η, positive, fun t ht small => ⟨preserved t ht small, fun condition => ?_⟩⟩
  rw [table_lookup, table_lookup, node_specialize]
  rfl

/-- info: 'Hex.SignDet.Node.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Node.check_specialize

/-- info: 'Hex.SignDet.Replay.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.check_specialize

/-- info: 'Hex.SignDet.Replay.table_count_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.table_count_specialize

/-- info: 'Hex.SignDet.Replay.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.specialize_near

/-- info: 'Hex.SignDet.Replay.table_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.table_near

end Hex.SignDet.Replay
