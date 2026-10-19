/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientReplay
public import HexSignDetTheory.SelectedRoot

public section

namespace Hex.RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

private theorem regular_derivative (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F)
    (regular : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    ∀ i, (p.derivative.coeff i) ∈ interpretation.domain := by
  classical
  obtain ⟨P, lift⟩ := polynomial_lift interpretation p regular
  have derivative : P.derivative.map (interpretation.domain).subtype =
      HexPolyTheory.toPolynomial p.derivative := by
    rw [← Polynomial.derivative_map, lift, HexPolyTheory.toPolynomial_derivative]
  intro i
  have coefficient := congrArg (fun q => q.coeff i) derivative
  simp only [Polynomial.coeff_map, HexPolyTheory.coeff_toPolynomial] at coefficient
  change (P.derivative.coeff i).val = p.derivative.coeff i at coefficient
  rw [← coefficient]
  exact (P.derivative.coeff i).property

/-- The actual derivative sequence maps from the original coefficient
guards alone. Iterated derivatives stay in the regular coefficient ring. -/
theorem derivativesFrom_map (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F) (n : Nat)
    (regular : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain) :
    (Hex.SignDet.derivativesFrom p n).map (fun q => interpretation.polynomial q) =
      Hex.SignDet.derivativesFrom (interpretation.polynomial p) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [Hex.SignDet.derivativesFrom, List.map_cons]
    apply congrArg₂ List.cons (polynomial_derivative interpretation p regular)
    rw [ih p.derivative (fun i _ => regular_derivative interpretation p regular i),
      polynomial_derivative interpretation p regular]

/-- Preserving the head's finite zero pattern also preserves the derivative
sequence length selected by its actual degree. -/
theorem derivatives_map (interpretation : RealClosure.CoefficientMap F G)
    (p : Hex.DensePoly F)
    (regular : ∀ i < p.size, (p.coeff i) ∈ interpretation.domain)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (Hex.SignDet.derivatives p).map (fun q => interpretation.polynomial q) =
      Hex.SignDet.derivatives (interpretation.polynomial p) := by
  rw [Hex.SignDet.derivatives, Hex.SignDet.derivatives, polynomial_degree interpretation p reflects]
  exact derivativesFrom_map interpretation p p.natDegree regular

end Hex.RealClosure.CoefficientMap

namespace Hex.SignDet.RawDescriptor
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u}

/-- Substitute the stored head and endpoints, retaining context, derivative
indices and signs. Queries are recomputed from the mapped head. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (raw : RawDescriptor F Ctx) : RawDescriptor G Ctx := by
  classical
  exact {
    context := raw.context
    head := interpretation.polynomial raw.head
    lower := raw.lower.substitute interpretation
    upper := raw.upper.substitute interpretation
    indices := raw.indices
    signs := raw.signs }

/-- Literal derivative indices and sign guards remain well formed when the
head's actual degree is preserved. -/
theorem wellFormed_map (interpretation : RealClosure.CoefficientMap F G)
    (raw : RawDescriptor F Ctx)
    (reflects : ∀ i < raw.head.size,
      interpretation.map (raw.head.coeff i) = 0 ↔ raw.head.coeff i = 0) :
    (raw.substitute interpretation).wellFormed = raw.wellFormed := by
  classical
  simp only [wellFormed, substitute, polynomial_degree interpretation raw.head reflects]
  rfl

/-- Recomputed formal derivative queries equal substitution of the original
ordered query list, including default zero reads at malformed indices. -/
theorem queries_map (interpretation : RealClosure.CoefficientMap F G)
    (raw : RawDescriptor F Ctx)
    (regular : ∀ i < raw.head.size, (raw.head.coeff i) ∈ interpretation.domain)
    (reflects : ∀ i < raw.head.size,
      interpretation.map (raw.head.coeff i) = 0 ↔ raw.head.coeff i = 0) :
    (raw.substitute interpretation).queries =
      raw.queries.map (fun q => interpretation.polynomial q) := by
  classical
  simp only [queries, substitute, List.map_map]
  rw [← derivatives_map interpretation raw.head regular reflects]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.getElem?_map]
  cases h : (derivatives raw.head)[i - 1]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ((polynomial_zero interpretation (0 : DensePoly F) (by simp)).mpr rfl).symm
  | some q => simp only [Option.map_some, Option.getD_some]

/-- Finite descriptor data include the head's coefficient array as well as
the full replay inventory for its actual reconstructed derivative queries. -/
@[expose] noncomputable def coefficients (raw : RawDescriptor F Ctx)
    (evidence : Replay F Ctx) : Finset F := by
  classical
  exact raw.head.toArray.toList.toFinset ∪
    evidence.coefficients raw.head raw.lower raw.upper raw.queries

/-- The complete descriptor checker remains accepted with queries rebuilt
from the mapped head and the same literal count-one replay. -/
theorem check_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx)
    (raw : RawDescriptor F Ctx) (evidence : Replay F Ctx)
    (data : ∀ x ∈ raw.coefficients evidence,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : raw.check sign context evidence = true) :
    (raw.substitute interpretation).check targetSign context
      (evidence.substitute interpretation) = true := by
  classical
  have head_data (i : Nat) (hi : i < raw.head.size) :=
    data (raw.head.coeff i) (Finset.mem_union_left _
      (List.mem_toFinset.mpr (coefficient_mem raw.head i hi)))
  have regular := fun i hi => (head_data i hi).1
  have reflects := fun i hi => (head_data i hi).2.1
  obtain ⟨wellFormed, bound, replay, one⟩ := check_eq accepted
  have checked : (evidence.substitute interpretation).check targetSign
      context (raw.substitute interpretation).head (raw.substitute interpretation).lower
      (raw.substitute interpretation).upper (raw.substitute interpretation).queries = true := by
    rw [queries_map interpretation raw regular reflects]
    exact evidence.check_map interpretation sign targetSign context raw.head raw.lower raw.upper raw.queries
      (fun x hx => data x (Finset.mem_union_right _ hx)) replay
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨(wellFormed_map interpretation raw reflects).trans wellFormed, bound⟩, checked⟩, ?_⟩
  rw [Replay.node_map]
  change evidence.node.system.count raw.signs = 1
  exact (evidence.table_lookup replay raw.signs).symm.trans one

end Hex.SignDet.RawDescriptor

namespace Hex.SignDet.Descriptor
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u} [DecidableEq Ctx]
variable {sign : F → Int} {targetSign : G → Int} {context : Ctx}

/-- Reuse the mapped count-one evidence to construct a checked target
descriptor whose derivative queries come from its actual new head. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (d : Descriptor F Ctx sign context)
    (data : ∀ x ∈ d.raw.coefficients d.evidence,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    Descriptor G Ctx targetSign context := by
  classical
  have accepted := d.raw.check_map interpretation sign targetSign context d.evidence data d.accepted
  simp only [RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ofTable (d.raw.substitute interpretation) (d.evidence.substitute interpretation)
    accepted.1.1.1 accepted.1.1.2 accepted.1.2
    (((d.evidence.substitute interpretation).table_lookup accepted.1.2
      (d.raw.substitute interpretation).signs).trans accepted.2)

/-- The validated result retains the literal mapped raw descriptor. -/
theorem map_raw (interpretation : RealClosure.CoefficientMap F G)
    (d : Descriptor F Ctx sign context)
    (data : ∀ x ∈ d.raw.coefficients d.evidence,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    (d.substitute interpretation data).raw = d.raw.substitute interpretation := by
  simp only [substitute, ofTable_raw]

/-- Checking the exact mapped raw input and replay returns this descriptor.
This uses the constructor's public equation across the module boundary. -/
theorem map_checked (interpretation : RealClosure.CoefficientMap F G)
    (d : Descriptor F Ctx sign context)
    (data : ∀ x ∈ d.raw.coefficients d.evidence,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    ofReplay? targetSign context
      (d.raw.substitute interpretation) (d.evidence.substitute interpretation) =
      some (d.substitute interpretation data) := by
  simp only [substitute]
  apply ofReplay_ofTable

/-- The validated descriptor retains the entire literal mapped replay. -/
theorem map_evidence (interpretation : RealClosure.CoefficientMap F G)
    (d : Descriptor F Ctx sign context)
    (data : ∀ x ∈ d.raw.coefficients d.evidence,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    (d.substitute interpretation data).evidence = d.evidence.substitute interpretation := by
  have accepted := d.raw.check_map interpretation sign targetSign context d.evidence data d.accepted
  have fields := ofReplay_data targetSign context
    (d.raw.substitute interpretation) (d.evidence.substitute interpretation)
  rw [map_checked interpretation d data, Option.map_some, ite_eq_left accepted] at fields
  exact (Prod.mk.inj (Option.some.inj fields)).2

end Hex.SignDet.Descriptor


namespace Hex.SignDet.RawDescriptor

/-- The actual first-parameter neighborhood preserves checking a selected-root
raw descriptor against its literal replay and recomputed derivative queries. -/
theorem firstMap_near {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (raw : RawDescriptor (RationalFn (RationalFn ℝ)) Ctx)
    (replay : Replay (RationalFn (RationalFn ℝ)) Ctx)
    (accepted : raw.check
      (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign))
      context replay = true) :
    ∀ᶠ first in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (raw.substitute (RealClosure.Specialize.firstMap first)).check
        (OrderedFn.Infinitesimal.sign OrderedFn.orderSign) context
        (replay.substitute (RealClosure.Specialize.firstMap first)) = true := by
  filter_upwards [RealClosure.Specialize.firstMap_near (raw.coefficients replay)] with first data
  exact raw.check_map (RealClosure.Specialize.firstMap first) _ _ context replay data accepted

/-- info: 'Hex.SignDet.RawDescriptor.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.check_map

/-- info: 'Hex.SignDet.RawDescriptor.firstMap_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.firstMap_near

end Hex.SignDet.RawDescriptor
