/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientDescriptor
public import HexRealClosureMathlib.SpecializeDescriptor

public section

namespace Hex.SignDet.SelectedSigns
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]
variable {Ctx : Type u} [DecidableEq Ctx] {sign : F → Int} {targetSign : G → Int} {context : Ctx}
variable {d : Descriptor F Ctx sign context} {qs : List (DensePoly F)}

/-- The literal descriptor and selected-sign replay inventories. -/
@[expose] noncomputable def coefficients (s : SelectedSigns d qs) : Finset F :=
  d.raw.coefficients d.evidence ∪
    s.evidence.coefficients d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs)

/-- Check the same selected-sign evidence after coefficient interpretation.
The integer values are retained in order; the target descriptor comes from
checking the actual substituted descriptor evidence. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (s : SelectedSigns d qs)
    (data : ∀ x ∈ s.coefficients,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    SelectedSigns (d.substitute interpretation
      (fun x hx => data x (Finset.mem_union_left _ hx)))
      (qs.map interpretation.polynomial) := by
  classical
  let values : Vector Int (qs.map interpretation.polynomial).length :=
    ⟨s.values.toArray, by simp⟩
  refine ⟨values, s.evidence.substitute interpretation, ?_⟩
  have original := s.accepted
  simp only [Descriptor.checkSigns, RawDescriptor.checkSigns, Bool.and_eq_true,
    decide_eq_true_eq] at original ⊢
  have head_data i (hi : i < d.raw.head.size) := data (d.raw.head.coeff i)
    (Finset.mem_union_left _ (Finset.mem_union_left _
      (List.mem_toFinset.mpr (coefficient_mem _ i hi))))
  have member := fun i hi => (head_data i hi).1
  have reflects := fun i hi => (head_data i hi).2.1
  rw [Descriptor.map_raw]
  refine ⟨⟨⟨(RawDescriptor.wellFormed_map interpretation d.raw reflects).trans
    original.1.1.1, original.1.1.2⟩, ?_⟩, ?_⟩
  · rw [RawDescriptor.queries_map interpretation d.raw member reflects, ← List.map_append]
    exact s.evidence.check_map interpretation sign targetSign context d.raw.head d.raw.lower
      d.raw.upper (d.raw.queries ++ qs)
      (fun x hx => data x (Finset.mem_union_right _ hx)) original.1.2
  · rw [RawDescriptor.queries_map interpretation d.raw member reflects, List.length_map,
      Replay.node_map]
    exact original.2

/-- Substitution retains every supplied sign code literally. -/
theorem substitute_values (interpretation : RealClosure.CoefficientMap F G)
    (s : SelectedSigns d qs)
    (data : ∀ x ∈ s.coefficients,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x) :
    (s.substitute interpretation data).values.toList = s.values.toList := rfl

/-- info: 'Hex.SignDet.SelectedSigns.substitute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.SelectedSigns.substitute

end Hex.SignDet.SelectedSigns

namespace Hex.RealClosure.Specialize
open Filter Topology Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret
attribute [local instance 2000] Field.toGrindField
variable {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}

/-- A selected root over two successive infinitesimals and an additional finite
coefficient family have one ordinary real realization. Both positive parameters
and the real selected root satisfy the requested conditions together. The real
descriptor and signs come from checking the supplied evidence at both stages. -/
theorem exists_nested_selected
    (d : Descriptor (Hex.RationalFn (Hex.RationalFn ℝ)) Ctx
      (Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
    (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn ℝ))))
    (s : SelectedSigns d qs)
    (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧ ∃ second : ℝ, 0 < second ∧ second < first ∧
      ∃ target : Descriptor ℝ Ctx (fun x : ℝ => (SignType.sign x : Int)) context,
        target.raw = (d.raw.substitute (firstMap first)).specialize (RingHom.id ℝ) second ∧
        target.evidence = (d.evidence.substitute (firstMap first)).specialize (RingHom.id ℝ) second ∧
        Descriptor.ofReplay? (fun x : ℝ => (SignType.sign x : Int)) context
          ((d.raw.substitute (firstMap first)).specialize (RingHom.id ℝ) second)
          ((d.evidence.substitute (firstMap first)).specialize (RingHom.id ℝ) second) = some target ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second))
          (target.root (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ => rfl) (fun _ => rfl)) = s.values.toList ∧
        (∀ i, target.raw.head.coeff i = evalNestedFraction (d.raw.head.coeff i) first second) ∧
        (∀ q ∈ qs, ∀ i,
          (polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second).coeff i =
            evalNestedFraction (q.coeff i) first second) ∧
        ∀ f ∈ fractions,
          (firstMap first).map f = mapFraction f first ∧
          evalMapped (RingHom.id ℝ) ((firstMap first).map f) second =
            evalNestedFraction f first second ∧
          (SignType.sign (evalNestedFraction f first second) : Int) =
            Hex.OrderedFn.Infinitesimal.sign
              (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
          (evalNestedFraction f first second = 0 ↔ f = 0) := by
  classical
  let family : Finset (Hex.RationalFn (Hex.RationalFn ℝ)) :=
    fractions ∪ d.raw.head.toArray.toList.toFinset ∪
      (qs.flatMap (fun q => q.toArray.toList)).toFinset ∪ {0}
  have inFamily (p : Hex.DensePoly (Hex.RationalFn (Hex.RationalFn ℝ)))
      (selected : p = d.raw.head ∨ p ∈ qs) (i : Nat) : p.coeff i ∈ family := by
    by_cases stored : i < p.size
    · have entry := RealClosure.CoefficientMap.coefficient_mem p i stored
      rcases selected with rfl | present
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (List.mem_toFinset.mpr entry)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨p, present, entry⟩)))
    · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt stored)]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have belowCap : ∀ᶠ first in 𝓝[>] (0 : ℝ), first < cap :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds positive)
  have firstPositive : ∀ᶠ first in 𝓝[>] (0 : ℝ), 0 < first := self_mem_nhdsWithin
  obtain ⟨first, ⟨⟨⟨data, ordinary⟩, below⟩, hfirst⟩⟩ :=
    ((((firstMap_near s.coefficients).and (nested_fractions_near family)).and belowCap).and
      firstPositive).exists
  let firstDescriptor : Descriptor (Hex.RationalFn ℝ) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context :=
    d.substitute (firstMap first) (fun x hx => data x (Finset.mem_union_left _ hx))
  let firstSigns : SelectedSigns firstDescriptor (qs.map (firstMap first).polynomial) :=
    s.substitute (firstMap first) data
  obtain ⟨η, hη, selected⟩ := selected_root_near (RingHom.id ℝ)
    (fun _ _ h => h) firstDescriptor (qs.map (firstMap first).polynomial) firstSigns
  have secondSmall : ∀ᶠ second in 𝓝[>] (0 : ℝ), second < first :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hfirst)
  have selectedSmall : ∀ᶠ second in 𝓝[>] (0 : ℝ), second < η :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hη)
  have secondPositive : ∀ᶠ second in 𝓝[>] (0 : ℝ), 0 < second := self_mem_nhdsWithin
  obtain ⟨second, ⟨⟨⟨conditions, belowFirst⟩, small⟩, hsecond⟩⟩ :=
    (((ordinary.2.and secondSmall).and selectedSmall).and secondPositive).exists
  obtain ⟨target, raw, evidence, checked, signs⟩ := selected second hsecond small
  have evaluated f (hf : f ∈ family) :
      (firstMap first).map f = mapFraction f first ∧
        evalMapped (RingHom.id ℝ) ((firstMap first).map f) second =
          evalNestedFraction f first second := by
    have interpreted := firstMap_value f first (ordinary.1 f hf).1 (ordinary.1 f hf).2
    refine ⟨interpreted.2, ?_⟩
    rw [interpreted.2]
    exact mapFraction_eval f first second (ordinary.1 f hf).2 (conditions f hf).1
  have head : target.raw = (d.raw.substitute (firstMap first)).specialize (RingHom.id ℝ) second := by
    simpa only [firstDescriptor, Descriptor.map_raw] using raw
  refine ⟨first, hfirst, below, second, hsecond, belowFirst, target, head, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [firstDescriptor, Descriptor.map_evidence] using evidence
  · simpa only [firstDescriptor, Descriptor.map_raw, Descriptor.map_evidence] using checked
  · simpa only [firstSigns, SelectedSigns.substitute_values, List.map_map, Function.comp_def] using signs
  · intro i
    rw [head]
    change (polynomial (RingHom.id ℝ) ((firstMap first).polynomial d.raw.head) second).coeff i = _
    rw [polynomial_coeff, RealClosure.CoefficientMap.polynomial_coeff]
    exact (evaluated _ (inFamily _ (Or.inl rfl) i)).2
  · intro q hq i
    rw [polynomial_coeff, RealClosure.CoefficientMap.polynomial_coeff]
    exact (evaluated _ (inFamily _ (Or.inr hq) i)).2
  · intro f hf
    have member : f ∈ family := Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ hf))
    exact ⟨(evaluated f member).1, (evaluated f member).2, (conditions f member).2⟩

/-- info: 'Hex.RealClosure.Specialize.exists_nested_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_nested_selected

end Hex.RealClosure.Specialize
