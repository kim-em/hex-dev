/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientSelected

public section

namespace Hex.RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField
variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- A field homomorphism is an interpretation on the entire coefficient field. -/
noncomputable def ofHom (hom : F →+* G) : CoefficientMap F G where
  domain := ⊤
  value := hom.comp (⊤ : Subring F).subtype

theorem ofHom_map (hom : F →+* G) (a : F) : (ofHom hom).map a = hom a := by
  rw [map_mem _ _ (by trivial)]
  rfl

end Hex.RealClosure.CoefficientMap

namespace Hex.RealClosure.Specialize
open scoped Hex.OrderedFn.Infinitesimal
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]

private theorem inner_orderSign (q : Hex.RationalFn F) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q = Hex.OrderedFn.orderSign q := by
  rw [Hex.OrderedFn.Infinitesimal.orderSign_eq]
  rcases lt_trichotomy q 0 with negative | rfl | positive
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_neg negative]
    simp [negative]
  · simp
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_pos positive]
    simp [positive]

/-- Embedding actual coefficients preserves the successive-infinitesimal sign. -/
theorem nestedHom_sign (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (f : Hex.RationalFn (Hex.RationalFn F)) :
    Hex.OrderedFn.Infinitesimal.sign (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
        (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding) f) =
      Hex.OrderedFn.Infinitesimal.sign (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f := by
  have source : (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign : Hex.RationalFn F → Int) =
      Hex.OrderedFn.orderSign := funext inner_orderSign
  have target : (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign : Hex.RationalFn ℝ → Int) =
      Hex.OrderedFn.orderSign := funext inner_orderSign
  rw [source, target]
  exact Hex.OrderedFn.Infinitesimal.mapHom_sign (HexRationalFnMathlib.mapHom embedding)
    (Hex.OrderedFn.Infinitesimal.mapHom_strictMono embedding ordered) f

/-- An executable ordered coefficient field, in particular the rational field,
can supply the exact checked descriptor and signs used by joint realization.
The coefficient embedding transfers the literal evidence before specialization. -/
theorem nested_embedding {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}
    (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
      (Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
    (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
    (s : Hex.SignDet.SelectedSigns d qs) :
    let interpretation := CoefficientMap.ofHom
      (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding))
    ∃ target : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn ℝ)) Ctx
        (Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context,
      target.raw = d.raw.substitute interpretation ∧
      target.evidence = d.evidence.substitute interpretation ∧
      ∃ signs : Hex.SignDet.SelectedSigns target (qs.map interpretation.polynomial),
        signs.values.toList = s.values.toList := by
  classical
  let interpretation := CoefficientMap.ofHom
    (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding))
  have data : ∀ f ∈ s.coefficients,
      f ∈ interpretation.domain ∧ (interpretation.map f = 0 ↔ f = 0) ∧
      Hex.OrderedFn.Infinitesimal.sign (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
          (interpretation.map f) =
        Hex.OrderedFn.Infinitesimal.sign (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f := by
    intro f _
    refine ⟨by trivial, ?_, ?_⟩
    · rw [CoefficientMap.ofHom_map]
      exact (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding)).map_eq_zero_iff
    · rw [CoefficientMap.ofHom_map]
      exact nestedHom_sign embedding ordered f
  let target := d.substitute interpretation (fun x hx => data x (Finset.mem_union_left _ hx))
  exact ⟨target, Hex.SignDet.Descriptor.map_raw _ _ _, Hex.SignDet.Descriptor.map_evidence _ _ _,
    s.substitute interpretation data, Hex.SignDet.SelectedSigns.substitute_values _ _ _⟩

/-- info: 'Hex.RealClosure.Specialize.nested_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_embedding

end Hex.RealClosure.Specialize

namespace Hex.RealClosure.Specialize.Native

open Hex.SignDet

variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}

/-- Transport the whole nested descriptor, query list and selected replay
through equality of the native base-field dictionary. -/
def nestedEvidence (g : Lean.Grind.Field F) (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
      (Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context) →
    (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F)))) →
    Hex.SignDet.SelectedSigns d qs →
    letI : Lean.Grind.Field F := Field.toGrindField
    Σ d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
      (Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context,
      Σ qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))),
        Hex.SignDet.SelectedSigns d qs := by
  cases compatible
  exact fun d qs s => ⟨d, qs, s⟩

omit [IsStrictOrderedRing F] in
/-- Transport retains the entire original descriptor, including raw data and replay. -/
theorem nestedEvidence_descriptor (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
        (Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
      (s : Hex.SignDet.SelectedSigns d qs),
      letI : Lean.Grind.Field F := Field.toGrindField
      HEq (nestedEvidence g compatible d qs s).1 d := by
  cases compatible
  intros
  rfl

omit [IsStrictOrderedRing F] in
/-- Transport retains the original ordered query polynomials. -/
theorem nestedEvidence_queries (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
        (Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
      (s : Hex.SignDet.SelectedSigns d qs),
      letI : Lean.Grind.Field F := Field.toGrindField
      HEq (nestedEvidence g compatible d qs s).2.1 qs := by
  cases compatible
  intros
  rfl

omit [IsStrictOrderedRing F] in
/-- Transport retains the actual checked selected-sign certificate. -/
theorem nestedEvidence_selected (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
        (Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
      (s : Hex.SignDet.SelectedSigns d qs),
      letI : Lean.Grind.Field F := Field.toGrindField
      HEq (nestedEvidence g compatible d qs s).2.2 s := by
  cases compatible
  intros
  rfl

omit [IsStrictOrderedRing F] in
/-- Dictionary transport retains every recorded integer sign. -/
theorem nestedEvidence_values (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ (d : Hex.SignDet.Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
        (Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
      (s : Hex.SignDet.SelectedSigns d qs),
      let values := s.values.toList
      letI : Lean.Grind.Field F := Field.toGrindField
      (nestedEvidence g compatible d qs s).2.2.values.toList = values := by
  cases compatible
  intros
  rfl

/-- Transport a finite native coefficient set to the compatible Mathlib
coefficient dictionary. -/
def nestedFractions (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    Finset (Hex.RationalFn (Hex.RationalFn F)) →
    letI : Lean.Grind.Field F := Field.toGrindField
    Finset (Hex.RationalFn (Hex.RationalFn F)) := by
  cases compatible
  exact id

/-- Native finite coefficient transport retains the entire original set. -/
theorem nestedFractions_heq (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ fractions : Finset (Hex.RationalFn (Hex.RationalFn F)),
      HEq (nestedFractions g compatible fractions) fractions := by
  cases compatible
  intro fractions
  rfl

/-- One ordinary real point realizes the actual native nested checked
descriptor, recorded selected signs and requested source coefficient signs. -/
theorem nested_selected (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g)
    (embedding : F →+* ℝ) (ordered : StrictMono embedding) :
    letI : Lean.Grind.Field F := g
    letI : Lean.Grind.Field (Hex.RationalFn F) := Hex.RationalFn.instField
    letI : Lean.Grind.Field (Hex.RationalFn (Hex.RationalFn F)) := Hex.RationalFn.instField
    ∀ (d : Descriptor (Hex.RationalFn (Hex.RationalFn F)) Ctx
      (Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))))
      (s : SelectedSigns d qs) (fractions : Finset (Hex.RationalFn (Hex.RationalFn F)))
      (cap : ℝ), 0 < cap →
    let values := s.values.toList
    let sourceSign := Hex.OrderedFn.Infinitesimal.sign
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
    let sourceSigns := fractions.toList.map sourceSign
    let headSigns := fun i => sourceSign (d.raw.head.coeff i)
    let querySigns := qs.map fun q => fun i => sourceSign (q.coeff i)
    letI : Lean.Grind.Field F := Field.toGrindField
    let data := nestedEvidence g compatible d qs s
    let requested := nestedFractions g compatible fractions
    let interpretation := CoefficientMap.ofHom
      (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding))
    ∃ first : ℝ, 0 < first ∧ first < cap ∧ ∃ second : ℝ, 0 < second ∧ second < first ∧
      ∃ target : Descriptor ℝ Ctx (fun r : ℝ => (SignType.sign r : Int)) context,
        target.raw = ((data.1.raw.substitute interpretation).substitute (firstMap first)).specialize
          (RingHom.id ℝ) second ∧
        target.evidence = ((data.1.evidence.substitute interpretation).substitute
          (firstMap first)).specialize (RingHom.id ℝ) second ∧
        Descriptor.ofReplay? (fun r : ℝ => (SignType.sign r : Int)) context
          (((data.1.raw.substitute interpretation).substitute (firstMap first)).specialize
            (RingHom.id ℝ) second)
          (((data.1.evidence.substitute interpretation).substitute (firstMap first)).specialize
            (RingHom.id ℝ) second) = some target ∧
        signsAt (fun r : ℝ => r) (fun _ => Iff.rfl)
          ((data.2.1.map interpretation.polynomial).map
            (fun q => polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second))
          (target.root (fun r : ℝ => r) (fun _ => Iff.rfl) rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ => rfl) (fun _ => rfl)) = values ∧
        (∀ i, target.raw.head.coeff i =
          evalNestedFraction ((data.1.raw.substitute interpretation).head.coeff i) first second) ∧
        (∀ q ∈ data.2.1.map interpretation.polynomial, ∀ i,
          (polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second).coeff i =
            evalNestedFraction (q.coeff i) first second) ∧
        (∀ f ∈ requested,
          (SignType.sign (evalNestedFraction (interpretation.map f) first second) : Int) =
            Hex.OrderedFn.Infinitesimal.sign
              (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
          (evalNestedFraction (interpretation.map f) first second = 0 ↔ f = 0)) ∧
        requested.toList.map (fun f =>
          (SignType.sign (evalNestedFraction (interpretation.map f) first second) : Int)) = sourceSigns ∧
        (∀ i, (SignType.sign (target.raw.head.coeff i) : Int) = headSigns i) ∧
        List.Forall₂ (fun expected q => ∀ i, (SignType.sign (q.coeff i) : Int) = expected i)
          querySigns ((data.2.1.map interpretation.polynomial).map
            (fun q => polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second)) := by
  cases compatible
  intro d qs s fractions cap positive
  dsimp only [nestedEvidence, nestedFractions]
  classical
  let interpretation := CoefficientMap.ofHom
    (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding))
  obtain ⟨embedded, raw, evidence, signs, values⟩ := nested_embedding embedding ordered d qs s
  let inventory := d.raw.head.toArray.toList ++ qs.flatMap (fun q => q.toArray.toList)
  let family := fractions ∪ inventory.toFinset ∪ {0}
  have inFamily (p : Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F)))
      (member : p = d.raw.head ∨ p ∈ qs) (i : Nat) : p.coeff i ∈ family := by
    by_cases stored : i < p.size
    · have inArray := RealClosure.CoefficientMap.coefficient_mem p i stored
      have inInventory : p.coeff i ∈ inventory := by
        rcases member with rfl | member
        · exact List.mem_append_left _ inArray
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, member, inArray⟩)
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr inInventory))
    · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt stored)]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  obtain ⟨first, firstPositive, below, second, secondPositive, smaller, target,
    targetRaw, targetEvidence, targetChecked, observed, head, queries, coefficients⟩ :=
    exists_nested_selected embedded _ signs (family.image interpretation.map) cap positive
  have preserved (f : Hex.RationalFn (Hex.RationalFn F)) (member : f ∈ family) :
      (SignType.sign (evalNestedFraction (interpretation.map f) first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (evalNestedFraction (interpretation.map f) first second = 0 ↔ f = 0) := by
    have facts := coefficients (interpretation.map f) (Finset.mem_image_of_mem _ member)
    refine ⟨facts.2.2.1.trans ?_, facts.2.2.2.trans ?_⟩
    · rw [CoefficientMap.ofHom_map]
      exact nestedHom_sign embedding ordered f
    · rw [CoefficientMap.ofHom_map]
      exact (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom embedding)).map_eq_zero_iff
  refine ⟨first, firstPositive, below, second, secondPositive, smaller, target,
    raw ▸ targetRaw, evidence ▸ targetEvidence, ?_, observed.trans values,
    raw ▸ head, queries,
    (fun f member => preserved f (Finset.mem_union_left _ (Finset.mem_union_left _ member))),
    ?_, ?_, ?_⟩
  · simpa only [raw, evidence] using targetChecked
  · apply List.map_congr_left
    intro f member
    exact (preserved f (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_toList.mp member)))).1
  · intro i
    have equation := head i
    rw [raw] at equation
    change target.raw.head.coeff i =
      evalNestedFraction (interpretation.polynomial d.raw.head |>.coeff i) first second at equation
    rw [equation, RealClosure.CoefficientMap.polynomial_coeff]
    exact (preserved _ (inFamily _ (Or.inl rfl) i)).1
  · have each : ∀ q ∈ qs, ∀ i,
        (SignType.sign ((polynomial (RingHom.id ℝ)
          ((firstMap first).polynomial (interpretation.polynomial q)) second).coeff i) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) (q.coeff i) := by
      intro q member i
      rw [queries _ (List.mem_map.mpr ⟨q, member, rfl⟩) i,
        RealClosure.CoefficientMap.polynomial_coeff]
      exact (preserved _ (inFamily _ (Or.inr member) i)).1
    have assembled : ∀ polynomials : List (Hex.DensePoly (Hex.RationalFn (Hex.RationalFn F))),
        (∀ q ∈ polynomials, ∀ i,
          (SignType.sign ((polynomial (RingHom.id ℝ)
            ((firstMap first).polynomial (interpretation.polynomial q)) second).coeff i) : Int) =
            Hex.OrderedFn.Infinitesimal.sign
              (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) (q.coeff i)) →
        List.Forall₂ (fun expected q => ∀ i, (SignType.sign (q.coeff i) : Int) = expected i)
          (polynomials.map fun q => fun i => Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) (q.coeff i))
          ((polynomials.map interpretation.polynomial).map
            (fun q => polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second)) := by
      intro polynomials
      induction polynomials with
      | nil => intro _; exact .nil
      | cons q rest ih =>
        intro facts
        exact .cons (facts q (by simp)) (ih (fun r member => facts r (by simp [member])))
    exact assembled qs each

end Hex.RealClosure.Specialize.Native

/-- info: 'Hex.RealClosure.Specialize.Native.nested_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.Native.nested_selected
