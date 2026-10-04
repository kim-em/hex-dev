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

end Hex.RealClosure.Specialize.Native
