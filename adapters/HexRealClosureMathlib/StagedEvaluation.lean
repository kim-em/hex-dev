/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientComposition
public import HexRealClosureMathlib.CoefficientEmbedding
public import HexRealClosureMathlib.BaseOrder

public section

namespace Hex.RealClosure.CoefficientMap

/-- Specialize a native rational-function stage without changing its field
dictionary. The new interpretation retains every old domain coefficient,
including those mapped to zero, as well as the finite requested signs. -/
theorem native_parameter {F : Type} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (native : Lean.Grind.Field F) (compatible : Field.toGrindField (K := F) = native)
    (first : CoefficientMap F ℝ)
    (values : List (@RationalFn F native inferInstance))
    (data : ∀ a ∈ @nativeCoefficients F native inferInstance values,
      a ∈ first.domain ∧ (SignType.sign (first.map a) : Int) = (SignType.sign a : Int)) :
    letI : Field (@RationalFn F native inferInstance) :=
      @HexPolyMathlib.fieldOfGrind _ (@RationalFn.instField F native inferInstance)
    ∃ interpretation : CoefficientMap (@RationalFn F native inferInstance) ℝ,
      (∀ q ∈ values, q ∈ interpretation.domain ∧
        (SignType.sign (interpretation.map q) : Int) =
          @OrderedFn.Infinitesimal.sign F native inferInstance OrderedFn.orderSign q) ∧
      (∀ a : F, a ∈ first.domain →
        @RationalFn.C F native inferInstance a ∈ interpretation.domain ∧
          interpretation.map (@RationalFn.C F native inferInstance a) = first.map a) := by
  cases compatible
  obtain ⟨t, positive, below, stable⟩ :=
    exists_signs_parameter first values data 1 zero_lt_one
  exact ⟨first.parameterMap t, stable, first.parameterMap_C t⟩

end Hex.RealClosure.CoefficientMap

namespace Hex.RealClosure.BaseContext

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {sign : K → Int} {chain : Chain registry K sign}

/-- A finite family in any actual provider-derived staged base has a partial
ordinary-real interpretation preserving its native signs and every coefficient
inherited from the caller's real prefix. Successive infinitesimals are
specialized in predecessor order after collecting the next finite inventory. -/
theorem Chain.Realization.exists_interpretation (following : chain.Realization registry) :
    ∀ values : List K,
      letI : Field K := HexPolyMathlib.fieldOfGrind
      ∃ interpretation : CoefficientMap K ℝ,
        (∀ a ∈ values, a ∈ interpretation.domain ∧
          (SignType.sign (interpretation.map a) : Int) = sign a) ∧
        (∀ a r, following.RealValue a r →
          a ∈ interpretation.domain ∧ interpretation.map a = r) := by
  induction following with
  | @real B field equality approx sign parent model previous =>
    intro values
    letI : Field B := HexPolyMathlib.fieldOfGrind
    refine ⟨CoefficientMap.ofHom model.hom, ?_, ?_⟩
    · intro a member
      refine ⟨CoefficientMap.ofHom_domain model.hom a, ?_⟩
      rw [CoefficientMap.ofHom_map]
      exact (model.sign a).symm
    · intro a r real
      change model.hom a = r at real
      exact ⟨CoefficientMap.ofHom_domain model.hom a,
        (CoefficientMap.ofHom_map model.hom a).trans real⟩
  | @infinitesimal B field equality sign parent previous ih =>
    intro values
    letI : Field B := HexPolyMathlib.fieldOfGrind
    let original := previous.ordered
    letI : LinearOrder B := original.order
    letI : IsStrictOrderedRing B := original.ordered
    obtain ⟨first, data, real⟩ := ih (CoefficientMap.nativeCoefficients values)
    have converted : ∀ a ∈ CoefficientMap.nativeCoefficients values,
        a ∈ first.domain ∧ (SignType.sign (first.map a) : Int) = (SignType.sign a : Int) := by
      intro a member
      exact ⟨(data a member).1, (data a member).2.trans (original.sign a)⟩
    obtain ⟨second, stable, constants⟩ := CoefficientMap.native_parameter field
      (HexPolyMathlib.toGrind_fieldOfGrind (s := field)) first values converted
    refine ⟨second, ?_, ?_⟩
    · intro a member
      refine ⟨(stable a member).1, ?_⟩
      have signs : Hex.OrderedFn.orderSign = sign := by
        funext a
        exact (Hex.OrderedFn.Infinitesimal.orderSign_eq a).trans (original.sign a).symm
      exact (stable a member).2.trans
        (congrArg (fun f => @Hex.OrderedFn.Infinitesimal.sign B field equality f a) signs)
    · intro a r inherited
      change ∃ b, a = RationalFn.C b ∧ previous.RealValue b r at inherited
      obtain ⟨b, rfl, inherited⟩ := inherited
      have old := real b r inherited
      exact ⟨(constants b old.1).1, (constants b old.1).2.trans old.2⟩

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.exists_interpretation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.exists_interpretation
