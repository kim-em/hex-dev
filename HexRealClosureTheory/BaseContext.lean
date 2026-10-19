/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCodec
public import HexOrderedFnTheory.Extension
public import HexOrderedFnTheory.Infinitesimal
public import HexPolyTheory.GrindTransport

public section

-- The native and semantic dictionaries are related by the explicit `compatible`
-- equality below; stored contexts retain the native dictionary in their indices.
namespace Hex.RealClosure.BaseContext

section Native

set_option linter.overlappingInstances false

open OrderedFn OrderedFn.Oracle

variable {registry : Registry} {K : Type} [Field K] [g : Lean.Grind.Field K] [DecidableEq K]
variable {approx : K → Rat → Bounds} {baseSign : K → Int}

/-- Interpret a canonical fraction through a proved equality of the entire core
field dictionary. The transport changes no executable representative. -/
@[expose] def modelFraction (compatible : Field.toGrindField (K := K) = g)
    (f : RationalFn K) : @RationalFn K Field.toGrindField inferInstance :=
  cast (congrArg (fun F => @RationalFn K F inferInstance) compatible.symm) f

/-- Derive erased progress for the exact native dictionary and provider.
Compatibility is a companion proof; it is not a core constructor argument. -/
@[expose] def RealContext.registration (compatible : Field.toGrindField (K := K) = g)
    (parent : RealContext registry K approx baseSign) (key : ConstantKey)
    (present : (registry key).isSome = true) (h : Real.Valid (parent.source key present)) :
    Real.Registration K where
  source := parent.source key present
  signProgress f := by
    subst g
    exact (Real.registration h).signProgress f
  approxProgress f δ := by
    subst g
    exact (Real.registration h).approxProgress f δ

/-- Register a real provider in the executable dictionary, deriving its search
progress from containment, width and relative transcendence. -/
@[expose] def RealContext.register (compatible : Field.toGrindField (K := K) = g)
    (parent : RealContext registry K approx baseSign) (key : ConstantKey)
    (present : (registry key).isSome = true) (h : Real.Valid (parent.source key present)) :=
  parent.constant key present (parent.registration compatible key present h).signProgress
    (parent.registration compatible key present h).approxProgress

variable (compatible : Field.toGrindField (K := K) = g)
variable {ι : K →+* ℝ} {τ : ℝ}

/-- The real embedding of the actual canonical fraction carrier. Its source
field is the existing lawful core field interpreted through `fieldOfGrind`. -/
@[expose] noncomputable def RealModel.evalHom
    (ht : Real.RelativeTranscendence ι τ) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    RationalFn K →+* ℝ := by
  letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  exact
    { toFun := fun f => Real.evalHom ht (modelFraction compatible f)
      map_zero' := by subst g; exact (Real.evalHom ht).map_zero
      map_one' := by subst g; exact (Real.evalHom ht).map_one
      map_add' := by intro a b; subst g; exact (Real.evalHom ht).map_add a b
      map_mul' := by intro a b; subst g; exact (Real.evalHom ht).map_mul a b }

theorem RealModel.evalHom_apply (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    RealModel.evalHom compatible ht f = Real.eval ι τ (modelFraction compatible f) :=
  Real.evalHom_apply ht _

theorem RealModel.evalHom_injective (ht : Real.RelativeTranscendence ι τ) :
    Function.Injective (RealModel.evalHom compatible ht) := by
  subst g
  exact (Real.evalHom ht).injective

/-- The real order on the native canonical fraction carrier, induced by its
injective embedding. This is local to the chosen real interpretation. -/
@[instance_reducible, expose] noncomputable def RealModel.linearOrder (ht : Real.RelativeTranscendence ι τ) :
    LinearOrder (RationalFn K) :=
  LinearOrder.lift' (RealModel.evalHom compatible ht) (RealModel.evalHom_injective compatible ht)

/-- Ordered-ring laws for that same carrier and actual arithmetic. -/
theorem RealModel.strictOrderedRing (ht : Real.RelativeTranscendence ι τ) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := RealModel.linearOrder compatible ht
    IsStrictOrderedRing (RationalFn K) := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := RealModel.linearOrder compatible ht
  exact Function.Injective.isStrictOrderedRing (RealModel.evalHom compatible ht)
    (map_zero _) (map_one _) (map_add _) (map_mul _) (by intros; rfl) (by intros; rfl)

theorem RealModel.sign_evalHom (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := RealModel.linearOrder compatible ht
    sgn (RealModel.evalHom compatible ht f) = (SignType.sign f : Int) := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := RealModel.linearOrder compatible ht
  have hm : StrictMono (RealModel.evalHom compatible ht) := by intro a b hab; exact hab
  exact congrArg (fun s : SignType => (s : Int)) (hm.sign_comp f)

section InfinitesimalModel

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The Hahn-series embedding of the actual native fraction carrier. -/
@[expose] noncomputable def InfinitesimalModel.embed :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    RationalFn K →+* Lex (HahnSeries ℤ K) := by
  letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  exact
    { toFun := fun f => Infinitesimal.embed (modelFraction compatible f)
      map_zero' := by subst g; exact Infinitesimal.embed.map_zero
      map_one' := by subst g; exact Infinitesimal.embed.map_one
      map_add' := by intro a b; subst g; exact Infinitesimal.embed.map_add a b
      map_mul' := by intro a b; subst g; exact Infinitesimal.embed.map_mul a b }

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem InfinitesimalModel.embed_injective :
    Function.Injective (InfinitesimalModel.embed compatible) := by
  subst g
  exact Infinitesimal.embed_injective

@[instance_reducible, expose] noncomputable def InfinitesimalModel.linearOrder :
    LinearOrder (RationalFn K) :=
  LinearOrder.lift' (InfinitesimalModel.embed compatible)
    (InfinitesimalModel.embed_injective compatible)

theorem InfinitesimalModel.strictOrderedRing :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
    IsStrictOrderedRing (RationalFn K) := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
  exact Function.Injective.isStrictOrderedRing (InfinitesimalModel.embed compatible)
    (map_zero _) (map_one _) (map_add _) (map_mul _) (by intros; rfl) (by intros; rfl)

omit [IsStrictOrderedRing K] in
theorem InfinitesimalModel.sign_embed (f : RationalFn K) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
    (SignType.sign (InfinitesimalModel.embed compatible f) : Int) = (SignType.sign f : Int) := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
  have hm : StrictMono (InfinitesimalModel.embed compatible) := by intro a b hab; exact hab
  exact congrArg (fun s : SignType => (s : Int)) (hm.sign_comp f)

theorem InfinitesimalModel.X_pos :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
    (0 : RationalFn K) < RationalFn.X := by
  subst g
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder rfl
  change Infinitesimal.embed 0 < Infinitesimal.embed (RationalFn.X : RationalFn K)
  exact (Infinitesimal.embed_lt _ _).mp Infinitesimal.X_pos

theorem InfinitesimalModel.X_lt_C (a : K) (ha : 0 < a) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
    (RationalFn.X : RationalFn K) < RationalFn.C a := by
  subst g
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder rfl
  change Infinitesimal.embed (RationalFn.X : RationalFn K) < Infinitesimal.embed (RationalFn.C a)
  exact (Infinitesimal.embed_lt _ _).mp (Infinitesimal.X_lt_C a ha)

end InfinitesimalModel

variable (parent : RealContext registry K approx baseSign)
variable (key : ConstantKey) (present : (registry key).isSome = true)
variable (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
variable (ap : ∀ (f : RationalFn K) (δ : Rat),
  Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)

/-- Sign correctness for the actual core constructor, with any search-progress
proofs, including progress derived in another companion. -/
theorem RealContext.constant_sign
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (parent.constant key present sp ap))).sign =
      sgn (Real.eval ι τ (modelFraction compatible f)) := by
  subst g
  exact Real.sign_sound ha f (sp f)

/-- Bounds from the actual core constructor contain the transported value. -/
theorem RealContext.constant_contains
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) (δ : Rat) :
    Contains ((parent.constant key present sp ap).approx f δ)
      (Real.eval ι τ (modelFraction compatible f)) := by
  subst g
  exact Real.approx_contains ha f δ (ap f δ)

/-- The executable real sign is the order sign on its native canonical carrier. -/
theorem RealContext.constant_orderSign
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := RealModel.linearOrder compatible ht
    (⟨f⟩ : Element (.real (parent.constant key present sp ap))).sign =
      (SignType.sign f : Int) := by
  rw [RealContext.constant_sign compatible parent key present sp ap ha,
    ← RealModel.evalHom_apply compatible ht]
  exact RealModel.sign_evalHom compatible ht f

/-- Correct derived coefficient bounds are used by the next real registration. -/
theorem RealContext.source_correct
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ) (nextKey : ConstantKey)
    (nextPresent : (registry nextKey).isSome = true) (σ : ℝ)
    (hc : ∀ δ, 0 < δ → Contains ((registry nextKey).get nextPresent δ) σ) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    ApproximationCorrect (RealModel.evalHom compatible ht) σ
      ((parent.constant key present sp ap).source nextKey nextPresent) := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  constructor
  · intro f δ hδ
    rw [RealModel.evalHom_apply compatible ht]
    exact parent.constant_contains compatible key present sp ap ha f δ
  · exact hc

omit [Field K] in
theorem RealContext.source_width (nextKey : ConstantKey)
    (nextPresent : (registry nextKey).isSome = true)
    (hw : ∀ δ, 0 < δ → ((registry nextKey).get nextPresent δ).width ≤ δ) :
    ApproximationWidth ((parent.constant key present sp ap).source nextKey nextPresent) where
  coeff f δ hδ := Real.approx_width _ f δ (ap f δ) hδ
  constant := hw

include compatible in
/-- Registered-constant embeddings preserve the predecessor's sign. -/
theorem Element.embedConstant_sign
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ)
    (hs : ∀ x, baseSign x = sgn (ι x)) (a : Element (.real parent)) :
    (Element.embedConstant parent key present sp ap a).sign = a.sign := by
  subst g
  rw [RealContext.constant_sign rfl parent key present sp ap ha]
  change sgn (Real.eval ι τ (RationalFn.C a.stored)) = baseSign a.stored
  rw [← Real.evalHom_apply ht, Real.evalHom_C]
  exact (hs a.stored).symm

include compatible in
/-- Every executable ordering result is preserved by the real inclusion. -/
theorem Element.embedConstant_compare
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ)
    (hs : ∀ x, baseSign x = sgn (ι x)) (a b : Element (.real parent)) :
    (Element.embedConstant parent key present sp ap a).compare
      (Element.embedConstant parent key present sp ap b) = a.compare b := by
  unfold Element.compare
  rw [← Element.embedConstant_sub,
    Element.embedConstant_sign compatible parent key present sp ap ha ht hs]

include compatible in
/-- Relative transcendence makes the actual constructor's zero sign reflect
its unique stored zero. No field instance is installed on `Element`. -/
theorem RealContext.constant_zero
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (parent.constant key present sp ap))).sign = 0 ↔
      (⟨f⟩ : Element (.real (parent.constant key present sp ap))) = 0 := by
  subst g
  exact (Real.sign_eq_zero_iff ha ht f (sp f)).trans (Element.stored_eq_zero _)

variable (h : Real.Valid (parent.source key present))

theorem RealContext.register_sign
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (RealContext.register compatible parent key present h))).sign =
      sgn (Real.eval ι τ (modelFraction compatible f)) :=
  parent.constant_sign compatible key present _ _ ha f

theorem RealContext.register_contains
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) (δ : Rat) :
    Contains ((RealContext.register compatible parent key present h).approx f δ)
      (Real.eval ι τ (modelFraction compatible f)) :=
  parent.constant_contains compatible key present _ _ ha f δ

theorem RealContext.register_zero
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (RealContext.register compatible parent key present h))).sign = 0 ↔
      (⟨f⟩ : Element (.real (RealContext.register compatible parent key present h))) = 0 :=
  parent.constant_zero compatible key present _ _ ha ht f

section Infinitesimal

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Sign correctness for the actual infinitesimal child, using a compatible
semantic field and the predecessor's sign correspondence. -/
theorem Element.infinitesimal_sign (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int))
    (a : Element (.infinitesimal context)) :
    a.sign = (SignType.sign (Infinitesimal.embed (modelFraction compatible a.stored)) : Int) := by
  subst g
  exact Infinitesimal.sign_eq baseSign hs a.stored

/-- The child sign is the native induced order sign, so this step iterates. -/
theorem Element.infinitesimal_orderSign (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int))
    (a : Element (.infinitesimal context)) :
    letI : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
    letI : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
    a.sign = (SignType.sign a.stored : Int) := by
  rw [Element.infinitesimal_sign compatible context hs]
  exact InfinitesimalModel.sign_embed compatible a.stored

include compatible in
theorem Element.infinitesimal_pos (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int)) :
    (Element.infinitesimal context).sign = 1 := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
  rw [Element.infinitesimal_orderSign compatible context hs]
  exact congrArg (fun s : SignType => (s : Int))
    (sign_eq_one_iff.mpr (InfinitesimalModel.X_pos compatible))

include compatible in
theorem Element.infinitesimal_lt (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int))
    (a : Element context) (ha : 0 < a.stored) :
    (Element.infinitesimal context).compare a.embed = .lt := by
  let : Field (RationalFn K) := HexPolyTheory.fieldOfGrind
  let : LinearOrder (RationalFn K) := InfinitesimalModel.linearOrder compatible
  let : IsStrictOrderedRing (RationalFn K) := InfinitesimalModel.strictOrderedRing compatible
  have hn : RationalFn.X - RationalFn.C a.stored < 0 :=
    sub_neg.mpr (InfinitesimalModel.X_lt_C compatible a.stored ha)
  unfold Element.compare
  rw [Element.infinitesimal_orderSign compatible context hs]
  change (if (SignType.sign (RationalFn.X - RationalFn.C a.stored) : Int) < 0 then
    Ordering.lt else if (SignType.sign (RationalFn.X - RationalFn.C a.stored) : Int) = 0 then
      Ordering.eq else Ordering.gt) = Ordering.lt
  simp [hn]

include compatible in
theorem Element.embed_sign (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int)) (a : Element context) :
    a.embed.sign = a.sign := by
  rw [Element.infinitesimal_sign compatible context hs]
  subst g
  simp only [Element.embed, modelFraction, cast_eq, Infinitesimal.embed_C]
  change (SignType.sign (toLex (HahnSeries.single (0 : ℤ) a.stored)) : Int) = baseSign a.stored
  rw [hs]
  have hp := HahnSeries.leadingCoeff_pos_iff (x := toLex (HahnSeries.single (0 : ℤ) a.stored))
  have hn := HahnSeries.leadingCoeff_neg_iff (x := toLex (HahnSeries.single (0 : ℤ) a.stored))
  simp only [ofLex_toLex, HahnSeries.leadingCoeff_of_single] at hp hn
  simp only [sign_apply, hp, hn]

include compatible in
/-- Every executable ordering result is preserved by the infinitesimal inclusion. -/
theorem Element.embed_compare (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int)) (a b : Element context) :
    a.embed.compare b.embed = a.compare b := by
  unfold Element.compare
  rw [← Element.embed_sub, Element.embed_sign compatible context hs]

end Infinitesimal
end Native
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealContext.constant_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealContext.constant_sign
/-- info: 'Hex.RealClosure.BaseContext.RealContext.constant_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealContext.constant_zero
/-- info: 'Hex.RealClosure.BaseContext.Element.infinitesimal_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.infinitesimal_sign
/-- info: 'Hex.RealClosure.BaseContext.RealModel.evalHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealModel.evalHom_injective
/-- info: 'Hex.RealClosure.BaseContext.RealContext.source_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealContext.source_correct
/-- info: 'Hex.RealClosure.BaseContext.Element.embedConstant_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.embedConstant_compare
/-- info: 'Hex.RealClosure.BaseContext.Element.embed_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.embed_compare
/-- info: 'Hex.RealClosure.BaseContext.InfinitesimalModel.strictOrderedRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.InfinitesimalModel.strictOrderedRing
/-- info: 'Hex.RealClosure.BaseContext.Element.infinitesimal_orderSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.infinitesimal_orderSign
/-- info: 'Hex.RealClosure.BaseContext.Element.infinitesimal_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.infinitesimal_lt
