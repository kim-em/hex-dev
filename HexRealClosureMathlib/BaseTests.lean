/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseContext
public import HexRealClosureMathlib.BaseProvider
public import HexRealClosureMathlib.BaseStagedRealization
public import HexRealClosure.BaseInclusion
public meta import HexRealClosure.BaseInclusion
public import HexRealClosure.LiveContext
public meta import HexRealClosure.LiveContext
public import HexRealClosure.AlgebraicContext
public import HexRealClosure.BasePolynomial
public import HexRealClosure.BaseCatalog
public import HexOrderedFnMathlib.LiouvilleTests
public meta import HexRealClosure.BaseCodec
public meta import HexRealClosure.BasePolynomial
public meta import HexRealClosure.BaseCatalog
public meta import HexOrderedFnMathlib.LiouvilleTests

public section

namespace Hex.RealClosure.BaseContext.RealTests

open OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private def key (version : Nat) : ConstantKey := ⟨"liouville", version⟩
private def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private abbrev prefixContext := RealContext.rational registry

private theorem present (version : Nat) : (registry (key version)).isSome = true := by
  simp [registry, key]

private noncomputable abbrev rationalModel := RealPrefix.Model.rational registry

private theorem providerTranscendence :
    letI : Field rationalModel.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rationalModel.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact OrderedFn.LiouvilleTests.transcendence

private theorem providerContained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry (key 1)).get (present 1) δ) (liouvilleNumber 2) :=
  OrderedFn.LiouvilleTests.provider_contains δ

private theorem providerWidth (δ : Rat) (positive : 0 < δ) :
    ((registry (key 1)).get (present 1) δ).width ≤ δ :=
  OrderedFn.LiouvilleTests.provider_width δ positive

/-- This constructs the full native prefix and its coherent predecessor model
using only the actual Liouville provider's analytic premises. -/
private noncomputable def providerModel := rationalModel.register (key 1) (present 1)
  (liouvilleNumber 2) providerContained providerWidth providerTranscendence

example : providerModel.context.keys = [key 1] := by
  exact (RealPrefix.Model.register_keys rationalModel (key 1) (present 1) (liouvilleNumber 2)
    providerContained providerWidth providerTranscendence).trans (by
      simp only [rationalModel, RealPrefix.Model.rational, RealPrefix.Model.context,
        RealPrefix.keys, RealContext.keys, RealContext.ofChain_chain, RealChain.keys,
        List.nil_append])

private theorem cast_source (F G : Lean.Grind.Field Rat) (h : F = G)
    (he : @Real.Registration Rat F inferInstance = @Real.Registration Rat G inferInstance)
    (r : @Real.Registration Rat F inferInstance) :
    @Real.Registration.source Rat G inferInstance
      (cast he r) =
      @Real.Registration.source Rat F inferInstance r := by
  cases h
  rfl

private theorem source_eq (version : Nat) :
    prefixContext.source (key version) (present version) =
      OrderedFn.LiouvilleCoreTests.registered.source := by
  simp only [OrderedFn.LiouvilleCoreTests.registered,
    cast_source _ _ HexRationalFnMathlib.ratField_eq]
  rfl

private theorem signProgress (version : Nat) (f : RationalFn Rat) :
    Acc (Next (Real.attempt (prefixContext.source (key version) (present version)) f)) 0 := by
  rw [source_eq]
  exact OrderedFn.LiouvilleCoreTests.registered.signProgress f

private theorem approxProgress (version : Nat) (f : RationalFn Rat) (δ : Rat) :
    Acc (Next (Real.approxAttempt (prefixContext.source (key version) (present version))
      f (Real.requestWidth δ))) 0 := by
  rw [source_eq]
  exact OrderedFn.LiouvilleCoreTests.registered.approxProgress f δ

private abbrev realContext (version : Nat) := Context.real
  (prefixContext.constant (key version) (present version)
    (signProgress version) (approxProgress version))

private def positive : Element (realContext 1) := ⟨OrderedFn.LiouvilleCoreTests.positive.val⟩
private abbrev mixed := (realContext 1).infinitesimal
private def epsilon : Element mixed := Element.infinitesimal (realContext 1)

/-- The complete stage order supports a selected algebraic root whose
coefficient uses both a registered real constant and an infinitesimal. -/
private def stagedRoot : Option (Array Int) := do
  let coefficient : Element mixed := positive.embed + epsilon + 2
  let y : DensePoly (Element mixed) := DensePoly.ofCoeffs #[0, 1]
  let p := y * y - DensePoly.C coefficient
  let d ← SignDet.Descriptor.validate Element.sign mixed.signature
    { context := mixed.signature, head := p, lower := .finite 1,
      upper := .finite 2, indices := [], signs := [] }
  let context := mixed.adjoin d
  let root := Algebraic.Element.ofPoly (context := context) y
  let target := Algebraic.Element.ofCoeff (context := context) coefficient
  return #[root.sign, (root * root - target).sign, (root - 1).sign,
    (root - 2).sign, (root⁻¹).sign, (root * root⁻¹ - 1).sign]

#guard stagedRoot == some #[1, 0, 1, -1, 1, 0]

/-- Gathering rebuilds an algebraic dependency over a proper real-prefix
enlargement while retaining the old infinitesimal and its defining equation. -/
private def gatheredPrefix : Option (Array Int) := do
  let original := Tower.Context.base (BaseContext.rational registry).infinitesimal
  let e : original.Value := Element.infinitesimal (BaseContext.rational registry)
  let x : DensePoly original.Value := DensePoly.ofCoeffs #[0, 1]
  let descriptor ← SignDet.Descriptor.validate original.sign original.signature
    { context := original.signature, head := x * x - DensePoly.C (2 + e),
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let child := original.adjoin descriptor
  let target := Tower.Context.base mixed.infinitesimal
  match Tower.Shared.gather? (.pack mixed.infinitesimal) [child.context, target] with
  | none => none
  | some shared =>
    if shared.input.context.signature.roots.length != 1 then none else
    let root := shared.value 0 child.generator
    let retained := shared.value 0 (child.embed e)
    let expected : target.Value := epsilon.embed
    let next : target.Value := Element.infinitesimal mixed
    some #[shared.input.context.sign root,
      shared.input.context.sign (root * root - (2 + retained)),
      shared.input.context.sign (retained - shared.value 1 expected),
      shared.input.context.sign (shared.value 1 next - retained),
      shared.input.context.sign retained]

#guard gatheredPrefix == some #[1, 0, 0, -1, 1]

private theorem source_correct (version : Nat) :
    ApproximationCorrect (Rat.castHom ℝ) (liouvilleNumber 2)
      (prefixContext.source (key version) (present version)) := by
  change ApproximationCorrect (Rat.castHom ℝ) (liouvilleNumber 2)
    OrderedFn.LiouvilleTests.source
  exact OrderedFn.LiouvilleTests.source_correct

example (f : RationalFn Rat) :
    (⟨f⟩ : Element (realContext 1)).sign =
      sgn (Real.eval (Rat.castHom ℝ) (liouvilleNumber 2)
        (modelFraction HexRationalFnMathlib.ratField_eq f)) :=
  prefixContext.constant_sign HexRationalFnMathlib.ratField_eq (key 1) (present 1)
    (signProgress 1) (approxProgress 1) (source_correct 1) f

example (f : RationalFn Rat) :
    (⟨f⟩ : Element (realContext 1)).sign = 0 ↔ (⟨f⟩ : Element (realContext 1)) = 0 :=
  prefixContext.constant_zero HexRationalFnMathlib.ratField_eq (key 1) (present 1)
    (signProgress 1) (approxProgress 1) (source_correct 1)
    OrderedFn.LiouvilleTests.transcendence f

example (f : RationalFn Rat) (δ : Rat) :
    Contains ((prefixContext.constant (key 1) (present 1)
      (signProgress 1) (approxProgress 1)).approx f δ)
      (Real.eval (Rat.castHom ℝ) (liouvilleNumber 2)
        (modelFraction HexRationalFnMathlib.ratField_eq f)) :=
  prefixContext.constant_contains HexRationalFnMathlib.ratField_eq (key 1) (present 1)
    (signProgress 1) (approxProgress 1) (source_correct 1) f δ

private theorem valid (version : Nat) : Real.Valid
    (prefixContext.source (key version) (present version)) :=
  ⟨Rat.castHom ℝ, liouvilleNumber 2, source_correct version,
    OrderedFn.LiouvilleTests.source_width, OrderedFn.LiouvilleTests.transcendence⟩

private abbrev derived := Context.real
  (RealContext.register HexRationalFnMathlib.ratField_eq prefixContext (key 1) (present 1) (valid 1))

-- The exposed companion helper builds the same context as the core constructor.
example (a : Element (realContext 1)) : Element derived := a
#guard (⟨positive.stored⟩ : Element derived).sign = 1

section MixedModel

local instance : Field (RationalFn Rat) := HexPolyMathlib.fieldOfGrind
noncomputable local instance : LinearOrder (RationalFn Rat) :=
  RealModel.linearOrder HexRationalFnMathlib.ratField_eq OrderedFn.LiouvilleTests.transcendence
local instance : IsStrictOrderedRing (RationalFn Rat) :=
  RealModel.strictOrderedRing HexRationalFnMathlib.ratField_eq OrderedFn.LiouvilleTests.transcendence

private theorem real_sign (f : RationalFn Rat) :
    (⟨f⟩ : Element (realContext 1)).sign = (SignType.sign f : Int) :=
  prefixContext.constant_orderSign HexRationalFnMathlib.ratField_eq (key 1) (present 1)
    (signProgress 1) (approxProgress 1) (source_correct 1) OrderedFn.LiouvilleTests.transcendence f

example (a : Element mixed) : a.sign =
    (SignType.sign (OrderedFn.Infinitesimal.embed
      (modelFraction HexPolyMathlib.toGrind_fieldOfGrind a.stored)) : Int) :=
  Element.infinitesimal_sign HexPolyMathlib.toGrind_fieldOfGrind (realContext 1) real_sign a

example (a : Element (realContext 1)) : a.embed.sign = a.sign :=
  Element.embed_sign HexPolyMathlib.toGrind_fieldOfGrind (realContext 1) real_sign a

example (a b : Element (realContext 1)) : a.embed.compare b.embed = a.compare b :=
  Element.embed_compare HexPolyMathlib.toGrind_fieldOfGrind (realContext 1) real_sign a b

example : epsilon.sign = 1 :=
  Element.infinitesimal_pos HexPolyMathlib.toGrind_fieldOfGrind (realContext 1) real_sign

example (a : Element (realContext 1)) (ha : 0 < a.stored) :
    epsilon.compare a.embed = .lt :=
  Element.infinitesimal_lt HexPolyMathlib.toGrind_fieldOfGrind (realContext 1) real_sign a ha

section SecondInfinitesimal

local instance : Field (RationalFn (RationalFn Rat)) := HexPolyMathlib.fieldOfGrind
noncomputable local instance : LinearOrder (RationalFn (RationalFn Rat)) :=
  InfinitesimalModel.linearOrder HexPolyMathlib.toGrind_fieldOfGrind
local instance : IsStrictOrderedRing (RationalFn (RationalFn Rat)) :=
  InfinitesimalModel.strictOrderedRing HexPolyMathlib.toGrind_fieldOfGrind

private theorem mixed_sign (f : RationalFn (RationalFn Rat)) :
    (⟨f⟩ : Element mixed).sign = (SignType.sign f : Int) :=
  Element.infinitesimal_orderSign HexPolyMathlib.toGrind_fieldOfGrind
    (realContext 1) real_sign ⟨f⟩

example (a : Element mixed.infinitesimal) : a.sign =
    (SignType.sign (Infinitesimal.embed
      (modelFraction HexPolyMathlib.toGrind_fieldOfGrind a.stored)) : Int) :=
  Element.infinitesimal_sign HexPolyMathlib.toGrind_fieldOfGrind mixed mixed_sign a

example (a b : Element mixed) : a.embed.compare b.embed = a.compare b :=
  Element.embed_compare HexPolyMathlib.toGrind_fieldOfGrind mixed mixed_sign a b

example : (Element.infinitesimal mixed).sign = 1 :=
  Element.infinitesimal_pos HexPolyMathlib.toGrind_fieldOfGrind mixed mixed_sign

example (a : Element mixed) (ha : 0 < a.stored) :
    (Element.infinitesimal mixed).compare a.embed = .lt :=
  Element.infinitesimal_lt HexPolyMathlib.toGrind_fieldOfGrind mixed mixed_sign a ha

end SecondInfinitesimal

end MixedModel

example (a : Element (rational registry).infinitesimal) : a.sign =
    (SignType.sign (Infinitesimal.embed
      (modelFraction HexRationalFnMathlib.ratField_eq a.stored)) : Int) :=
  Element.infinitesimal_sign HexRationalFnMathlib.ratField_eq (rational registry)
    Infinitesimal.orderSign_eq a

private def rationalValue : Element (.real prefixContext) := ⟨3⟩
private def included : Element (realContext 1) :=
  Element.embedConstant prefixContext (key 1) (present 1)
    (signProgress 1) (approxProgress 1) rationalValue

private def rationalPolynomial : Polynomial (.real prefixContext) :=
  Polynomial.ofCoeffs #[rationalValue, 1, 2]

private def realPolynomial : Polynomial (realContext 1) :=
  rationalPolynomial.embedConstant prefixContext (key 1) (present 1)
    (signProgress 1) (approxProgress 1)

private def namedPolynomial : Polynomial (realContext 1) :=
  Polynomial.ofCoeffs #[positive, 1]

example (p : Polynomial (.real prefixContext)) (a : Element (.real prefixContext)) :
    (p.embedConstant prefixContext (key 1) (present 1) (signProgress 1) (approxProgress 1)).eval
      (Element.embedConstant prefixContext (key 1) (present 1) (signProgress 1) (approxProgress 1) a) =
    Element.embedConstant prefixContext (key 1) (present 1) (signProgress 1) (approxProgress 1)
      (p.eval a) :=
  Polynomial.embedConstant_eval prefixContext (key 1) (present 1)
    (signProgress 1) (approxProgress 1) p a

private theorem rational_sign (a : Rat) : orderSign a = sgn ((Rat.castHom ℝ) a) := by
  rw [Infinitesimal.orderSign_eq]
  change (SignType.sign a : Int) = (SignType.sign (a : ℝ) : Int)
  simp only [sign_apply, Rat.cast_pos, Rat.cast_lt_zero]

example (a b : Element (.real prefixContext)) :
    (Element.embedConstant prefixContext (key 1) (present 1)
      (signProgress 1) (approxProgress 1) a).compare
    (Element.embedConstant prefixContext (key 1) (present 1)
      (signProgress 1) (approxProgress 1) b) = a.compare b :=
  Element.embedConstant_compare HexRationalFnMathlib.ratField_eq prefixContext
    (key 1) (present 1) (signProgress 1) (approxProgress 1)
    (source_correct 1) OrderedFn.LiouvilleTests.transcendence rational_sign a b

#guard positive.sign = 1
#guard included.sign = 1
#guard included.equal 3
#guard positive.equal positive
#guard !(positive.equal 0)
#guard (0 : Element (realContext 1)).inv?.isNone
#guard positive.inv?.isSome
#guard (positive - positive).sign = 0
#guard (epsilon - positive.embed).sign = -1
#guard epsilon.sign = 1
#guard (Element.infinitesimal mixed - epsilon.embed).sign = -1
#guard (realPolynomial.eval included).equal 24
#guard (namedPolynomial.eval positive).equal (positive + positive)
#guard ((Polynomial.ofCoeffs #[-positive, 1]).eval positive).sign = 0
#guard (Polynomial.read (realContext 1) namedPolynomial.write).map Polynomial.stored =
  some namedPolynomial.stored
#guard (Polynomial.read (realContext 2) namedPolynomial.write).isNone
#guard (Polynomial.read (realContext 1) realPolynomial.write).map Polynomial.stored =
  some realPolynomial.stored
#guard (Polynomial.read (realContext 2) realPolynomial.write).isNone
#guard (Element.read (realContext 1) positive.write).map Element.stored = some positive.stored
#guard (Element.read (realContext 2) positive.write).isNone
#guard (Element.read mixed positive.write).isNone
#guard (Element.read mixed epsilon.write).map Element.stored = some epsilon.stored
#check_failure (fun (a : Element (realContext 1)) => (a : Element (realContext 2)))
#check_failure (fun (p : Polynomial (realContext 1)) => (p : Polynomial (realContext 2)))
#check_failure (fun (p : Polynomial (realContext 1)) (q : Polynomial (realContext 2)) => p + q)

example (p : Polynomial (realContext 1)) : Polynomial derived := p

private abbrev entry (version : Nat) : RealPrefix registry := .pack
  (prefixContext.constant (key version) (present version)
    (signProgress version) (approxProgress version))
private def installed := (Catalog.empty registry).insert (entry 1)
private def catalog := installed.getD (Catalog.empty registry)
private def extendedCatalog := (catalog.insert (entry 2)).getD catalog

#guard installed.isSome
#guard (catalog.insert (entry 1)).isNone
#guard (catalog.readElement positive.write).map PackedElement.sign = some 1
#guard (catalog.readElement (positive - positive).write).map PackedElement.sign = some 0
#guard (catalog.readElement epsilon.write).map PackedElement.sign = some 1
#guard (catalog.readElement (Element.infinitesimal mixed - epsilon.embed).write).map
  PackedElement.sign = some (-1)
#guard ((Catalog.empty registry).read (realContext 1).signature).isNone
#guard (catalog.read (realContext 2).signature).isNone
#guard (extendedCatalog.read (realContext 2).signature).isSome
#guard (extendedCatalog.readElement positive.write).map PackedElement.sign = some 1
#guard (catalog.read ⟨[key 1, key 1], 0⟩).isNone
#guard (catalog.read ⟨[⟨"other", 1⟩], 0⟩).isNone
#guard (catalog.readElement ⟨(realContext 1).signature, .rational 1⟩).isNone
#guard (catalog.readPolynomial namedPolynomial.write).isSome
#guard ((Catalog.empty registry).readPolynomial namedPolynomial.write).isNone
#guard (catalog.readPolynomial { namedPolynomial.write with binding :=
  (realContext 2).signature }).isNone
#guard (catalog.readPolynomial { namedPolynomial.write with coefficients :=
  [.rational 1] }).isNone

private theorem entry_keys (version : Nat) : (entry version).keys = [key version] := by
  rw [RealPrefix.keys_pack]
  have h := RealContext.keys_constant prefixContext (key version) (present version)
    (signProgress version) (approxProgress version)
  have hp : prefixContext.chain.keys = [] := RealContext.keys_rational registry
  simpa only [RealContext.keys, hp, List.nil_append] using h

private theorem installed_some : installed.isSome = true :=
  (Catalog.insert_isSome_iff (Catalog.empty registry) (entry 1)).mpr
    (Catalog.lookup_empty registry (entry 1).keys (by rw [entry_keys]; simp))

private theorem installed_eq : installed = some catalog := by
  cases h : installed with
  | none =>
    have hs := installed_some
    simp [h] at hs
  | some c => simp [catalog, h]

private theorem catalog_lookup : catalog.lookup (entry 1).keys = some (entry 1) := by
  simpa using Catalog.lookup_of_insert (Catalog.empty registry) catalog (entry 1)
    (entry 1).keys installed_eq

private theorem named_prefix :
    (PackedContext.pack (realContext 1)).realPrefix = entry 1 :=
  Context.realPrefix_real _

example : catalog.readElement positive.write =
    some (⟨.pack (realContext 1), positive⟩ : PackedElement registry) := by
  exact Catalog.read_write catalog (⟨.pack (realContext 1), positive⟩ : PackedElement registry)
    (by simpa only [named_prefix] using catalog_lookup)

example : catalog.readPolynomial namedPolynomial.write =
    some (⟨.pack (realContext 1), namedPolynomial⟩ : PackedPolynomial registry) := by
  exact Catalog.readPolynomial_write catalog
    (⟨.pack (realContext 1), namedPolynomial⟩ : PackedPolynomial registry)
    (by simpa only [named_prefix] using catalog_lookup)

example : (registry ⟨"unknown", 1⟩).isSome = false := by decide +kernel

section TwoConstants

local instance : Field (RationalFn Rat) := HexPolyMathlib.fieldOfGrind

-- The second provider is arbitrary: repeating the first constant would not
-- satisfy relative transcendence over the whole predecessor field.
example (r : Registry) (k₁ k₂ : ConstantKey)
    (p₁ : (r k₁).isSome = true) (p₂ : (r k₂).isSome = true) (τ σ : ℝ)
    (ha : ApproximationCorrect (Rat.castHom ℝ) τ
      ((RealContext.rational r).source k₁ p₁))
    (hw : ApproximationWidth ((RealContext.rational r).source k₁ p₁))
    (ht : Real.RelativeTranscendence (Rat.castHom ℝ) τ)
    (hc₂ : ∀ δ, 0 < δ → Contains ((r k₂).get p₂ δ) σ)
    (hw₂ : ∀ δ, 0 < δ → ((r k₂).get p₂ δ).width ≤ δ)
    (ht₂ : Real.RelativeTranscendence
      (RealModel.evalHom HexRationalFnMathlib.ratField_eq ht) σ) :
    let first := RealContext.register HexRationalFnMathlib.ratField_eq
      (RealContext.rational r) k₁ p₁ ⟨Rat.castHom ℝ, τ, ha, hw, ht⟩
    ∃ (sp : ∀ f : RationalFn (RationalFn Rat),
        Acc (Next (Real.attempt (first.source k₂ p₂) f)) 0)
      (ap : ∀ (f : RationalFn (RationalFn Rat)) (δ : Rat),
        Acc (Next (Real.approxAttempt (first.source k₂ p₂) f (Real.requestWidth δ))) 0),
      (Context.real (first.constant k₂ p₂ sp ap)).signature.constants = [k₁, k₂] ∧
      (∀ f : RationalFn (RationalFn Rat),
        (⟨f⟩ : Element (.real (first.constant k₂ p₂ sp ap))).sign =
          sgn (Real.eval (RealModel.evalHom HexRationalFnMathlib.ratField_eq ht) σ
            (modelFraction HexPolyMathlib.toGrind_fieldOfGrind f)) ∧
        ((⟨f⟩ : Element (.real (first.constant k₂ p₂ sp ap))).sign = 0 ↔
          (⟨f⟩ : Element (.real (first.constant k₂ p₂ sp ap))) = 0)) ∧
      (letI : Field (RationalFn (RationalFn Rat)) := HexPolyMathlib.fieldOfGrind
       letI : LinearOrder (RationalFn (RationalFn Rat)) :=
         RealModel.linearOrder HexPolyMathlib.toGrind_fieldOfGrind ht₂
       ∀ f : RationalFn (RationalFn Rat),
         (⟨f⟩ : Element (.real (first.constant k₂ p₂ sp ap))).sign = (SignType.sign f : Int)) ∧
      (∀ a b : Element (.real first),
        (Element.embedConstant first k₂ p₂ sp ap a).compare
          (Element.embedConstant first k₂ p₂ sp ap b) = a.compare b) ∧
      ∀ a : Element (.real (first.constant k₂ p₂ sp ap)), Element.read _ a.write = some a := by
  let first := RealContext.register HexRationalFnMathlib.ratField_eq
    (RealContext.rational r) k₁ p₁ ⟨Rat.castHom ℝ, τ, ha, hw, ht⟩
  have ha₂ : ApproximationCorrect
      (RealModel.evalHom HexRationalFnMathlib.ratField_eq ht) σ (first.source k₂ p₂) :=
    (RealContext.rational r).source_correct HexRationalFnMathlib.ratField_eq
      k₁ p₁ _ _ ha ht k₂ p₂ σ hc₂
  have width₂ : ApproximationWidth (first.source k₂ p₂) :=
    (RealContext.rational r).source_width k₁ p₁ _ _ k₂ p₂ hw₂
  let reg₂ := first.registration HexPolyMathlib.toGrind_fieldOfGrind k₂ p₂
    ⟨RealModel.evalHom HexRationalFnMathlib.ratField_eq ht, σ, ha₂, width₂, ht₂⟩
  refine ⟨reg₂.signProgress, reg₂.approxProgress, ?_, ?_, ?_, ?_, ?_⟩
  · have firstKeys : first.chain.keys = [k₁] :=
      ((RealContext.rational r).keys_constant k₁ p₁ _ _).trans
        (congrArg (fun ks => ks ++ [k₁]) (RealContext.keys_rational r))
    have secondKeys := first.keys_constant k₂ p₂ reg₂.signProgress reg₂.approxProgress
    exact congrArg Signature.constants (Context.signature_real _)
      |>.trans (secondKeys.trans (congrArg (fun ks => ks ++ [k₂]) firstKeys))
  · intro f
    exact ⟨first.constant_sign HexPolyMathlib.toGrind_fieldOfGrind k₂ p₂
      reg₂.signProgress reg₂.approxProgress ha₂ f,
      first.constant_zero HexPolyMathlib.toGrind_fieldOfGrind k₂ p₂
        reg₂.signProgress reg₂.approxProgress ha₂ ht₂ f⟩
  · intro f
    exact first.constant_orderSign HexPolyMathlib.toGrind_fieldOfGrind k₂ p₂
      reg₂.signProgress reg₂.approxProgress ha₂ ht₂ f
  · intro a b
    have firstSign (f : RationalFn Rat) :
        (⟨f⟩ : Element (.real first)).sign =
          sgn (RealModel.evalHom HexRationalFnMathlib.ratField_eq ht f) := by
      rw [RealModel.evalHom_apply]
      exact (RealContext.rational r).constant_sign HexRationalFnMathlib.ratField_eq
        k₁ p₁ _ _ ha f
    exact Element.embedConstant_compare HexPolyMathlib.toGrind_fieldOfGrind first k₂ p₂
      reg₂.signProgress reg₂.approxProgress ha₂ ht₂ firstSign a b
  · intro a
    exact Element.read_write a

end TwoConstants

private def prefixInclusions : IO Unit := do
  let source := (rational registry).infinitesimal
  let target := (realContext 1).infinitesimal.infinitesimal
  let some inclusion := Tower.BaseInclusion.make? (.pack source) (.pack target)
    | throw (IO.userError "proper real-prefix inclusion failed")
  let epsilon : (Tower.Context.ofBase (.pack source)).Value :=
    Element.infinitesimal (rational registry)
  let expected : (Tower.Context.ofBase (.pack target)).Value :=
    (Element.infinitesimal (realContext 1)).embed
  unless inclusion.value epsilon == expected do
    throw (IO.userError "adjoining a real constant moved the earlier infinitesimal")
  let targetContext := Tower.Context.ofBase (.pack target)
  let delta : targetContext.Value := Element.infinitesimal (realContext 1).infinitesimal
  unless targetContext.sign (delta - inclusion.value epsilon) == -1 do
    throw (IO.userError "proper real-prefix inclusion changed infinitesimal order")
  unless (Tower.BaseInclusion.make? (.pack (realContext 1))
      (.pack (realContext 2).infinitesimal)).isNone do
    throw (IO.userError "base inclusion accepted unrelated real-prefix paths")
  unless (Tower.BaseInclusion.make? (.pack target) (.pack source)).isNone do
    throw (IO.userError "base inclusion accepted a shorter real prefix")

#eval prefixInclusions

end Hex.RealClosure.BaseContext.RealTests
