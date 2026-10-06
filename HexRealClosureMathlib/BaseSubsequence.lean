/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseSubsequence
public import HexRealClosureMathlib.BaseRealization
public import HexRealClosureMathlib.BaseProvider
public import HexPolyMathlib.Interpret
import all HexRealClosureMathlib.BaseRealization

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

private def fractionParts {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (f : RationalFn K) : Array K × Array K := (f.num.coeffs, f.den.coeffs)

set_option linter.overlappingInstances false in
private theorem fraction_arrays {K : Type} [Field K]
    [g : Lean.Grind.Field K] [DecidableEq K]
    (compatible : Field.toGrindField (K := K) = g) (f : RationalFn K) :
    @fractionParts K Field.toGrindField inferInstance (modelFraction compatible f) =
      @fractionParts K g inferInstance f := by
  subst g
  rfl

/-- Read the native stored fraction by coefficient interpretation, including
ordinary evaluation at an arbitrary real argument. -/
theorem RealModel.eval_interpret {K : Type} [g : Lean.Grind.Field K] [DecidableEq K]
    (hom : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ)
    (τ : ℝ) (f : RationalFn K) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    Real.eval hom τ (modelFraction HexPolyMathlib.toGrind_fieldOfGrind f) =
      (HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom) f.num).eval τ /
        (HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom) f.den).eval τ := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  have polynomial (p : DensePoly K) :
      HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom) p =
        (HexPolyMathlib.toPolynomial p).map hom := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, Polynomial.coeff_map,
      HexPolyMathlib.coeff_toPolynomial]
  rw [polynomial, polynomial, Polynomial.eval_map, Polynomial.eval_map]
  unfold Real.eval
  have arrays := fraction_arrays HexPolyMathlib.toGrind_fieldOfGrind f
  have numerator := congrArg Prod.fst arrays
  have denominator := congrArg Prod.snd arrays
  dsimp only [fractionParts] at numerator denominator
  simp only [HexPolyMathlib.toPolynomial, DensePoly.size, DensePoly.coeff,
    numerator, denominator]

/-- The derived field embedding uses the same unchanged numerator and denominator. -/
theorem RealModel.evalHom_interpret {K : Type} [g : Lean.Grind.Field K] [DecidableEq K]
    {hom : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ} {τ : ℝ}
    (transcendental : letI : Field K := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence hom τ) (f : RationalFn K) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind transcendental f =
      (HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom) f.num).eval τ /
        (HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom) f.den).eval τ := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  rw [RealModel.evalHom_apply]
  exact RealModel.eval_interpret hom τ f

/-- The unchanged native formal variable evaluates to the argument without
requiring transcendence of that argument. -/
theorem RealModel.eval_X {K : Type} [g : Lean.Grind.Field K] [DecidableEq K]
    (hom : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ) (τ : ℝ) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    Real.eval hom τ (modelFraction HexPolyMathlib.toGrind_fieldOfGrind
      (RationalFn.X : RationalFn K)) = τ := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  rw [RealModel.eval_interpret]
  have numerator : HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom)
      (RationalFn.X : RationalFn K).num = Polynomial.X := by
    ext i
    simp only [HexPolyMathlib.Interpret.coeff_interpret, RationalFn.X, RationalFn.ofPoly,
      DensePoly.coeff_monomial, Polynomial.coeff_X]
    by_cases same : i = 1
    · simp only [same, ↓reduceIte, hom.map_one]
    · simp only [same, Ne.symm same, ↓reduceIte]
      exact hom.map_zero
  have denominator : HexPolyMathlib.Interpret.interpret hom (fun a => map_eq_zero hom)
      (RationalFn.X : RationalFn K).den = 1 := by
    exact HexPolyMathlib.Interpret.interpret_one hom (fun a => map_eq_zero hom) hom.map_one
  rw [numerator, denominator, Polynomial.eval_X, Polynomial.eval_one, div_one]

/-- Retaining the formal variable commutes with real evaluation when the
coefficient map already preserves its predecessor values. -/
theorem RealModel.evalHom_map {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {original : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ}
    {following : letI : Field L := HexPolyMathlib.fieldOfGrind; L →+* ℝ} {τ : ℝ}
    (sourceTranscendental : letI : Field K := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence original τ)
    (targetTranscendental : letI : Field L := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence following τ)
    (map : FieldEmbedding K L)
    (agreement : ∀ a, following (map.value a) = original a) (f : RationalFn K) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI : Field L := HexPolyMathlib.fieldOfGrind
    RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind targetTranscendental
      (map.rationalFunctions.value f) =
        RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind sourceTranscendental f := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field L := HexPolyMathlib.fieldOfGrind
  have polynomial (p : DensePoly K) :
      HexPolyMathlib.Interpret.interpret following (fun a => map_eq_zero following)
        (DensePoly.Interpret.map map.value map.zero p) =
          HexPolyMathlib.Interpret.interpret original (fun a => map_eq_zero original) p := by
    ext i
    rw [HexPolyMathlib.Interpret.coeff_interpret, DensePoly.Interpret.map_coeff,
      HexPolyMathlib.Interpret.coeff_interpret, agreement]
  rw [RealModel.evalHom_interpret, RealModel.evalHom_interpret,
    FieldEmbedding.rationalFunctions_value]
  simp only [RationalFn.mapCoeffs_num, RationalFn.mapCoeffs_den, polynomial]

/-- Stored approximation progress forces a registered provider to denote one
real value. The proof uses the actual computed bounds for its formal variable. -/
theorem RealContext.provider_unique {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) (model : parent.Interpretation)
    (key : ConstantKey) (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)
    (τ σ : ℝ)
    (left : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (right : ∀ δ, 0 < δ → Contains ((registry key).get present δ) σ) : τ = σ := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  let child := parent.constant key present sp ap
  let formalX : RationalFn K := RationalFn.X
  have contains (x : ℝ)
      (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) x) (δ : Rat) :
      Contains (child.approx formalX δ) x := by
    have actual := parent.constant_contains HexPolyMathlib.toGrind_fieldOfGrind
      key present sp ap (model.source_correct key present x contained) formalX δ
    simpa only [formalX, RealModel.eval_X] using actual
  have widths := Real.width_tendsto (fun δ => child.approx formalX δ)
    (fun δ positive => child.approx_width formalX δ positive)
  exact tendsto_nhds_unique
    (Contains.endpoints_tendsto (fun n => contains τ left (Real.precision n)) widths).1
    (Contains.endpoints_tendsto (fun n => contains σ right (Real.precision n)) widths).1

private theorem RealChain.provider_unique {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealChain registry K approx sign)
    (model : (RealContext.ofChain parent).Interpretation)
    (key : ConstantKey) (bounds : Rat → Bounds) (registered : registry key = some bounds)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0)
    (τ σ : ℝ) (left : ∀ δ, 0 < δ → Contains (bounds δ) τ)
    (right : ∀ δ, 0 < δ → Contains (bounds δ) σ) : τ = σ := by
  have present : (registry key).isSome = true := by simp only [registered, Option.isSome_some]
  have provider : (registry key).get present = bounds := by simp only [registered]; rfl
  apply (RealContext.ofChain parent).provider_unique model key present
    (by simpa only [RealContext.source, provider] using sp)
    (by simpa only [RealContext.source, provider] using ap) τ σ
  · simpa only [provider] using left
  · simpa only [provider] using right

/-- The actual subsequence producer preserves real values between independently
registered source and target chains. Provider agreement is derived from the
same immutable registry and stored progress at every matched key. -/
theorem RealChain.Realization.subsequence
    {registry : Registry} {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (realization : target.Realization registry model)
    {source : RealChain registry S sourceApprox sourceSign}
    {original : (RealContext.ofChain source).Interpretation}
    (sourceProof : source.Realization registry original)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map)
    (a : S) : model.hom (map.value a) = original.hom a := by
  induction realization generalizing S with
  | base =>
    cases sourceProof with
    | base =>
      rw [RealChain.subsequence?] at produced
      cases produced
      rw [FieldEmbedding.identity_value]
    | step parent model previous key bounds registered sp ap τ contained transcendental =>
      rw [RealChain.subsequence?] at produced
      contradiction
  | @step B targetField targetEq targetApprox targetSign parent parentModel previous
      key bounds registered sp ap τ contained transcendental ih =>
    have sourceWhole := sourceProof
    cases sourceProof with
    | base =>
      rw [RealChain.subsequence?] at produced
      cases found : parent.subsequence? RealChain.base with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        rw [FieldEmbedding.comp_value, FieldEmbedding.constants_value,
          RealChain.interpretStep_embed]
        exact ih sourceWhole previousMap found a
    | @step A sourceField sourceEq sourceApprox sourceSign sourceParent sourceModel sourcePrevious
        sourceKey sourceBounds sourceRegistered sourceSp sourceAp σ sourceContained sourceTranscendental =>
      by_cases same : sourceKey = key
      · subst sourceKey
        have providers : sourceBounds = bounds := Option.some.inj (sourceRegistered.symm.trans registered)
        subst sourceBounds
        have arguments : τ = σ := parent.provider_unique parentModel key bounds registered sp ap
          τ σ contained sourceContained
        subst σ
        rw [RealChain.subsequence?] at produced
        simp only [↓reduceIte] at produced
        cases found : parent.subsequence? sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          letI : Field A := HexPolyMathlib.fieldOfGrind
          letI : Field B := HexPolyMathlib.fieldOfGrind
          change RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind transcendental
            (previousMap.rationalFunctions.value a) =
              RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind sourceTranscendental a
          exact RealModel.evalHom_map sourceTranscendental transcendental previousMap
            (fun b => ih sourcePrevious previousMap found b) a
      · rw [RealChain.subsequence?] at produced
        simp only [same, ↓reduceIte] at produced
        cases found : parent.subsequence?
          (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp) with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          rw [FieldEmbedding.comp_value, FieldEmbedding.constants_value,
            RealChain.interpretStep_embed]
          exact ih sourceWhole previousMap found a

/-- Checked subsequence inclusions preserve coefficients in both independently
registered provider models. -/
theorem RealPrefix.Model.subsequence {registry : Registry} (source target : Model registry)
    (map : FieldEmbedding source.context.Carrier target.context.Carrier)
    (produced : source.context.subsequence? target.context = some map)
    (a : source.context.Carrier) : target.interpretation.hom (map.value a) =
      source.interpretation.hom a := by
  cases source with
  | pack original originalModel originalProof =>
    cases target with
    | pack following followingModel followingProof =>
      change (RealContext.ofChain following).chain.subsequence?
        (RealContext.ofChain original).chain = some map at produced
      rw [RealContext.ofChain_chain, RealContext.ofChain_chain] at produced
      exact followingProof.subsequence originalProof map produced a

/-- The complete key check produces an actual value-preserving native map.
Each model retains its own progress premises for its exact predecessor. -/
theorem RealPrefix.Model.subsequence_map {registry : Registry} (source target : Model registry)
    (keys : List.Sublist source.context.keys target.context.keys) :
    ∃ map : FieldEmbedding source.context.Carrier target.context.Carrier,
      source.context.subsequence? target.context = some map ∧
      ∀ a, target.interpretation.hom (map.value a) = source.interpretation.hom a := by
  have success := (RealPrefix.subsequence?_isSome source.context target.context).mpr keys
  cases produced : source.context.subsequence? target.context with
  | none => simp only [produced, Option.isSome_none, Bool.false_eq_true] at success
  | some map => exact ⟨map, rfl, fun a => source.subsequence target map produced a⟩

/-- The same derived inclusion preserves the actual source and target sign
operations, without a caller sign-agreement premise. -/
theorem RealChain.Realization.subsequence_sign
    {registry : Registry} {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (realization : target.Realization registry model)
    {source : RealChain registry S sourceApprox sourceSign}
    {original : (RealContext.ofChain source).Interpretation}
    (sourceProof : source.Realization registry original)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  calc
    sign (map.value a) = sgn (model.hom (map.value a)) := model.sign _
    _ = sgn (original.hom a) := congrArg sgn
      (realization.subsequence sourceProof map produced a)
    _ = sourceSign a := (original.sign a).symm

end Hex.RealClosure.BaseContext


/-- info: 'Hex.RealClosure.BaseContext.RealContext.provider_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.provider_unique

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.subsequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.subsequence

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.subsequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.subsequence

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.subsequence_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.subsequence_map

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.subsequence_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.subsequence_sign
