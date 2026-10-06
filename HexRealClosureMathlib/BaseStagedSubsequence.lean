/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseSubsequence
public import HexRealClosureMathlib.BaseStagedRealization

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

variable {registry : Registry}

/-- A real-prefix factory preserves the interpretations of both actual
provider histories. The staged lift uses this law at its real base case. -/
structure RealChain.Factory.Valid (factory : RealChain.Factory registry) : Prop where
  value : ∀ {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (_following : target.Realization registry model)
    {source : RealChain registry S sourceApprox sourceSign}
    {original : (RealContext.ofChain source).Interpretation}
    (_original : source.Realization registry original)
    (map : FieldEmbedding S K) (_produced : factory target source = some map)
    (a : S), model.hom (map.value a) = original.hom a

/-- The checked subsequence map preserves signs through both actual provider
realizations and all retained or additional infinitesimal variables. -/
theorem Chain.Realization.lift_sign
    (factory : RealChain.Factory registry) (valid : factory.Valid)
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (realization : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.lift? factory source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  induction realization generalizing S with
  | real targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change factory targetReal sourceReal = some map at produced
      calc
        _ = sgn (model.hom (map.value a)) := model.sign _
        _ = sgn (sourceModel.hom a) := congrArg sgn (valid.value targetProof sourceProof map produced a)
        _ = _ := (sourceModel.sign a).symm
    | infinitesimal sourceParent sourceProof =>
      change none = some map at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.lift?.eq_def] at produced
      simp only [deeper, ↓reduceIte] at produced
      cases found : parent.lift? factory source with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        rw [FieldEmbedding.comp_value]
        exact (FieldEmbedding.constants_sign _ previous.sign_zero previous.sign_one _).trans
          (ih source original previousMap found a)
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.lift?.eq_def] at produced
        simp only [deeper, ↓reduceIte] at produced
        cases found : parent.lift? factory sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          exact FieldEmbedding.rationalFunctions_sign previousMap _ _
            (fun b => ih sourceParent sourceProof previousMap found b) a

/-- Two factories preserving the actual provider interpretations produce
the same staged map whenever both accept the same source and target. -/
theorem Chain.Realization.lift_eq
    (first next : RealChain.Factory registry) (firstValid : first.Valid) (nextValid : next.Valid)
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (left right : FieldEmbedding S K)
    (leftProduced : target.lift? first source = some left)
    (rightProduced : target.lift? next source = some right) : left = right := by
  induction following generalizing S with
  | @real B field eq approx sign targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change first targetReal sourceReal = some left at leftProduced
      change next targetReal sourceReal = some right at rightProduced
      letI : Field B := HexPolyMathlib.fieldOfGrind
      apply FieldEmbedding.value_ext
      intro a
      apply model.hom.injective
      rw [firstValid.value targetProof sourceProof left leftProduced a,
        nextValid.value targetProof sourceProof right rightProduced a]
    | infinitesimal sourceParent sourceProof =>
      change none = some left at leftProduced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.lift?.eq_def] at leftProduced rightProduced
      simp only [deeper, ↓reduceIte] at leftProduced rightProduced
      cases leftFound : parent.lift? first source with
      | none => simp only [leftFound, Option.map_none] at leftProduced; contradiction
      | some leftMap =>
        cases rightFound : parent.lift? next source with
        | none => simp only [rightFound, Option.map_none] at rightProduced; contradiction
        | some rightMap =>
          simp only [leftFound, Option.map_some, Option.some.injEq] at leftProduced
          simp only [rightFound, Option.map_some, Option.some.injEq] at rightProduced
          subst left right
          rw [ih source original leftMap rightMap leftFound rightFound]
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.lift?.eq_def] at leftProduced rightProduced
        simp only [deeper, ↓reduceIte] at leftProduced rightProduced
        cases leftFound : parent.lift? first sourceParent with
        | none => simp only [leftFound, Option.map_none] at leftProduced; contradiction
        | some leftMap =>
          cases rightFound : parent.lift? next sourceParent with
          | none => simp only [rightFound, Option.map_none] at rightProduced; contradiction
          | some rightMap =>
            simp only [leftFound, Option.map_some, Option.some.injEq] at leftProduced
            simp only [rightFound, Option.map_some, Option.some.injEq] at rightProduced
            subst left right
            rw [ih sourceParent sourceProof leftMap rightMap leftFound rightFound]

/-- Checked staged subsequences retain the prescribed real values of every
inherited provider coefficient, even between independently validated prefixes. -/
theorem Chain.Realization.lift_realValue
    (factory : RealChain.Factory registry) (valid : factory.Valid)
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.lift? factory source = some map)
    (a : S) (r : ℝ) (inherited : original.RealValue a r) :
    following.RealValue (map.value a) r := by
  induction following generalizing S with
  | real targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change factory targetReal sourceReal = some map at produced
      change model.hom (map.value a) = r
      exact (valid.value targetProof sourceProof map produced a).trans inherited
    | infinitesimal sourceParent sourceProof =>
      change none = some map at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.lift?.eq_def] at produced
      simp only [deeper, ↓reduceIte] at produced
      cases found : parent.lift? factory source with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        exact ⟨previousMap.value a,
          by rw [FieldEmbedding.comp_value, FieldEmbedding.constants_value],
          ih source original previousMap found a inherited⟩
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.lift?.eq_def] at produced
        simp only [deeper, ↓reduceIte] at produced
        cases found : parent.lift? factory sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          obtain ⟨b, same, real⟩ := inherited
          subst a
          refine ⟨previousMap.value b, ?_, ih sourceParent sourceProof previousMap found b real⟩
          rw [FieldEmbedding.rationalFunctions_value, RationalFn.mapCoeffs_C]

theorem RealChain.subsequence_valid :
    RealChain.Factory.Valid (registry := registry) (fun target source => target.subsequence? source) :=
by
  constructor
  intro K S fieldK eqK fieldS eqS approx sign sourceApprox sourceSign target model
    following source original sourceProof map produced a
  exact following.subsequence sourceProof map produced a

/-- The ordered factory uses the common staged preservation law. -/
theorem Chain.Realization.subsequence_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (realization : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  exact realization.lift_sign _ RealChain.subsequence_valid source original map produced a

/-- The ordered factory uses the common staged preservation law. -/
theorem Chain.Realization.subsequence_realValue
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map)
    (a : S) (r : ℝ) (inherited : original.RealValue a r) :
    following.RealValue (map.value a) r := by
  exact following.lift_realValue _ RealChain.subsequence_valid source original map produced a r inherited


end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.subsequence_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.subsequence_sign

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A checked nominal inclusion preserves signs through the provider-derived
real subsequences and all staged infinitesimals. No agreement premise is required. -/
theorem BaseInclusion.sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Chain registry S sourceSign)
    (target : BaseContext.Chain registry K sign)
    (original : source.Realization registry) (following : target.Realization registry)
    (inclusion : BaseInclusion (.pack (BaseContext.Context.ofChain source))
      (.pack (BaseContext.Context.ofChain target)))
    (a : (Context.ofBase (.pack (BaseContext.Context.ofChain source))).Value) :
    (Context.ofBase (.pack (BaseContext.Context.ofChain target))).sign (inclusion.value a) =
      (Context.ofBase (.pack (BaseContext.Context.ofChain source))).sign a := by
  change sign (inclusion.coefficients.value a.stored) = sourceSign a.stored
  exact following.subsequence_sign source original inclusion.coefficients
    (by simpa only [BaseContext.PackedContext.subsequence?_ofChain] using inclusion.produced) a.stored

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.sign

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.subsequence_realValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.subsequence_realValue

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.lift_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.lift_sign

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.lift_realValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.lift_realValue

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.lift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.lift_eq

/-- info: 'Hex.RealClosure.BaseContext.RealChain.subsequence_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.subsequence_valid
