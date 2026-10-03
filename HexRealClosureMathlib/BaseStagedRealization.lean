/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseRealization
public import HexRealClosure.BaseInclusion

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

variable {registry : Registry}

/-- A staged base retains the provider-derived realization of its complete
real prefix. Infinitesimal steps add no new real-provider assumptions. -/
inductive Chain.Realization (registry : Registry) :
    {K : Type} → [Lean.Grind.Field K] → [DecidableEq K] → {sign : K → Int} →
    Chain registry K sign → Type 1
  | real {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → Bounds} {sign : K → Int}
      (parent : RealChain registry K approx sign)
      (model : (RealContext.ofChain parent).Interpretation)
      (realization : parent.Realization registry model) :
      Realization registry (.real parent)
  | infinitesimal {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
      (parent : Chain registry K sign) (previous : Realization registry parent) :
      Realization registry (.infinitesimal parent)

/-- Zero retains its computed sign at every staged depth. -/
theorem Chain.Realization.sign_zero
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    {chain : Chain registry K sign} (realization : chain.Realization registry) : sign 0 = 0 := by
  cases realization with
  | real parent model previous =>
    rw [model.sign]
    simp [sgn]
  | infinitesimal parent previous => exact Infinitesimal.sign_zero _

/-- One retains its computed sign at every staged depth. -/
theorem Chain.Realization.sign_one
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    {chain : Chain registry K sign} (realization : chain.Realization registry) : sign 1 = 1 := by
  induction realization with
  | @real B field eq approx sign parent model previous =>
    let : Field B := HexPolyMathlib.fieldOfGrind
    rw [model.sign]
    simp [sgn]
  | infinitesimal parent previous ih =>
    simpa only [FieldEmbedding.constants_value, RationalFn.C_one, ih] using
      FieldEmbedding.constants_sign _ previous.sign_zero ih 1

/-- Checked base transport preserves all native signs, including larger real
prefixes, retained infinitesimals and additional target infinitesimals. -/
theorem Chain.Realization.embedding_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (realization : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K)
    (produced : target.embedding? (.pack (Context.ofChain source)) = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  induction realization generalizing S with
  | real targetReal model targetModel =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      rw [Chain.embedding?_real] at produced
      exact targetModel.embedding_sign (RealContext.ofChain sourceReal) sourceModel map produced a
    | infinitesimal sourceParent sourceProof =>
      rw [Chain.embedding?_real_inf] at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : (PackedContext.pack (Context.ofChain source)).signature.infinitesimals <
        parent.signature.infinitesimals + 1
    · rw [Chain.embedding?_extra parent _ deeper] at produced
      cases found : parent.embedding? (.pack (Context.ofChain source)) with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        rw [FieldEmbedding.comp_value]
        exact (FieldEmbedding.constants_sign _ previous.sign_zero previous.sign_one _).trans
          (ih source original previousMap found a)
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        have depth : (PackedContext.pack (Context.ofChain (.real sourceReal))).signature.infinitesimals =
            0 := by
          simp only [PackedContext.signature, Context.signature, Context.ofChain_chain,
            Chain.signature]
        rw [depth] at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.embedding?_aligned parent sourceParent deeper] at produced
        cases found : parent.embedding? (.pack (Context.ofChain sourceParent)) with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          exact FieldEmbedding.rationalFunctions_sign previousMap _ _
            (fun b => ih sourceParent sourceProof previousMap found b) a

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A checked nominal inclusion preserves signs through the provider-derived
real prefixes and all staged infinitesimals. No agreement premise is required. -/
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
  exact following.embedding_sign source original inclusion.coefficients
    (by simpa only [BaseContext.PackedContext.embedding?_ofChain] using inclusion.produced) a.stored

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.embedding_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.embedding_sign

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.sign
