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

/-- The checked subsequence map preserves signs through both actual provider
realizations and all retained or additional infinitesimal variables. -/
theorem Chain.Realization.subsequence_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (realization : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  induction realization generalizing S with
  | real targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change targetReal.subsequence? sourceReal = some map at produced
      exact targetProof.subsequence_sign sourceProof map produced a
    | infinitesimal sourceParent sourceProof =>
      change none = some map at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.subsequence?.eq_def] at produced
      simp only [deeper, ↓reduceIte] at produced
      cases found : parent.subsequence? source with
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
        rw [Chain.subsequence?.eq_def] at produced
        simp only [deeper, ↓reduceIte] at produced
        cases found : parent.subsequence? sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          exact FieldEmbedding.rationalFunctions_sign previousMap _ _
            (fun b => ih sourceParent sourceProof previousMap found b) a

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.subsequence_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.subsequence_sign

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
  exact following.subsequence_sign source original inclusion.coefficients
    (by simpa only [BaseContext.PackedContext.subsequence?_ofChain] using inclusion.produced) a.stored

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.sign
