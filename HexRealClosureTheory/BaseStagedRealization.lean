/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.BaseRealization
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

section RealValues

variable {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {sign : K → Int} {chain : Chain registry K sign}

/-- A native coefficient inherited from the actual caller-provided real
prefix, together with its fixed real value. Later infinitesimals include it
as a constant at every level. -/
@[expose] def Chain.Realization.RealValue (following : chain.Realization registry) :
    K → ℝ → Prop := by
  induction following with
  | real parent model previous => exact fun a r => model.hom a = r
  | infinitesimal parent previous ih =>
    exact fun a r => ∃ b, a = RationalFn.C b ∧ ih b r

/-- Index transport changes no inherited real coefficient values. -/
theorem Chain.Realization.realValue_cast {other : Chain registry K sign}
    (same : chain = other) (following : chain.Realization registry) (a : K) (r : ℝ) :
    (same ▸ following).RealValue a r ↔ following.RealValue a r := by
  cases same
  rfl

/-- Real-prefix coefficients have their caller-supplied interpreted values. -/
@[simp] theorem Chain.Realization.realValue_real
    {A : Type} [Lean.Grind.Field A] [DecidableEq A]
    {approx : A → Rat → OrderedFn.Oracle.Bounds} {nativeSign : A → Int}
    (parent : RealChain registry A approx nativeSign)
    (model : (RealContext.ofChain parent).Interpretation)
    (previous : parent.Realization registry model) (a : A) (r : ℝ) :
    (Chain.Realization.real parent model previous).RealValue a r ↔ model.hom a = r := Iff.rfl

/-- Adding an infinitesimal retains exactly the embedded real-prefix values. -/
@[simp] theorem Chain.Realization.realValue_infinitesimal
    (parent : Chain registry K sign) (previous : parent.Realization registry)
    (a : RationalFn K) (r : ℝ) :
    (Chain.Realization.infinitesimal parent previous).RealValue a r ↔
      ∃ b, a = RationalFn.C b ∧ previous.RealValue b r := Iff.rfl

end RealValues

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
    let : Field B := HexPolyTheory.fieldOfGrind
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

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.embedding_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.embedding_sign
