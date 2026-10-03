/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignEvidence
public import HexRealClosureMathlib.SignFacts

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

/-- Derive every scalar fact from one checked joint row. The interpretation
arguments occur only in erased proofs. Exact original keys, including zero
and repeated keys, occupy the same vector slots as the requested queries. -/
@[expose, macro_inline] def Context.signFacts (context : Context E Ctx coeffSign parent)
    {queries : List (DensePoly E)} (signs : SelectedSigns context.root queries) :
    Vector (SignFact context) queries.length :=
  Vector.ofFn fun i => ⟨queries[i.val], signs.values[i.val], by
    rw [context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi,
      Context.evalPoly, Context.rootValue]
    have values := signs.values_at_root f hz h1 ha hs hm hnat hsign
    have slot := congrArg (fun xs : List Int => xs[i.val]?) values
    simpa [signsAt, i.isLt] using slot.symm⟩

/-- This executable extraction retains every original slot literally. -/
theorem Context.signFacts_fields (context : Context E Ctx coeffSign parent)
    {queries : List (DensePoly E)} (signs : SelectedSigns context.root queries)
    (i : Fin queries.length) :
    (context.signFacts f hz h1 ha hs hm hnat hsign hn hi signs)[i.val].polynomial =
      queries[i.val] ∧
    (context.signFacts f hz h1 ha hs hm hnat hsign hn hi signs)[i.val].sign =
      signs.values[i.val] := by
  simp [Context.signFacts]

/-- Check the supplied child graph once and derive all its requested facts.
Missing or false evidence returns `none`; no producer is called to fill gaps. -/
@[expose, macro_inline] def Context.readEvidence? (context : Context E Ctx coeffSign parent)
    (required : List (DensePoly E)) (evidence : SignEvidence E Ctx) :
    Option (Vector (SignFact context) required.length) :=
  let context := context
  match evidence.check? context required with
  | none => none
  | some signs => some (context.signFacts f hz h1 ha hs hm hnat hsign hn hi signs)

/-- Checking a packet made from joint signs returns exactly their scalar
facts, rather than merely some vector of the same length. -/
theorem Context.readEvidence_ofSigns [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) (queries : List (DensePoly E))
    (signs : SelectedSigns context.root queries) :
    context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi queries
      (SignEvidence.ofSigns signs) =
        some (context.signFacts f hz h1 ha hs hm hnat hsign hn hi signs) := by
  unfold Context.readEvidence?
  dsimp only
  rw [SignEvidence.check_ofSigns]

/-- Acceptance is exactly the existing independent graph selection. -/
theorem Context.readEvidence_accept (context : Context E Ctx coeffSign parent)
    (required : List (DensePoly E)) (evidence : SignEvidence E Ctx) :
    (context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence).isSome =
      (evidence.check? context required).isSome := by
  unfold Context.readEvidence?
  dsimp only
  split <;> simp_all

/-- Arbitrary successful evidence supplies one accepted joint row and all
facts derived from it. This is not restricted to producer-generated packets. -/
theorem Context.readEvidence_evidence (context : Context E Ctx coeffSign parent)
    (required : List (DensePoly E)) (evidence : SignEvidence E Ctx)
    (facts : Vector (SignFact context) required.length)
    (h : context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence = some facts) :
    ∃ signs, evidence.check? context required = some signs ∧
      facts = context.signFacts f hz h1 ha hs hm hnat hsign hn hi signs := by
  unfold Context.readEvidence? at h
  cases hc : evidence.check? context required with
  | none => simp [hc] at h
  | some signs =>
    simp only [hc, Option.some.injEq] at h
    exact ⟨signs, rfl, h.symm⟩

/-- Decode the complete context-bound child packet using the supplied
predecessor reader, then check its graph and exact required key list. -/
@[expose, macro_inline] def Context.decodeEvidence (context : Context E Ctx coeffSign parent)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (required : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits := {}) :
    Except String (Vector (SignFact context) required.length) := do
  let context := context
  let evidence ← (SignEvidence.codec value ctx context.root.raw).decodeBytes input limits
  match context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence with
  | none => throw "child sign evidence rejected"
  | some facts => return facts

/-- Success refers to the actual decoded bytes and accepted graph. No claim
about the printer, a cached sign or a second certificate replaces that check. -/
theorem Context.decodeEvidence_evidence (context : Context E Ctx coeffSign parent)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (required : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits)
    (facts : Vector (SignFact context) required.length)
    (h : context.decodeEvidence f hz h1 ha hs hm hnat hsign hn hi
      value ctx required input limits = .ok facts) :
    ∃ evidence, (SignEvidence.codec value ctx context.root.raw).decodeBytes input limits =
        .ok evidence ∧
      context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence = some facts := by
  unfold Context.decodeEvidence at h
  cases hd : (SignEvidence.codec value ctx context.root.raw).decodeBytes input limits with
  | error error => simp [hd, bind, Except.bind] at h
  | ok evidence =>
    simp only [hd, bind, Except.bind] at h
    cases hc : context.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence with
    | none => simp [hc] at h
    | some result =>
      simp only [hc, pure, Except.pure, Except.ok.injEq] at h
      subst facts
      exact ⟨evidence, rfl, hc⟩

include f hz h1 ha hs hm hnat hsign hn hi in
/-- Under the existing coefficient interpretation laws, the actual shared
producer always returns a child packet. No availability hypothesis or fallback
certificate is supplied by the caller. -/
theorem Context.buildEvidence_success [Hashable E] [Hashable Ctx]
    (context : Context E Ctx coeffSign parent) (queries : List (DensePoly E)) :
    ∃ evidence, context.buildEvidence queries = .ok evidence ∧
      (evidence.check? context queries).isSome = true := by
  obtain ⟨signs, success⟩ := context.root.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi queries
  have hc : context.buildSigns queries = .ok signs := by
    rw [context.buildSigns_eq]
    exact success
  exact ⟨SignEvidence.ofSigns signs, context.buildEvidence_of_success queries signs hc,
    by simp only [SignEvidence.check_ofSigns, Option.isSome_some]⟩

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.decodeEvidence_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.decodeEvidence_evidence

/-- info: 'Hex.RealClosure.Algebraic.Context.buildEvidence_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.buildEvidence_success
