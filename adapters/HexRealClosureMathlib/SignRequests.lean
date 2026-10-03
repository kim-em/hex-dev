/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignRequests
public import HexRealClosureMathlib.SignFacts

public section

namespace Hex.RealClosure.Algebraic

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

/-- A supplied sign for the original polynomial agrees with the actual total
scalar operation. Reduction is justified by that operation's existing semantic
theorem, rather than recomputed while selecting the supplied evidence. -/
@[expose, macro_inline] def Context.readRequest? (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (request : SignRequest E) : Option (SignFact context) :=
  match h : request.signs? context memo with
  | none => none
  | some signs => some ⟨request.polynomial, request.sign, by
      have actual : context.signPoly request.polynomial = signs.value := by
        rw [context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi,
          Context.evalPoly, Context.rootValue]
        exact (signs.value_at_root f hz h1 ha hs hm hnat hsign).symm
      exact actual.trans (SignRequest.signs_value h)⟩

theorem Context.readRequest_fields (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (request : SignRequest E) (fact : SignFact context)
    (h : context.readRequest? f hz h1 ha hs hm hnat hsign hn hi memo request = some fact) :
    fact.polynomial = request.polynomial ∧ fact.sign = request.sign := by
  unfold Context.readRequest? at h
  split at h
  · contradiction
  · cases Option.some.inj h
    exact ⟨rfl, rfl⟩

/-- Acceptance is precisely the supplied original-query selection. -/
theorem Context.readRequest_accept (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (request : SignRequest E) :
    (context.readRequest? f hz h1 ha hs hm hnat hsign hn hi memo request).isSome =
      (request.signs? context memo).isSome := by
  unfold Context.readRequest?
  split <;> simp_all

/-- Resolve every ordered reference against one accepted memo. A missing or
false reference rejects the entire list; the successful size proof rules out
silently dropping dependencies. Interpretation arguments occur only in the
individual facts' erased proofs. -/
@[expose, macro_inline] def Context.readRequests? (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (requests : Array (SignRequest E)) :
    Option {facts : Array (SignFact context) // facts.size = requests.size} :=
  requests.mapM' fun request =>
    context.readRequest? f hz h1 ha hs hm hnat hsign hn hi memo request

/-- Decode requests bound to the exact selected-root subject, then resolve
all of them against the supplied checked memo. The predecessor codec controls
lower-level decoding; this function adds no graph or query production. -/
@[expose, macro_inline] def Context.decodeRequests (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (input : ByteArray) (limits : SignDet.Codec.Limits := {}) :
    Except String (Array (SignFact context)) := do
  let requests ← (SignRequests.codec value ctx context.root.raw).decodeBytes input limits
  match context.readRequests? f hz h1 ha hs hm hnat hsign hn hi memo requests with
  | none => throw "sign request missing or mismatched"
  | some facts => return facts.val

/-- Success uses the actual decoded bytes and a complete reference list.
The returned facts cannot omit a request. -/
theorem Context.decodeRequests_evidence (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (input : ByteArray) (limits : SignDet.Codec.Limits)
    (facts : Array (SignFact context))
    (h : context.decodeRequests f hz h1 ha hs hm hnat hsign hn hi
      value ctx memo input limits = .ok facts) :
    ∃ requests, ∃ size : facts.size = requests.size,
      (SignRequests.codec value ctx context.root.raw).decodeBytes input limits = .ok requests ∧
      context.readRequests? f hz h1 ha hs hm hnat hsign hn hi memo requests =
        some ⟨facts, size⟩ := by
  unfold Context.decodeRequests at h
  cases hr : (SignRequests.codec value ctx context.root.raw).decodeBytes input limits with
  | error error => simp [hr, bind, Except.bind] at h
  | ok requests =>
    simp only [hr, bind, Except.bind] at h
    cases hf : context.readRequests? f hz h1 ha hs hm hnat hsign hn hi memo requests with
    | none => simp [hf] at h
    | some result =>
      simp only [hf, pure, Except.pure, Except.ok.injEq] at h
      subst facts
      exact ⟨requests, result.property, rfl, hf⟩

end Hex.RealClosure.Algebraic
