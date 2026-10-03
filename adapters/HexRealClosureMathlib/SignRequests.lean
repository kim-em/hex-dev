/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignRequests
public import HexRealClosureMathlib.SignFacts
import all Init.Data.Array.BasicAux

public section

namespace Hex.RealClosure.Algebraic

private theorem mapM_slots {α β : Type} (f : α → Option β) (xs : Array α)
    (ys : {a : Array β // a.size = xs.size}) (h : xs.mapM' f = some ys) :
    ∀ i (hi : i < xs.size), f xs[i] = some (ys.val[i]'(by omega)) := by
  let rec loop (i : Nat) (acc : {a : Array β // a.size = i}) (hle : i ≤ xs.size)
      (slots : ∀ j (hj : j < i),
        f (xs[j]'(by omega)) = some (acc.val[j]'(by omega)))
      (run : Array.mapM'.go f xs i acc hle = some ys) :
      ∀ j (hj : j < xs.size), f xs[j] = some (ys.val[j]'(by omega)) := by
    by_cases done : i = xs.size
    · have same : acc.val = ys.val := by
        have values := congrArg (Option.map Subtype.val) run
        cases done
        simpa [Array.mapM'.go] using values
      intro j hj
      simpa only [same] using slots j (by omega)
    · rw [Array.mapM'.go] at run
      simp only [dite_eq_right done, bind, Option.bind] at run
      cases hf : f (xs[i]'(by omega)) with
      | none => simp [hf] at run
      | some b =>
        simp only [hf] at run
        apply loop (i + 1) ⟨acc.val.push b, by simp [acc.property]⟩ (by omega) _ run
        intro j hj
        by_cases previous : j < i
        · simpa [Array.getElem_push, acc.property, previous] using slots j previous
        · have same : j = i := by omega
          subst j
          simpa [Array.getElem_push, acc.property] using hf
  termination_by xs.size - i
  exact loop 0 ⟨#[], rfl⟩ (by omega) (by omega) h

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
      rw [context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi,
        Context.evalPoly, Context.rootValue]
      have values := signs.signs.values_at_root f hz h1 ha hs hm hnat hsign
      have slot := congrArg (fun xs : List Int => xs[signs.index.val]?) values
      have bound : signs.index.val < signs.queries.length := signs.index.isLt
      simpa [Hex.SignDet.signsAt, bound, signs.query, signs.sign] using slot.symm⟩

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
  let context := context
  let memo := memo
  requests.mapM' fun request =>
    context.readRequest? f hz h1 ha hs hm hnat hsign hn hi memo request

/-- Every returned slot retains the corresponding request, in the same order. -/
theorem Context.readRequests_fields (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (requests : Array (SignRequest E))
    (facts : {a : Array (SignFact context) // a.size = requests.size})
    (h : context.readRequests? f hz h1 ha hs hm hnat hsign hn hi memo requests = some facts)
    (i : Nat) (indexLt : i < requests.size) :
    (facts.val[i]'(by omega)).polynomial = requests[i].polynomial ∧
      (facts.val[i]'(by omega)).sign = requests[i].sign := by
  exact context.readRequest_fields f hz h1 ha hs hm hnat hsign hn hi memo
    requests[i] facts.val[i] (mapM_slots _ requests facts h i indexLt)

/-- Decode requests bound to the exact selected-root subject, then resolve
all of them against the supplied checked memo. The predecessor codec controls
lower-level decoding; this function adds no graph or query production. -/
@[expose, macro_inline] def Context.decodeRequests (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (input : ByteArray) (limits : SignDet.Codec.Limits := {}) :
    Except String (Array (SignFact context)) := do
  let context := context
  let memo := memo
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
