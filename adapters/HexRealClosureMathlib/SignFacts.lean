/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts
public import HexRealClosureMathlib.Algebraic
public import HexSignDetMathlib.DagSelectedSigns
public import HexSignDet.Codec

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
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

/-- Restore a literal scalar-sign fact from a shared checked graph. The graph
row must supply the actual reduced query, descriptor prefix and claimed sign.
The interpretation laws prove correspondence; they do not produce evidence.
Inlining removes the interpretation and field instances before compilation,
since they occur only in the erased proof of the returned fact. Computing the
reduced query uses the predecessor's ordinary coefficient operations. -/
@[expose, macro_inline] def Context.readSignFact? (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (SignFact context) :=
  match h : context.readSigns? p claimed memo index with
  | none => none
  | some signs => some ⟨p, claimed, by
      have checked := context.signPoly_checked f hz h1 ha hs hm hnat hsign hn hi p signs
      exact checked.trans (Context.readSigns_value h)⟩

theorem Context.readSignFact_fields (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    (fact : SignFact context)
    (h : context.readSignFact? f hz h1 ha hs hm hnat hsign hn hi p claimed memo index = some fact) :
    fact.polynomial = p ∧ fact.sign = claimed := by
  unfold Context.readSignFact? at h
  split at h
  · contradiction
  · cases Option.some.inj h
    exact ⟨rfl, rfl⟩

/-- Acceptance is exactly that of the supplied memo selection. Selection adds
no call to this context's sign producer and supplies no replacement evidence
or default sign. Predecessor arithmetic retains its existing implementation. -/
theorem Context.readSignFact_accept (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    (context.readSignFact? f hz h1 ha hs hm hnat hsign hn hi p claimed memo index).isSome =
      (SignDet.SelectedSigns.readMemo? context.root [context.queryPoly p]
        #v[claimed] memo index).isSome := by
  unfold Context.readSignFact? Context.readSigns?
  split <;> simp_all

end Hex.RealClosure.Algebraic

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

/-- Decode a supplied sign graph at the actual predecessor and descriptor.
The coefficient and context codecs are supplied by the caller. All entries
are independently checked before selection of the original reduced query.
The interpretation is used only for the erased correspondence proof. -/
@[expose, macro_inline] def Context.readSignPacket? (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    (p : DensePoly E) (claimed : Int) (packet : SignDet.Codec.Json) :
    Option (SignFact context) := do
  let graph ← (SignDet.Codec.readGraph value ctx parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? coeffSign parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  context.readSignFact? f hz h1 ha hs hm hnat hsign hn hi p claimed memo graph.root

/-- Success retains the exact supplied graph and its validation, rather than
replacing the packet with evidence produced from the requested query. -/
theorem Context.readSignPacket_evidence (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    (p : DensePoly E) (claimed : Int) (packet : SignDet.Codec.Json)
    {fact : SignFact context}
    (h : context.readSignPacket? f hz h1 ha hs hm hnat hsign hn hi value ctx p claimed packet =
      some fact) :
    ∃ graph memo,
      SignDet.Codec.readGraph value ctx parent context.root.raw.head
        context.root.raw.lower context.root.raw.upper packet = .ok graph ∧
      graph.validate? coeffSign parent context.root.raw.head
        context.root.raw.lower context.root.raw.upper = some memo ∧
      context.readSignFact? f hz h1 ha hs hm hnat hsign hn hi p claimed memo graph.root =
        some fact := by
  unfold Context.readSignPacket? at h
  cases hd : SignDet.Codec.readGraph value ctx parent context.root.raw.head
      context.root.raw.lower context.root.raw.upper packet with
  | error error => simp [hd, Except.toOption] at h
  | ok graph =>
    simp only [hd, Except.toOption, bind, Option.bind] at h
    cases hmemo : graph.validate? coeffSign parent context.root.raw.head
        context.root.raw.lower context.root.raw.upper with
    | none => simp [hmemo] at h
    | some memo =>
      simp only [hmemo, bind, Option.bind] at h
      exact ⟨graph, memo, rfl, hmemo, h⟩

theorem Context.readSignPacket_fields (context : Context E Ctx coeffSign parent)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    (p : DensePoly E) (claimed : Int) (packet : SignDet.Codec.Json)
    {fact : SignFact context}
    (h : context.readSignPacket? f hz h1 ha hs hm hnat hsign hn hi value ctx p claimed packet =
      some fact) : fact.polynomial = p ∧ fact.sign = claimed := by
  obtain ⟨graph, memo, _, _, selected⟩ :=
    context.readSignPacket_evidence f hz h1 ha hs hm hnat hsign hn hi value ctx p claimed packet h
  exact context.readSignFact_fields f hz h1 ha hs hm hnat hsign hn hi p claimed memo
    graph.root fact selected

end Hex.RealClosure.Algebraic
