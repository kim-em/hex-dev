/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts
public import HexRealClosureMathlib.Algebraic
public import HexSignDetMathlib.DagSelectedSigns

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
since they occur only in the erased proof of the returned fact. -/
@[expose, macro_inline] def Context.readSignFact? (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (SignFact context) :=
  match h : SignDet.SelectedSigns.readMemo? context.root [context.queryPoly p]
      #v[claimed] memo index with
  | none => none
  | some signs => some ⟨p, claimed, by
      obtain ⟨bound, _, accepted⟩ := SignDet.SelectedSigns.readMemo_evidence h
      obtain ⟨_, _, values, _⟩ := SignDet.SelectedSigns.ofMemo_evidence accepted
      have checked := context.signPoly_checked f hz h1 ha hs hm hnat hsign hn hi p signs
      simpa [SignDet.SelectedSigns.value, values] using checked⟩

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

/-- Acceptance is exactly that of the supplied memo selection. No native sign
producer, replacement certificate or default sign is used on either branch. -/
theorem Context.readSignFact_accept (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    (context.readSignFact? f hz h1 ha hs hm hnat hsign hn hi p claimed memo index).isSome =
      (SignDet.SelectedSigns.readMemo? context.root [context.queryPoly p]
        #v[claimed] memo index).isSome := by
  unfold Context.readSignFact?
  split <;> simp_all

end Hex.RealClosure.Algebraic
