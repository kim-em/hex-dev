/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosureMathlib.Algebraic
public import HexRealClosure.AlgebraicContext
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
variable (hd : ∀ a b, f (a / b) = f a / f b)


variable (first : Context E Ctx coeffSign parent)
variable {NextCtx : Type z} [DecidableEq NextCtx] {key : NextCtx}
variable (root : SignDet.Descriptor (Element first) NextCtx Element.sign key)

/-- Interpret the actual second algebraic level using the first level's proved
ordinary operations and sign. No field laws on either stored carrier are assumed. -/
noncomputable abbrev Context.nextDenote : Element (first.extend root) → K :=
  Element.denote (Element.denote f hz h1 ha hs hm hnat hsign (context := first))
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi (context := first))

include hn hi hd in
/-- The first level's zero reflection and arithmetic suffice for the second
level's actual gcd/cofactor inverse. -/
theorem Context.next_inv (a : Element (first.extend root)) :
    first.nextDenote f hz h1 ha hs hm hnat hsign hn hi root (a⁻¹) =
      (first.nextDenote f hz h1 ha hs hm hnat hsign hn hi root a)⁻¹ :=
  Element.denote_inv (Element.denote f hz h1 ha hs hm hnat hsign (context := first))
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd (context := first))
    (Element.denote_div f hz h1 ha hs hm hnat hsign hn hi hd (context := first)) a

include hn hi hd in
theorem Context.next_zero (a : Element (first.extend root)) :
    first.nextDenote f hz h1 ha hs hm hnat hsign hn hi root a = 0 ↔ a = 0 :=
  Element.denote_eq_zero (Element.denote f hz h1 ha hs hm hnat hsign (context := first))
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd (context := first)) a

include hn hi hd in
theorem Context.next_sign (a : Element (first.extend root)) :
    a.sign = (SignType.sign (first.nextDenote f hz h1 ha hs hm hnat hsign hn hi root a) : Int) :=
  Element.sign_spec (Element.denote f hz h1 ha hs hm hnat hsign (context := first))
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi (context := first))
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd (context := first)) a

/-- info: 'Hex.RealClosure.Algebraic.Context.next_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Context.next_inv
end Hex.RealClosure.Algebraic
