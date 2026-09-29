/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Algebraic
public import HexRealClosure.AlgebraicReencode
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.RealClosure.Algebraic

open HexPolyMathlib.Interpret

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

/-- The checked re-encoding preserves the root selected in the ambient field. -/
theorem Context.rootValue_reencode (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) :
    (context.reencode r).rootValue f hz h1 ha hs hm hnat hsign =
      context.rootValue f hz h1 ha hs hm hnat hsign := by
  simpa only [Context.rootValue, context.root_reencode r] using
    r.root_eq_source f hz h1 ha hs hm hnat hsign

/-- Every predecessor-coefficient polynomial has the same selected value
after this checked change of definition. -/
theorem Context.evalPoly_reencode (context : Context E Ctx coeffSign parent)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) (p : DensePoly E) :
    (context.reencode r).evalPoly f hz h1 ha hs hm hnat hsign p =
      context.evalPoly f hz h1 ha hs hm hnat hsign p := by
  unfold Context.evalPoly
  rw [context.rootValue_reencode f hz h1 ha hs hm hnat hsign r]

namespace Element

include hn hi in
/-- Repacking preserves the mathematical value, including the selected-zero
case and the possibly different stored remainder. -/
theorem denote_reencode {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) (a : Element context) :
    (a.reencode r).denote f hz h1 ha hs hm hnat hsign =
      a.denote f hz h1 ha hs hm hnat hsign := by
  cases hstored : a.stored with
  | none =>
    have ha : a = 0 := Element.ext (by simpa only [stored_zero] using hstored)
    subst a
    rw [reencode_zero]
    simp only [denote_zero]
  | some value =>
    have hpack : a.reencode r = ofPoly a.polynomial := by
      simp only [reencode, hstored]
    rw [hpack]
    calc
      _ = (context.reencode r).evalPoly f hz h1 ha hs hm hnat hsign a.polynomial :=
        denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi a.polynomial
      _ = context.evalPoly f hz h1 ha hs hm hnat hsign a.polynomial :=
        context.evalPoly_reencode f hz h1 ha hs hm hnat hsign r a.polynomial
      _ = a.denote f hz h1 ha hs hm hnat hsign := rfl

include f hz h1 ha hs hm hnat hsign hn hi in
/-- The packed sign cache is preserved by checked re-encoding. -/
theorem sign_reencode {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) (a : Element context) :
    (a.reencode r).sign = a.sign := by
  rw [sign_spec f hz h1 ha hs hm hnat hsign hn hi (a.reencode r),
    sign_spec f hz h1 ha hs hm hnat hsign hn hi a,
    denote_reencode f hz h1 ha hs hm hnat hsign hn hi r a]

include f hz h1 ha hs hm hnat hsign hn hi in
/-- The checked conversion cannot turn a nonzero value into the canonical zero. -/
theorem reencode_zero_iff {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper) (a : Element context) :
    a.reencode r = 0 ↔ a = 0 := by
  calc
    a.reencode r = 0 ↔
        (a.reencode r).denote f hz h1 ha hs hm hnat hsign = 0 :=
      (denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi (a.reencode r)).symm
    _ ↔ a.denote f hz h1 ha hs hm hnat hsign = 0 := by
      rw [denote_reencode f hz h1 ha hs hm hnat hsign hn hi r a]
    _ ↔ a = 0 := denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi a

include hn hi in
/-- Every dependent polynomial coefficient retains its selected value,
including coefficients omitted from the stored array. -/
theorem reencodePoly_coeff_value {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper)
    (p : DensePoly (Element context)) (i : Nat) :
    ((reencodePoly r p).coeff i).denote f hz h1 ha hs hm hnat hsign =
      (p.coeff i).denote f hz h1 ha hs hm hnat hsign := by
  rw [reencodePoly_coeff r
    (reencode_zero_iff f hz h1 ha hs hm hnat hsign hn hi r) p i]
  exact denote_reencode f hz h1 ha hs hm hnat hsign hn hi r (p.coeff i)

include hn hi in
/-- The interpreted dependent polynomial is unchanged by checked
coefficient transport. -/
theorem reencodePoly_interpret {context : Context E Ctx coeffSign parent}
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (r : SignDet.Reencoding context.root head lower upper)
    (p : DensePoly (Element context)) :
    interpret
      (fun a : Element (context.reencode r) => a.denote f hz h1 ha hs hm hnat hsign)
      (fun a => denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi a)
      (reencodePoly r p) =
    interpret
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      (fun a => denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi a) p := by
  apply Polynomial.ext
  intro i
  simpa only [coeff_interpret] using
    reencodePoly_coeff_value f hz h1 ha hs hm hnat hsign hn hi r p i

end Element
end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.rootValue_reencode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Context.rootValue_reencode
/-- info: 'Hex.RealClosure.Algebraic.Element.denote_reencode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.denote_reencode
/-- info: 'Hex.RealClosure.Algebraic.Element.sign_reencode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.sign_reencode
/-- info: 'Hex.RealClosure.Algebraic.Element.reencodePoly_interpret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.reencodePoly_interpret
