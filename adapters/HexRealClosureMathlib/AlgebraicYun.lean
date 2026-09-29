/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Algebraic
public import HexRealClosureMathlib.YunInvariant

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

include hd in
/-- Yun's raw coefficient recurrence over one actual algebraic tower level
interprets exactly as the same recurrence over its ambient field. The
stored coefficients need no field laws as literal equalities. -/
theorem Context.mapYun (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) :
    Yun.Decomposition.map
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
      (Yun.decomposeRaw p) =
    Yun.decomposeRaw (DensePoly.Interpret.map
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p) := by
  exact Yun.map_decomposeRaw
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_div f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi) p

include hd in
/-- Yun's actual recurrence over a stored algebraic tower level passes the
full exact replay after coefficient interpretation in the ambient field. -/
theorem Context.checkYun (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) :
    Yun.check
      (DensePoly.Interpret.map
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p)
      (Yun.Decomposition.map
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        (Yun.decomposeRaw p)) = true := by
  rw [context.mapYun f hz h1 ha hs hm hnat hsign hn hi hd p]
  exact Yun.decompose_sound _

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.mapYun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.mapYun
/-- info: 'Hex.RealClosure.Algebraic.Context.checkYun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.checkYun
