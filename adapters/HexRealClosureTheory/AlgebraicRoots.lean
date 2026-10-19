/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Algebraic
public import HexRealClosureTheory.RootFactors

public section

namespace Hex.RealClosure.Algebraic

open HexPolyTheory.Interpret

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

include hn hi hd in
/-- Successful root assembly over stored algebraic values lists exactly the
roots of the interpreted input, with their original multiplicities. -/
theorem Context.assemble_spec (context : Context E Ctx coeffSign parent)
    {NextCtx : Type z} [DecidableEq NextCtx] (key : NextCtx)
    (p : DensePoly (Element context))
    {out : List (Roots.Entry Element.sign key)}
    (accepted : Roots.assemble Element.sign key p = .ok (.finite out))
    (x : K) (label : Nat) :
    (∃ entry ∈ out,
      entry.value (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
        (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi) = x ∧
      entry.multiplicity = label) ↔
    (interpret (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p).IsRoot x ∧
      label = (interpret (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p).rootMultiplicity x := by
  exact Roots.assemble_spec
    (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_div f hz h1 ha hs hm hnat hsign hn hi hd)
    p accepted x label

include hn hi hd in
/-- Successful root assembly over stored algebraic values emits each
mathematical root once. -/
theorem Context.assemble_nodup (context : Context E Ctx coeffSign parent)
    {NextCtx : Type z} [DecidableEq NextCtx] (key : NextCtx)
    (p : DensePoly (Element context))
    {out : List (Roots.Entry Element.sign key)}
    (accepted : Roots.assemble Element.sign key p = .ok (.finite out)) :
    (out.map fun entry =>
      entry.value (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
        (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi)).Nodup := by
  exact Roots.assemble_nodup
    (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_neg f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_inv f hz h1 ha hs hm hnat hsign hn hi hd)
    (Element.denote_div f hz h1 ha hs hm hnat hsign hn hi hd)
    p accepted

/-- The separate all-roots result over actual algebraic coefficients is
returned exactly for a semantically zero input. -/
theorem Context.assemble_all (context : Context E Ctx coeffSign parent)
    {NextCtx : Type z} [DecidableEq NextCtx] (key : NextCtx)
    (p : DensePoly (Element context)) :
    Roots.assemble Element.sign key p = .ok .all ↔
      interpret (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi) p = 0 :=
  Roots.assemble_all
    (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    key p

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.assemble_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.assemble_spec
/-- info: 'Hex.RealClosure.Algebraic.Context.assemble_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.assemble_nodup
/-- info: 'Hex.RealClosure.Algebraic.Context.assemble_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.assemble_all
