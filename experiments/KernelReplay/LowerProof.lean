/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.LowerProbe
public import HexRealClosureMathlib.Algebraic
import all Init.Data.Zero

public section

namespace Hex.RealClosure.Algebraic.LowerProbe

open HexPolyMathlib.Interpret

variable {E K Ctx : Type} [Zero E] [DecidableEq E]
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
variable {context : Context E Ctx coeffSign parent}

include hn hi in
theorem evalCoefficients_value (cs : List (Element context)) (x : Element context) :
    context.evalPoly f hz h1 ha hs hm hnat hsign
        (DensePoly.evalCoeffList (cs.map Element.polynomial) x.polynomial) =
      (DensePoly.evalCoeffList cs x).denote f hz h1 ha hs hm hnat hsign := by
  induction cs with
  | nil =>
    change context.evalPoly f hz h1 ha hs hm hnat hsign 0 =
      (0 : Element context).denote f hz h1 ha hs hm hnat hsign
    exact (context.evalPoly_zero f hz h1 ha hs hm hnat hsign).trans
      (Element.denote_zero f hz h1 ha hs hm hnat hsign).symm
  | cons c cs ih =>
    simp only [List.map_cons, DensePoly.evalCoeffList,
      Element.denote_add f hz h1 ha hs hm hnat hsign hn hi,
      Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi]
    change (interpret f hz (_ * x.polynomial + c.polynomial)).eval _ = _
    rw [interpret_add f hz ha, Polynomial.eval_add, interpret_mul f hz ha hm,
      Polynomial.eval_mul]
    change context.evalPoly f hz h1 ha hs hm hnat hsign _ *
        x.denote f hz h1 ha hs hm hnat hsign + c.denote f hz h1 ha hs hm hnat hsign = _
    rw [ih]

include hn hi in
/-- The shared Horner calculation on stored representatives preserves the
value of ordinary algebraic evaluation. No injectivity of storage is used. -/
theorem evalPolynomial_value (p : DensePoly (Element context)) (x : Element context) :
    context.evalPoly f hz h1 ha hs hm hnat hsign (evalPolynomial p x) =
      (p.eval x).denote f hz h1 ha hs hm hnat hsign :=
  evalCoefficients_value f hz h1 ha hs hm hnat hsign hn hi p.toList x

include hz h1 ha hs hm hnat hsign hn hi in
/-- Supplied lower-level replay determines the ordinary evaluation's sign.
The interpretation assumptions belong to this correspondence proof, and are
absent from the executable reader's arguments. -/
theorem readEvalSign_sound (p : DensePoly (Element context)) (x : Element context)
    (claimed : Int) {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Hex.SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    (value : Int) (h : readEvalSign? p x claimed memo index = some value) :
    value = (p.eval x).sign := by
  unfold readEvalSign? at h
  cases ht : context.readSigns? (evalPolynomial p x) claimed memo index with
  | none => simp [ht] at h
  | some signs =>
    have hv : signs.value = value := by simpa only [ht, Option.map_some, Option.some.injEq] using h
    have checked := context.signPoly_checked f hz h1 ha hs hm hnat hsign hn hi
      (evalPolynomial p x) signs
    rw [context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi,
      evalPolynomial_value f hz h1 ha hs hm hnat hsign hn hi,
      ← Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi] at checked
    exact hv.symm.trans checked.symm

include hz h1 ha hs hm hnat hsign hn hi in
theorem readDifferenceSign_sound (a b : Element context) (claimed : Int)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Hex.SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    (value : Int) (h : readDifferenceSign? a b claimed memo index = some value) :
    value = (a - b).sign := by
  unfold readDifferenceSign? at h
  cases ht : context.readSigns? (a.polynomial - b.polynomial) claimed memo index with
  | none => simp [ht] at h
  | some signs =>
    have hv : signs.value = value := by simpa only [ht, Option.map_some, Option.some.injEq] using h
    have checked := context.signPoly_checked f hz h1 ha hs hm hnat hsign hn hi
      (a.polynomial - b.polynomial) signs
    rw [context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi,
      ← Element.denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi,
      ← Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi] at checked
    exact hv.symm.trans checked.symm

end Hex.RealClosure.Algebraic.LowerProbe

/-- info: 'Hex.RealClosure.Algebraic.LowerProbe.readEvalSign_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.LowerProbe.readEvalSign_sound

/-- info: 'Hex.RealClosure.Algebraic.LowerProbe.readDifferenceSign_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.LowerProbe.readDifferenceSign_sound
