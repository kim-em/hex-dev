/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.AlgebraicContext
public import HexRealClosureMathlib.AlgebraicClean
public import Mathlib.Data.Rat.Lemmas
public section

namespace Hex.RealClosure.BaseContext

private def Closed {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]
    (clean : K → Bool) : Prop :=
  clean 0 = true ∧ clean 1 = true ∧
  (∀ a b, clean a = true → clean b = true → clean (a + b) = true) ∧
  (∀ a b, clean a = true → clean b = true → clean (a - b) = true) ∧
  (∀ a b, clean a = true → clean b = true → clean (a * b) = true)

private theorem rational_closed : Closed (fun q : Rat => q.den == 1) := by
  have integral (q : Rat) (h : (q.den == 1) = true) : (q.num : Rat) = q :=
    Rat.coe_int_num_of_den_eq_one (by simpa using h)
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro a b ha hb
    rw [← integral a ha, ← integral b hb, ← Int.cast_add]
    simp
  · intro a b ha hb
    rw [← integral a ha, ← integral b hb, ← Int.cast_sub]
    simp
  · intro a b ha hb
    rw [← integral a ha, ← integral b hb]
    have he : ((a.num * b.num : Int) : Rat) = (a.num : Rat) * (b.num : Rat) := Int.cast_mul _ _
    rw [← he]
    simp only [Rat.den_intCast, beq_self_eq_true]

private theorem function_closed {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (clean : K → Bool) (hc : Closed clean) :
    Closed (fun f : RationalFn K => (f.den == 1) && f.num.toArray.all clean) := by
  obtain ⟨hz, h1, ha, hs, hm⟩ := hc
  let c : RationalFn K → Bool := fun f => (f.den == 1) && f.num.toArray.all clean
  have of_poly (p : DensePoly K) (hp : ∀ i, clean (p.coeff i) = true) :
      c (RationalFn.ofPoly p) = true := by
    change (((1 : DensePoly K) == 1) && p.toArray.all clean) = true
    simp only [beq_self_eq_true, Bool.true_and]
    exact (Algebraic.Clean.array_iff clean hz p).mpr hp
  have as_poly (f : RationalFn K) (hf : c f = true) : f = RationalFn.ofPoly f.num := by
    apply RationalFn.ext
    · rfl
    change f.den = 1
    simpa using (Bool.and_eq_true_iff.mp hf).1
  have coefficients (f : RationalFn K) (hf : c f = true) :
      ∀ i, clean (f.num.coeff i) = true :=
    (Algebraic.Clean.array_iff clean hz f.num).mp (Bool.and_eq_true_iff.mp hf).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply of_poly 0
    intro i; rw [DensePoly.coeff_zero]; exact hz
  · apply of_poly 1
    intro i
    change clean ((DensePoly.C (1 : K)).coeff i) = true
    rw [DensePoly.coeff_C]
    split
    · exact h1
    · exact hz
  · intro a b hac hbc
    have hap := coefficients a hac
    have hbp := coefficients b hbc
    rw [as_poly a hac, as_poly b hbc, ← RationalFn.ofPoly_add]
    exact of_poly _ (Algebraic.Clean.add clean hz ha _ _ hap hbp)
  · intro a b hac hbc
    have hap := coefficients a hac
    have hbp := coefficients b hbc
    rw [as_poly a hac, as_poly b hbc]
    have he : RationalFn.ofPoly a.num - RationalFn.ofPoly b.num =
        RationalFn.ofPoly (a.num - b.num) := by
      rw [Lean.Grind.Ring.sub_eq_add_neg, ← RationalFn.ofPoly_neg,
        ← RationalFn.ofPoly_add, ← Lean.Grind.Ring.sub_eq_add_neg]
    rw [he]
    exact of_poly _ (Algebraic.Clean.sub clean hz hs _ _ hap hbp)
  · intro a b hac hbc
    have hap := coefficients a hac
    have hbp := coefficients b hbc
    rw [as_poly a hac, as_poly b hbc, ← RationalFn.ofPoly_mul]
    exact of_poly _ (Algebraic.Clean.mul clean hz ha hm _ _ hap hbp)

private theorem RealChain.closed {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → OrderedFn.Oracle.Bounds}
    {sign : K → Int} (chain : RealChain registry K approx sign) : Closed chain.isClean := by
  induction chain with
  | base => exact rational_closed
  | step parent _ _ _ _ _ ih => exact function_closed parent.isClean ih

private theorem Chain.closed {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) : Closed chain.isClean := by
  induction chain with
  | real parent => exact parent.closed
  | infinitesimal parent ih => exact function_closed parent.isClean ih

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {sign : K → Int} (context : Context registry K sign)

/-- Recursive base cleanliness is closed under the operations used by monic division. -/
theorem Context.clean_zero : context.isClean 0 = true := context.chain.closed.1
theorem Context.clean_one : context.isClean 1 = true := context.chain.closed.2.1
theorem Context.clean_add (a b : K) (ha : context.isClean a = true)
    (hb : context.isClean b = true) : context.isClean (a + b) = true :=
  context.chain.closed.2.2.1 a b ha hb
theorem Context.clean_sub (a b : K) (ha : context.isClean a = true)
    (hb : context.isClean b = true) : context.isClean (a - b) = true :=
  context.chain.closed.2.2.2.1 a b ha hb
theorem Context.clean_mul (a b : K) (ha : context.isClean a = true)
    (hb : context.isClean b = true) : context.isClean (a * b) = true :=
  context.chain.closed.2.2.2.2 a b ha hb

namespace Element

theorem clean_zero : (0 : Element context).isClean = true := context.clean_zero
theorem clean_one : (1 : Element context).isClean = true := context.clean_one
theorem clean_add (a b : Element context) (ha : a.isClean = true)
    (hb : b.isClean = true) : (a + b).isClean = true :=
  context.clean_add a.stored b.stored ha hb
theorem clean_sub (a b : Element context) (ha : a.isClean = true)
    (hb : b.isClean = true) : (a - b).isClean = true :=
  context.clean_sub a.stored b.stored ha hb
theorem clean_mul (a b : Element context) (ha : a.isClean = true)
    (hb : b.isClean = true) : (a * b).isClean = true :=
  context.clean_mul a.stored b.stored ha hb

end Element

/-- Clean packing over an actual base derives every closure premise from
that immutable predecessor; constructors need no semantic law arguments. -/
theorem Context.pack_clean
    (root : SignDet.Descriptor (Element context) Signature Element.sign context.signature)
    (p : DensePoly (Element context)) (hp : p.toArray.all Element.isClean = true) :
    (Algebraic.Element.ofPoly (context := context.adjoin root) p).isClean = true := by
  apply Algebraic.Element.ofPoly_clean (context.adjoin root)
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using Element.clean_zero context
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using Element.clean_one context
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using Element.clean_add context
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using Element.clean_sub context
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using Element.clean_mul context
  · simpa only [Context.adjoin, Algebraic.Context.clean_adjoin] using hp

/-- info: 'Hex.RealClosure.BaseContext.Context.clean_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Context.clean_mul

end Hex.RealClosure.BaseContext
