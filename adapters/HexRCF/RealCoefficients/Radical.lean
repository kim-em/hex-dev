/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RadicalCheck
public import HexPolyTheory.Interpret
public import HexRealClosureTheory.TransportPower
public import HexRealAlgebraicTheory.Order
public import Mathlib.Basic.Real.Basic

public section

/-! A checked radical identity preserves the complete real root set. -/

namespace Hex.RCF.RealCoefficients

open HexPolyTheory.Interpret

private theorem interpret_natPow {E : Type u} [Zero E] [One E] [Add E] [Mul E]
    [DecidableEq E]
    (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (p : DensePoly E) (n : Nat) :
    interpret f hz (DensePoly.natPow p n) = (interpret f hz p) ^ n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
      conv => lhs; rw [DensePoly.natPow]
      by_cases hn : n = 0
      · subst n
        simp [interpret_one f hz h1]
      · rw [ite_eq_right hn]
        by_cases hOne : n = 1
        · rw [ite_eq_left hOne, hOne, pow_one]
        rw [ite_eq_right hOne]
        have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        by_cases heven : n % 2 = 0
        · rw [ite_eq_left heven, ih (n / 2) hlt (p * p),
            interpret_mul f hz ha hm]
          have hn2 : n = 2 * (n / 2) := by omega
          conv_rhs => rw [hn2, pow_mul, pow_two]
        · rw [ite_eq_right heven, interpret_mul f hz ha hm,
            ih (n / 2) hlt (p * p), interpret_mul f hz ha hm]
          have hn2 : n = 2 * (n / 2) + 1 := by omega
          conv_rhs => rw [hn2, pow_add, pow_one, pow_mul, pow_two]

namespace RadicalCert

/-- These two polynomial identities preserve the entire real root set.
The core need not be squarefree; accepted Sturm domains check that separately. -/
theorem roots_of_identities (product core quotient cofactor : Polynomial ℝ)
    (exponent : Nat) (first : product = core * quotient)
    (second : core ^ (exponent + 1) = quotient * cofactor) (x : ℝ) :
    core.IsRoot x ↔ product.IsRoot x := by
  have first := congrArg (Polynomial.eval x) first
  have second := congrArg (Polynomial.eval x) second
  simp only [Polynomial.eval_mul, Polynomial.eval_pow] at first second
  simp only [Polynomial.IsRoot]
  constructor
  · intro hc
    rw [first, hc, zero_mul]
  · intro hp
    rw [first] at hp
    rcases mul_eq_zero.mp hp with hc | hq
    · exact hc
    · rw [hq, zero_mul] at second
      exact (pow_eq_zero_iff (Nat.succ_ne_zero exponent)).mp second

/-- Both checked identities imply equality of the real root sets. This theorem
does not assume that the core is squarefree; the Sturm domain checker verifies
that independently before any root counts or sign queries are accepted. -/
theorem roots {E : Type u} {Ctx : Type v} [Zero E] [One E] [Add E] [Sub E] [Mul E]
    [DecidableEq E] [DecidableEq Ctx]
    (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (context : Ctx) (product : DensePoly E) (cert : RadicalCert E Ctx)
    (h : cert.check context product = true) (x : ℝ) :
    (interpret f hz cert.core).IsRoot x ↔ (interpret f hz product).IsRoot x := by
  obtain ⟨hfirst, hsecond, _⟩ := cert.check_identities context product h
  have hfirst := (sub_isZero f hz hs product (cert.core * cert.quotient)).mp hfirst
  rw [interpret_mul f hz ha hm] at hfirst
  have hsecond := (sub_isZero f hz hs
    (DensePoly.natPow cert.core (cert.exponent + 1))
    (cert.quotient * cert.cofactor)).mp hsecond
  rw [interpret_natPow f hz h1 ha hm, interpret_mul f hz ha hm] at hsecond
  exact roots_of_identities _ _ _ _ cert.exponent hfirst hsecond x

/-- The root identities also transport through a noninjective interpretation.
Only preservation of the arithmetic actually used is needed. -/
theorem roots_transport {E : Type u} {Ctx : Type v}
    [Zero E] [One E] [Add E] [Sub E] [Mul E] [DecidableEq E] [DecidableEq Ctx]
    (f : E → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (context : Ctx) (product : DensePoly E) (cert : RadicalCert E Ctx)
    (accepted : cert.check context product = true) (x : ℝ) :
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Hex.RealClosure.Transport.polynomial f cert.core)).IsRoot x ↔
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Hex.RealClosure.Transport.polynomial f product)).IsRoot x := by
  let read := Hex.RealClosure.Transport.polynomial f
  have mul (a b : DensePoly E) : read (a * b) = read a * read b :=
    Hex.RealClosure.Transport.Ring.polynomial_mul f h0 a b
      (fun _ _ _ _ => hm _ _) (fun _ _ _ _ => ha _ _)
  have powData (a : DensePoly E) (n : Nat) :
      Hex.RealClosure.Transport.PowerData f a n := by
    induction n using Nat.strongRecOn generalizing a with
    | ind n ih =>
      rw [Hex.RealClosure.Transport.PowerData]
      split
      · trivial
      · split
        · trivial
        · refine ⟨⟨fun _ _ _ _ => hm _ _, fun _ _ _ _ => ha _ _⟩,
            ih (n / 2) (by omega) (a * a), ?_⟩
          split
          · trivial
          · exact ⟨fun _ _ _ _ => hm _ _, fun _ _ _ _ => ha _ _⟩
  have power (a : DensePoly E) (n : Nat) : read (a.natPow n) = (read a).natPow n :=
    Hex.RealClosure.Transport.polynomial_natPow f h0 h1 a n (powData a n)
  have identity (a b : DensePoly E) (zero : (a - b).isZero = true) : read a = read b := by
    have same : a - b = 0 :=
      (DensePoly.size_eq_zero_iff _).mp ((DensePoly.isZero_eq_true_iff _).mp zero)
    have mapped := Hex.RealClosure.Transport.Ring.polynomial_sub f h0 a b (fun _ _ => hs _ _)
    have empty : read (0 : DensePoly E) = 0 := by
      apply DensePoly.ext_coeff
      intro i
      simp only [read, Hex.RealClosure.Transport.polynomial_coeff f h0, DensePoly.coeff_zero, h0]
    dsimp only [read] at empty
    rw [same, empty] at mapped
    apply DensePoly.ext_coeff
    intro i
    have coeff := congrArg (fun q : DensePoly ℝ => q.coeff i) mapped
    rw [DensePoly.coeff_zero, DensePoly.coeff_sub _ _ i (sub_self (0 : ℝ))] at coeff
    exact sub_eq_zero.mp coeff.symm
  obtain ⟨first, second, _⟩ := cert.check_identities context product accepted
  have first := identity _ _ first
  have second := identity _ _ second
  rw [mul] at first
  rw [power, mul] at second
  let into := interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
  have first := congrArg into first
  have second := congrArg into second
  dsimp only [into] at first second
  rw [interpret_mul (fun x : ℝ => x) (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)] at first
  rw [interpret_natPow (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl),
    interpret_mul (fun x : ℝ => x) (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)] at second
  exact roots_of_identities _ _ _ _ cert.exponent first second x

/-- The chosen real embedding reflects zero. -/
theorem zero_iff (a : RealAlgebraicNumber) : a.toReal = 0 ↔ a = 0 := by
  rw [← RealAlgebraicNumber.zero_toReal]
  exact RealAlgebraicNumber.toReal_injective.eq_iff

/-- The generic root transport applies to the canonical real-algebraic
coefficient operations used by formula specialization. The connection from a
specialized source atom to this interpretation is supplied by the formula
product bridge. -/
theorem roots_algebraic {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (product : DensePoly RealAlgebraicNumber)
    (cert : RadicalCert RealAlgebraicNumber Ctx)
    (h : cert.check context product = true) (x : ℝ) :
    (interpret RealAlgebraicNumber.toReal zero_iff cert.core).IsRoot x ↔
      (interpret RealAlgebraicNumber.toReal zero_iff product).IsRoot x := by
  exact cert.roots RealAlgebraicNumber.toReal
    zero_iff
    RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
    RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
    context product h x

end RadicalCert
end Hex.RCF.RealCoefficients
