/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RadicalCheck
public import HexPolyMathlib.Interpret
public import HexRealAlgebraicMathlib.Order
public import Mathlib.Basic.Real.Basic

public section

/-! A checked radical identity preserves the complete real root set. -/

namespace Hex.RCF.RealCoefficients

open HexPolyMathlib.Interpret

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
  have hfirstx := congrArg (Polynomial.eval x) hfirst
  have hsecondx := congrArg (Polynomial.eval x) hsecond
  simp only [Polynomial.eval_mul, Polynomial.eval_pow] at hfirstx hsecondx
  simp only [Polynomial.IsRoot]
  constructor
  · intro hc
    rw [hfirstx, hc, zero_mul]
  · intro hp
    rw [hfirstx] at hp
    rcases mul_eq_zero.mp hp with hc | hq
    · exact hc
    · rw [hq, zero_mul] at hsecondx
      exact (pow_eq_zero_iff (Nat.succ_ne_zero cert.exponent)).mp hsecondx

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
