/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PseudoDiv

public section

/-! Recorded pseudo-division scales and the plain fraction-free gcd sequence.
No coefficient division or Bézout accumulator is used. -/
namespace Hex.DensePoly

universe u
variable {R : Type u} [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]

/-- The multiplier, quotient and remainder of a pseudo-division. -/
structure PseudoResult (R : Type u) [Zero R] [DecidableEq R] where
  multiplier : R
  quotient : DensePoly R
  remainder : DensePoly R

/-- The fixed leading-coefficient exponent, including the zero/smaller-input cases. -/
@[expose] def pseudoExponent (p q : DensePoly R) : Nat :=
  if q.isZero || p.size < q.size then 0 else p.size - q.size + 1

/-- Pseudo-division with its actual scalar multiplier. The quotient and remainder
reuse `pseudoDivMod`. On a zero divisor or a smaller dividend the multiplier is one. -/
@[expose] def pseudoDiv (p q : DensePoly R) : PseudoResult R :=
  let qr := pseudoDivMod p q
  ⟨npowRec (pseudoExponent p q) q.leadingCoeff, qr.1, qr.2⟩

@[simp] theorem pseudoDiv_zero_right (p : DensePoly R) :
    pseudoDiv p 0 = ⟨1, 0, p⟩ := by
  rfl

/-- An already smaller input requires no cancellation or scaling. -/
theorem pseudoDiv_of_size_lt (p q : DensePoly R) (h : p.size < q.size) :
    pseudoDiv p q = ⟨1, 0, p⟩ := by
  simp only [pseudoDiv, pseudoExponent, h, decide_true, Bool.or_true, ↓reduceIte, npowRec,
    pseudoDivMod_of_size_lt p q h]

/-- Choose a positive multiplier by negating all three outputs together when
necessary. The leading-coefficient sign and exponent parity determine the
correction, avoiding a sign query on the larger computed power. -/
@[expose] def positivePseudoDiv [Neg R] (sign : R → Int) (p q : DensePoly R) : PseudoResult R :=
  let r := pseudoDiv p q
  if pseudoExponent p q % 2 = 1 ∧ sign q.leadingCoeff < 0 then
    ⟨-r.multiplier, -r.quotient, -r.remainder⟩ else r

omit [One R] [Add R] [Mul R] in
private theorem size_neg_le (p : DensePoly R) : (-p).size ≤ p.size := by
  change (sub 0 p).size ≤ p.size
  rw [sub_eq_subImpl]
  unfold subImpl
  apply Nat.le_trans (size_ofCoeffs_le _)
  simp only [Array.size_ofFn, size_zero, Nat.zero_max, Nat.le_refl]

/-- Sign correction cannot increase the stored remainder size, even before
any interpretation or algebraic laws are supplied. -/
theorem positivePseudoDiv_remainder_lt [Neg R] (sign : R → Int)
    (p q : DensePoly R) (hq : q ≠ 0) :
    (positivePseudoDiv sign p q).remainder.size < q.size := by
  simp only [positivePseudoDiv]
  split
  · exact Nat.lt_of_le_of_lt (size_neg_le _) (pseudoDivMod_remainder_lt p q hq)
  · exact pseudoDivMod_remainder_lt p q hq

/-- Plain pseudo-gcd. Its recursion decreases the stored size of the second
polynomial, with no user bound and no Bézout polynomials. Correctness over a
domain is a fraction-field gcd statement, not a gcd statement in `R[X]`. -/
@[expose] def pseudoGcd (p q : DensePoly R) : DensePoly R :=
  if _h : q.isZero then p else pseudoGcd q (pseudoDivMod p q).2
termination_by q.size
decreasing_by
  apply pseudoDivMod_remainder_lt
  intro hq
  subst q
  have ht : (0 : DensePoly R).isZero = true := rfl
  rw [ht] at _h
  contradiction

@[simp] theorem pseudoGcd_zero_right (p : DensePoly R) : pseudoGcd p 0 = p := by
  rw [pseudoGcd]
  rfl

/-- The recursive equation records an actual division step and its strict descent. -/
theorem pseudoGcd_step (p q : DensePoly R) (hq : q ≠ 0) :
    pseudoGcd p q = pseudoGcd q (pseudoDivMod p q).2 := by
  rw [pseudoGcd]
  have hn : q.isZero = false := by
    simp only [isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h))
  simp only [hn, Bool.false_eq_true, ↓reduceDIte]

@[simp] theorem pseudoGcd_zero_left (q : DensePoly R) : pseudoGcd 0 q = q := by
  by_cases hq : q = 0
  · subst q
    exact pseudoGcd_zero_right _
  · have hsize : (0 : DensePoly R).size < q.size := by
      rw [size_zero]
      exact Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h))
    rw [pseudoGcd_step _ _ hq, pseudoDivMod_of_size_lt _ _ hsize, pseudoGcd_zero_right]

/-- A genuine coefficient domain has a nonzero pseudo-division multiplier;
no division or field structure on the coefficient type is involved. -/
theorem pseudoDiv_multiplier_ne_zero (hone : (1 : R) ≠ 0)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → a * b ≠ 0)
    (p q : DensePoly R) (hq : q ≠ 0) : (pseudoDiv p q).multiplier ≠ 0 := by
  have hlead : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero_of_pos_size q
    (Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h)))
  have hpow (n : Nat) : npowRec n q.leadingCoeff ≠ 0 := by
    induction n with
    | zero => exact hone
    | succ n ih => exact hmul _ _ ih hlead
  exact hpow (pseudoExponent p q)

/-- The remainder bound holds without algebraic assumptions on stored coefficients. -/
theorem pseudoDiv_remainder_lt (p q : DensePoly R) (hq : q ≠ 0) :
    (pseudoDiv p q).remainder.size < q.size :=
  pseudoDivMod_remainder_lt p q hq

private theorem npowRec_eq_pow {S : Type u} [Lean.Grind.CommRing S] (a : S) (n : Nat) :
    npowRec n a = a ^ n := by
  induction n with
  | zero => exact (Lean.Grind.Semiring.pow_zero a).symm
  | succ n ih => rw [npowRec, ih, Lean.Grind.Semiring.pow_succ]

/-- The recorded operation-only power agrees with the ring's natural power. -/
theorem pseudoDiv_multiplier {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    (pseudoDiv p q).multiplier = q.leadingCoeff ^ pseudoExponent p q :=
  npowRec_eq_pow _ _

/-- Reconstruction uses exactly the multiplier returned by `pseudoDiv`, including
zero dividends and dividends smaller than the divisor. -/
theorem pseudoDiv_reconstruct {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (hq : q ≠ 0) :
    scale (pseudoDiv p q).multiplier p =
      (pseudoDiv p q).quotient * q + (pseudoDiv p q).remainder := by
  have hqz : q.isZero = false := (isZero_eq_false_iff q).mpr
    (Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h)))
  by_cases hlt : p.size < q.size
  · have hone : scale (1 : S) p = p := by
      apply ext_coeff
      intro i
      simp only [coeff_scale_semiring, Lean.Grind.Semiring.one_mul]
    simp only [pseudoDiv, pseudoExponent, hqz, hlt, decide_true, Bool.false_or,
      ↓reduceIte, npowRec, pseudoDivMod_of_size_lt p q hlt,
      Lean.Grind.Semiring.zero_mul, zero_add_semiring, hone]
  · simpa only [pseudoDiv, pseudoExponent, hqz, hlt, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, npowRec_eq_pow] using
      pseudoDivMod_reconstruct p q hq (Nat.le_of_not_gt hlt)

end Hex.DensePoly
