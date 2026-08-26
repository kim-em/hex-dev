/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Basic

public section

/-!
Mathlib transport for executable pseudo-division.

The main identity is the determinant-resultant version of one pseudo-division
step.  It is independent of Brown's later exact scalar quotients and is the
value invariant used by the subresultant correspondence proof.
-/
namespace Hex.DensePoly.PseudoDivMod

universe u

variable {R : Type u}

/-- The executable reconstruction identity transported to Mathlib
polynomials. -/
theorem reconstruct [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let q := (pseudoDivMod f g).1
    let r := (pseudoDivMod f g).2
    Polynomial.C (g.leadingCoeff ^ (f.size - g.size + 1)) *
        HexPolyMathlib.toPolynomial f =
      HexPolyMathlib.toPolynomial q * HexPolyMathlib.toPolynomial g +
        HexPolyMathlib.toPolynomial r := by
  have h := congrArg HexPolyMathlib.toPolynomial
    (pseudoDivMod_reconstruct f g hg hgf)
  simpa only [HexPolyMathlib.toPolynomial_scale,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add] using h

/-- A pseudo-quotient fits in the formal-degree gap required by Mathlib's
resultant row-operation theorem. -/
theorem quotient_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    (HexPolyMathlib.toPolynomial (pseudoDivMod f g).1).natDegree +
        (HexPolyMathlib.toPolynomial g).natDegree ≤
      (HexPolyMathlib.toPolynomial f).natDegree := by
  rw [HexPolyMathlib.natDegree_toPolynomial,
    HexPolyMathlib.natDegree_toPolynomial,
    HexPolyMathlib.natDegree_toPolynomial]
  have hq := pseudoDivMod_quotient_size_le f g
  have hgpos : 0 < g.size := by
    exact Nat.pos_of_ne_zero fun hg0 =>
      hg ((size_eq_zero_iff g).mp hg0)
  have hfpos : 0 < f.size := Nat.lt_of_lt_of_le hgpos hgf
  have hgdeg : g.degree?.getD 0 = g.size - 1 := by
    by_cases hg0 : g.size = 0
    · rw [(degree?_eq_none_iff g).2 hg0, Option.getD_none]
      omega
    · rw [degree?_eq_some_of_pos_size g (Nat.pos_of_ne_zero hg0),
        Option.getD_some]
  have hfdeg : f.degree?.getD 0 = f.size - 1 := by
    rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
  rw [hgdeg, hfdeg]
  by_cases hq0 : (pseudoDivMod f g).1.size = 0
  · rw [(degree?_eq_none_iff (pseudoDivMod f g).1).2 hq0,
      Option.getD_none]
    omega
  · rw [degree?_eq_some_of_pos_size (pseudoDivMod f g).1
        (Nat.pos_of_ne_zero hq0), Option.getD_some]
    omega

/-- A pseudo-remainder is zero or has strictly smaller Mathlib degree than
the nonzero divisor. The disjunction records Mathlib's default degree `0` for
the zero polynomial, including the constant-divisor case. -/
theorem remainder_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) :
    HexPolyMathlib.toPolynomial (pseudoDivMod f g).2 = 0 ∨
      (HexPolyMathlib.toPolynomial (pseudoDivMod f g).2).natDegree <
        (HexPolyMathlib.toPolynomial g).natDegree := by
  have hr := pseudoDivMod_remainder_lt f g hg
  have hgpos : 0 < g.size := by
    exact Nat.pos_of_ne_zero fun hg0 =>
      hg ((size_eq_zero_iff g).mp hg0)
  by_cases hr0 : (pseudoDivMod f g).2.size = 0
  · left
    rw [(size_eq_zero_iff (pseudoDivMod f g).2).mp hr0,
      HexPolyMathlib.toPolynomial_zero]
  · right
    rw [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial,
      degree?_eq_some_of_pos_size (pseudoDivMod f g).2
        (Nat.pos_of_ne_zero hr0),
      degree?_eq_some_of_pos_size g hgpos, Option.getD_some,
      Option.getD_some]
    omega

/-- One fraction-free pseudo-division step transports the formal-degree
resultant from `(f,g)` to `(g,r)`, including the Sylvester swap sign. -/
theorem resultant_step [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let r := (pseudoDivMod f g).2
    let F := HexPolyMathlib.toPolynomial f
    let G := HexPolyMathlib.toPolynomial g
    let P := HexPolyMathlib.toPolynomial r
    let n := F.natDegree
    let m := G.natDegree
    (g.leadingCoeff ^ (f.size - g.size + 1)) ^ m *
        Polynomial.resultant F G n m =
      (-1 : R) ^ (n * m) * Polynomial.resultant G P m n := by
  let q := (pseudoDivMod f g).1
  let r := (pseudoDivMod f g).2
  let F := HexPolyMathlib.toPolynomial f
  let G := HexPolyMathlib.toPolynomial g
  let P := HexPolyMathlib.toPolynomial r
  let Q := HexPolyMathlib.toPolynomial q
  let n := F.natDegree
  let m := G.natDegree
  let b := g.leadingCoeff ^ (f.size - g.size + 1)
  have hrec : Polynomial.C b * F = Q * G + P := by
    simpa only [b, F, G, P, Q, q, r] using reconstruct f g hg hgf
  have hrow : Polynomial.resultant (P + G * Q) G n m =
      Polynomial.resultant P G n m := by
    apply Polynomial.resultant_add_mul_left
    · simpa only [Q, G, n, m, q] using quotient_degree f g hg hgf
    · exact (show G.natDegree ≤ m by rfl)
  change b ^ m * Polynomial.resultant F G n m =
    (-1 : R) ^ (n * m) * Polynomial.resultant G P m n
  have hreorder : Q * G + P = P + G * Q := by ring
  calc
    b ^ m * Polynomial.resultant F G n m =
        Polynomial.resultant (Polynomial.C b * F) G n m := by
      rw [Polynomial.resultant_C_mul_left]
    _ = Polynomial.resultant (P + G * Q) G n m := by
      rw [hrec, hreorder]
    _ = Polynomial.resultant P G n m := hrow
    _ = (-1 : R) ^ (n * m) * Polynomial.resultant G P m n :=
      Polynomial.resultant_comm P G n m

/-- The pseudo-division resultant identity with the remainder returned to its
actual default degree. The compensating leading-coefficient power records the
formal-degree promotion explicitly. -/
theorem resultant_step_degree [CommRing R] [DecidableEq R]
    (f g : DensePoly R) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let r := (pseudoDivMod f g).2
    let F := HexPolyMathlib.toPolynomial f
    let G := HexPolyMathlib.toPolynomial g
    let P := HexPolyMathlib.toPolynomial r
    let n := F.natDegree
    let m := G.natDegree
    let k := P.natDegree
    (g.leadingCoeff ^ (f.size - g.size + 1)) ^ m *
        Polynomial.resultant F G n m =
      (-1 : R) ^ (n * m) *
        (g.leadingCoeff ^ (n - k) * Polynomial.resultant G P m k) := by
  let r := (pseudoDivMod f g).2
  let F := HexPolyMathlib.toPolynomial f
  let G := HexPolyMathlib.toPolynomial g
  let P := HexPolyMathlib.toPolynomial r
  let n := F.natDegree
  let m := G.natDegree
  let k := P.natDegree
  have hr : r.size < g.size := by
    simpa only [r] using pseudoDivMod_remainder_lt f g hg
  have hgpos : 0 < g.size := by
    exact Nat.pos_of_ne_zero fun hg0 =>
      hg ((size_eq_zero_iff g).mp hg0)
  have hfpos : 0 < f.size := Nat.lt_of_lt_of_le hgpos hgf
  have hk : k ≤ n := by
    change (HexPolyMathlib.toPolynomial r).natDegree ≤
      (HexPolyMathlib.toPolynomial f).natDegree
    rw [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial]
    by_cases hr0 : r.size = 0
    · rw [(degree?_eq_none_iff r).2 hr0, Option.getD_none,
        degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
      omega
    · rw [degree?_eq_some_of_pos_size r (Nat.pos_of_ne_zero hr0),
        degree?_eq_some_of_pos_size f hfpos, Option.getD_some,
        Option.getD_some]
      omega
  have hpromote : Polynomial.resultant G P m n =
      g.leadingCoeff ^ (n - k) * Polynomial.resultant G P m k := by
    have h := Polynomial.resultant_add_right_deg G P m k (n - k) le_rfl
    rw [Nat.add_sub_of_le hk] at h
    have hlc : G.coeff m = g.leadingCoeff := by
      simpa only [G, m, Polynomial.leadingCoeff] using
        HexPolyMathlib.leadingCoeff_toPolynomial g
    simpa only [m, k, hlc] using h
  calc
    (g.leadingCoeff ^ (f.size - g.size + 1)) ^ m *
          Polynomial.resultant F G n m =
        (-1 : R) ^ (n * m) * Polynomial.resultant G P m n := by
      simpa only [r, F, G, P, n, m] using resultant_step f g hg hgf
    _ = (-1 : R) ^ (n * m) *
          (g.leadingCoeff ^ (n - k) * Polynomial.resultant G P m k) := by
      rw [hpromote]

end Hex.DensePoly.PseudoDivMod
