/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRoots.Prec
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Discriminant
public import HexPolyZMathlib.Mignotte
public import HexPolyZMathlib.MahlerSeparation

public section

/-!
# Separation bounds for `rootBound` and `sepPrec`

This module proves soundness of the closed-form integer estimates that drive
real-root isolation in `HexRealRoots.Prec`, against the Mathlib casts
`toPolyℝ`/`toPolyℂ` of the executable integer polynomial `p`.

* `rootBound_bounds_roots`: every real root of a nonzero `toPolyℝ p` lies
  strictly inside the power-of-two Cauchy bound `Hex.rootBound p`, via Cauchy's
  bound (`Polynomial.IsRoot.norm_lt_cauchyBound`) and the conservative
  power-of-two rounding of `rootBound`. The supporting numeric lemma
  `le_two_pow_ceilLog2Nat` characterises the ceiling logarithm, and
  `toReal_twoPow` evaluates the dyadic power of two.

The Mahler separation bound `sepPrec_separates` — distinct complex roots of a
squarefree `p` are more than `4 · 2^{-sepPrec p}` apart — combines the generic
discriminant/Vandermonde analysis in `HexPolyZMathlib.MahlerSeparation` with
Landau's inequality and the executable `sepPrec` exponent arithmetic retained
in this companion.
-/

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-- Real value of a dyadic number, through `Dyadic.toRat`. -/
def Dyadic.toReal (x : Dyadic) : ℝ := (x.toRat : ℝ)

/-- The real cast of an executable integer polynomial. -/
abbrev toPolyℝ (p : Hex.ZPoly) : Polynomial ℝ :=
  (toPolynomial p).map (Int.castRingHom ℝ)

/-- The complex cast of an executable integer polynomial. -/
abbrev toPolyℂ (p : Hex.ZPoly) : Polynomial ℂ :=
  (toPolynomial p).map (Int.castRingHom ℂ)

/-! ### Dyadic and ceiling-logarithm helpers -/

/-- `toRat` turns a left shift into multiplication by a power of two. -/
theorem toRat_shiftLeft (x : Dyadic) (i : Int) :
    (x <<< i).toRat = x.toRat * (2 : ℚ) ^ i := by
  cases x with
  | zero => simp [HShiftLeft.hShiftLeft, Dyadic.shiftLeft]
  | ofOdd n k hn =>
    show (Dyadic.ofOdd n (k - i) hn).toRat = _
    rw [Dyadic.toRat_ofOdd_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow,
      show -(k - i) = -k + i by ring, zpow_add₀ (by norm_num)]
    ring

/-- `toRat` turns a right shift into multiplication by a negative power of two. -/
theorem toRat_shiftRight (x : Dyadic) (i : Int) :
    (x >>> i).toRat = x.toRat * (2 : ℚ) ^ (-i) := by
  cases x with
  | zero => simp [HShiftRight.hShiftRight, Dyadic.shiftRight]
  | ofOdd n k hn =>
    show (Dyadic.ofOdd n (k + i) hn).toRat = _
    rw [Dyadic.toRat_ofOdd_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow,
      show -(k + i) = -k + -i by ring, zpow_add₀ (by norm_num)]
    ring

/-- The real value of an integer dyadic is the integer cast. -/
@[simp] theorem toReal_ofInt (n : Int) : Dyadic.toReal (Dyadic.ofInt n) = (n : ℝ) := by
  unfold Dyadic.toReal
  rw [show Dyadic.ofInt n = ((n : Int) : Dyadic) from rfl, Dyadic.toRat_intCast]
  push_cast; ring

/-- `Hex.twoPow k` has real value `2 ^ k`. -/
@[simp] theorem toReal_twoPow (k : Int) : Dyadic.toReal (Hex.twoPow k) = (2 : ℝ) ^ k := by
  have h1 : (1 : Dyadic).toRat = 1 := by
    rw [show (1 : Dyadic) = ((1 : Int) : Dyadic) from rfl, Dyadic.toRat_intCast]; norm_num
  unfold Dyadic.toReal Hex.twoPow
  rw [toRat_shiftLeft, h1, one_mul]
  push_cast
  norm_cast

/-- The real value of a left shift is multiplication by a power of two. -/
theorem toReal_shiftLeft (x : Dyadic) (i : Int) :
    Dyadic.toReal (x <<< i) = Dyadic.toReal x * (2 : ℝ) ^ i := by
  unfold Dyadic.toReal
  rw [toRat_shiftLeft]; push_cast; ring

/-- The real value of a right shift is multiplication by a negative power of two. -/
theorem toReal_shiftRight (x : Dyadic) (i : Int) :
    Dyadic.toReal (x >>> i) = Dyadic.toReal x * (2 : ℝ) ^ (-i) := by
  unfold Dyadic.toReal
  rw [toRat_shiftRight]; push_cast; ring

/-- The real value of the dyadic `n / 2ⁱ` (an integer shifted right by `i` bits). -/
@[simp] theorem toReal_ofInt_shiftRight (n i : Int) :
    Dyadic.toReal (Dyadic.ofInt n >>> i) = (n : ℝ) * (2 : ℝ) ^ (-i) := by
  rw [toReal_shiftRight, toReal_ofInt]

/-- `ceilLog2Nat m` is a base-two ceiling: `m ≤ 2 ^ (ceilLog2Nat m)`. -/
theorem le_two_pow_ceilLog2Nat (m : Nat) : m ≤ 2 ^ Hex.ceilLog2Nat m := by
  unfold Hex.ceilLog2Nat
  by_cases hm : m ≤ 1
  · rw [if_pos hm]; simpa using hm
  · rw [if_neg hm]
    have hm2 : 2 ≤ m := by omega
    have hne : m - 1 ≠ 0 := by omega
    have := (Nat.log2_lt hne).1 (Nat.lt_succ_self (m - 1).log2)
    omega

/-- The `List.range` fold used by `rootBound` to compute the maximum absolute
non-leading coefficient equals the corresponding `Finset.sup`. -/
theorem range_foldl_max_eq_finset_sup (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => max acc (g i)) 0 = (Finset.range m).sup g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih, Finset.range_add_one, Finset.sup_insert]
    exact Nat.max_comm _ _

/-! ### Cast bridges to the executable polynomial -/

@[simp] theorem coeff_toPolyℝ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℝ p).coeff n = (p.coeff n : ℝ) := by
  simp [toPolyℝ]

/-- Evaluating the real cast at `x` is the degree-indexed sum of the integer
coefficients cast to `ℝ`. For a literal `ofCoeffs` this unfolds via
`Finset.sum_range_succ` into an explicit polynomial in `x`; combined with
`Polynomial.IsRoot`, it turns a root goal into a plain equation
`ring`/`norm_num` can discharge. -/
theorem eval_toPolyℝ (p : Hex.ZPoly) (x : ℝ) :
    (toPolyℝ p).eval x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℝ) * x ^ i := by
  rw [toPolyℝ, Polynomial.eval_map, HexPolyMathlib.eval₂_toPolynomial]
  simp

theorem natDegree_toPolyℝ (p : Hex.ZPoly) :
    (toPolyℝ p).natDegree = p.degree?.getD 0 := by
  rw [toPolyℝ, Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℝ)),
    HexPolyMathlib.natDegree_toPolynomial]

/-- Coefficients of the complex cast are the complex casts of the integer
coefficients. -/
@[simp] theorem coeff_toPolyℂ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℂ p).coeff n = (p.coeff n : ℂ) := by
  simp [toPolyℂ]

/-- The complex cast preserves the natural degree. -/
theorem natDegree_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℂ p).natDegree = p.degree?.getD 0 := by
  rw [toPolyℂ, Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (Int.castRingHom ℂ)),
    HexPolyMathlib.natDegree_toPolynomial]

/-- The complex cast preserves the leading coefficient. -/
theorem leadingCoeff_toPolyℂ (p : Hex.ZPoly) :
    (toPolyℂ p).leadingCoeff = (p.leadingCoeff : ℂ) := by
  rw [toPolyℂ, Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective_int (Int.castRingHom ℂ)), HexPolyMathlib.leadingCoeff_toPolynomial]
  simp

/-- The complex cast is the map of the integer polynomial. -/
theorem toPolyℂ_eq_map (p : Hex.ZPoly) :
    toPolyℂ p = (toPolynomial p).map (Int.castRingHom ℂ) := rfl

/-! ### `rootBound` soundness -/

/-- The power-of-two Cauchy bound `Hex.rootBound p` dominates Cauchy's bound. -/
theorem cauchyBound_le_rootBound (p : Hex.ZPoly) :
    ((toPolyℝ p).cauchyBound : ℝ) ≤ Dyadic.toReal (Hex.rootBound p) := by
  set q := toPolyℝ p with hq
  -- The zero-degree case: Cauchy's bound is `1`, and so is `rootBound`.
  rcases hd : p.degree? with _ | d
  · -- `degree? = none`: `natDegree q = 0`, `cauchyBound q = 1`.
    have hnd : q.natDegree = 0 := by simp [hq, natDegree_toPolyℝ, hd]
    have hcb : q.cauchyBound = 1 := by simp [Polynomial.cauchyBound, hnd]
    rw [hcb, Hex.rootBound_of_degree?_none hd, toReal_ofInt]; norm_num
  · rcases d with _ | d'
    · have hnd : q.natDegree = 0 := by simp [hq, natDegree_toPolyℝ, hd]
      have hcb : q.cauchyBound = 1 := by simp [Polynomial.cauchyBound, hnd]
      rw [hcb, Hex.rootBound_of_degree?_zero hd, toReal_ofInt]; norm_num
    · -- The general branch of `rootBound`.
      have hnd : q.natDegree = d' + 1 := by simp [hq, natDegree_toPolyℝ, hd]
      -- The stored size is `d + 1 > 0`, so the leading coefficient is nonzero.
      have hsize : 0 < p.size := by
        by_contra h
        have hz : p.size = 0 := by omega
        rw [← Hex.DensePoly.degree?_eq_none_iff] at hz
        rw [hz] at hd; simp at hd
      have hlc0 : p.leadingCoeff ≠ 0 :=
        Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size p hsize
      set c := p.leadingCoeff.natAbs with hc
      have hc0 : c ≠ 0 := by simp [hc, Int.natAbs_eq_zero, hlc0]
      -- `A`, the maximum absolute non-leading coefficient.
      set A := (List.range (d' + 1)).foldl (fun acc i => max acc (p.coeff i).natAbs) 0 with hA
      have hAsup : A = (Finset.range (d' + 1)).sup (fun i => (p.coeff i).natAbs) := by
        rw [hA, range_foldl_max_eq_finset_sup]
      -- `rootBound p = twoPow (ceilLog2Nat (A / c + 2))`.
      have hrb : Hex.rootBound p = Hex.twoPow (Hex.ceilLog2Nat (A / c + 2) : Int) :=
        Hex.rootBound_of_degree?_pos hd
      -- The leading coefficient of `q`.
      have hqlc : q.leadingCoeff = (p.leadingCoeff : ℝ) := by
        rw [hq, toPolyℝ, Polynomial.leadingCoeff_map_of_injective
          (RingHom.injective_int (Int.castRingHom ℝ)), HexPolyMathlib.leadingCoeff_toPolynomial]
        simp
      -- Bound `cauchyBound q` in `ℝ≥0` by `A / ‖lc‖₊ + 1`.
      have hcbound : q.cauchyBound ≤ (A : NNReal) / ‖q.leadingCoeff‖₊ + 1 := by
        rw [Polynomial.cauchyBound]
        gcongr
        rw [hnd]
        apply Finset.sup_le
        intro i hi
        rw [coeff_toPolyℝ]
        have hnn : ‖(p.coeff i : ℝ)‖₊ = ((p.coeff i).natAbs : NNReal) := by
          rw [← Real.nnnorm_natCast ((p.coeff i).natAbs), nnnorm_natAbs]
        rw [hnn, hAsup]
        exact_mod_cast Finset.le_sup (f := fun i => (p.coeff i).natAbs) hi
      -- Push to `ℝ`.
      have hlcnorm : ‖q.leadingCoeff‖ = (c : ℝ) := by
        rw [hqlc, hc, ← norm_natAbs]; simp
      calc (q.cauchyBound : ℝ)
          ≤ (((A : NNReal) / ‖q.leadingCoeff‖₊ + 1 : NNReal) : ℝ) := by exact_mod_cast hcbound
        _ = (A : ℝ) / (c : ℝ) + 1 := by
            push_cast [NNReal.coe_div]
            rw [hlcnorm]
        _ ≤ Dyadic.toReal (Hex.rootBound p) := by
            rw [hrb, toReal_twoPow]
            have hc0' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc0
            -- `A / c < A / c (nat) + 1`, and `A / c (nat) + 2 ≤ 2 ^ ceilLog2Nat`.
            have hfloor : (A : ℝ) / (c : ℝ) ≤ (A / c : Nat) + 1 := by
              rw [div_le_iff₀ hc0']
              have : (A : ℝ) < ((A / c : Nat) + 1) * (c : ℝ) := by
                have hlt : A < (A / c + 1) * c := by
                  have h1 := Nat.div_add_mod A c
                  have h2 := Nat.mod_lt A (Nat.pos_of_ne_zero hc0)
                  nlinarith [h1, h2]
                calc (A : ℝ) < (((A / c + 1) * c : Nat) : ℝ) := by exact_mod_cast hlt
                  _ = ((A / c : Nat) + 1) * (c : ℝ) := by push_cast; ring
              linarith
            have hpow : ((A / c + 2 : Nat) : ℝ) ≤ (2 : ℝ) ^ (Hex.ceilLog2Nat (A / c + 2) : Int) := by
              rw [zpow_natCast]
              exact_mod_cast le_two_pow_ceilLog2Nat (A / c + 2)
            have : (A : ℝ) / (c : ℝ) + 1 ≤ ((A / c + 2 : Nat) : ℝ) := by push_cast; linarith
            linarith

/-- **Cauchy root bound.** Every real root of a nonzero `toPolyℝ p` lies strictly
inside the power-of-two bound `Hex.rootBound p`. -/
theorem rootBound_bounds_roots (p : Hex.ZPoly) (hp : toPolyℝ p ≠ 0) :
    ∀ r : ℝ, (toPolyℝ p).IsRoot r → |r| < Dyadic.toReal (Hex.rootBound p) := by
  intro r hr
  have hlt : (‖r‖₊ : ℝ) < ((toPolyℝ p).cauchyBound : ℝ) := by
    exact_mod_cast hr.norm_lt_cauchyBound hp
  have hle := cauchyBound_le_rootBound p
  have : |r| = (‖r‖₊ : ℝ) := by simp [Real.norm_eq_abs]
  rw [this]
  linarith

/-! ### Mahler's root-separation bound

The remainder of this file proves `sepPrec_separates`. The classical proof
(Mahler 1964; textbook form Mignotte 1982) bounds the Vandermonde determinant of
the roots two ways: the discriminant root-product gives `|disc| = |lc|^{2n-2} ·
|det V|²`, while an isolating column operation plus Hadamard's inequality bounds
`|lc|^{n-1} · |det V|` by `n^{(n+2)/2} · M(p)^{n-1} · ‖z₁ − z₂‖`. Combined with
`|disc| ≥ 1` and Landau's inequality `M(p) ≤ L`, this yields the separation.

The generic building blocks and Vandermonde assembly now live in
`HexPolyZMathlib.MahlerSeparation`; the closed-form exponent and executable
specialization remain below. -/

/-! The following forwarding theorems intentionally preserve the qualified
`HexRealRootsMathlib` API from before the shared-module extraction. New proofs
should use the `HexPolyZMathlib` declarations directly. -/

/-- Compatibility forwarding theorem for the generic divided-difference bound. -/
theorem norm_pow_sub_pow_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ (i : ℝ) * C ^ (i - 1) * ‖y - x‖ :=
  HexPolyZMathlib.norm_pow_sub_pow_le hx hy hC i

/-- Compatibility forwarding theorem for the ordinary Vandermonde-column bound. -/
theorem sqrt_sum_pow_sq_le (a : ℂ) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2) ≤
      Real.sqrt N * (max 1 ‖a‖) ^ (N - 1) :=
  HexPolyZMathlib.sqrt_sum_pow_sq_le a N

/-- Compatibility forwarding theorem for the differenced Vandermonde-column bound. -/
theorem sqrt_sum_sub_pow_sq_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2) ≤
      C ^ (N - 2) * ‖y - x‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) :=
  HexPolyZMathlib.sqrt_sum_sub_pow_sq_le hx hy hC N

/-- Compatibility forwarding theorem for the sum-of-squares estimate. -/
theorem sqrt_sum_sq_le (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) ≤ Real.sqrt N ^ 3 :=
  HexPolyZMathlib.sqrt_sum_sq_le N

/-- Compatibility forwarding theorem for the isolating-column determinant bound. -/
theorem norm_det_vandermonde_le {N : ℕ} (hN : 2 ≤ N) (c : ℂ) (α : Fin N → ℂ)
    {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁) (hle : ‖α i₀‖ ≤ ‖α i₁‖) :
    ‖c‖ ^ (N - 1) * ‖(Matrix.vandermonde α).det‖ ≤
      Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (‖c‖ * ∏ j, max 1 ‖α j‖) ^ (N - 1) * ‖α i₁ - α i₀‖ :=
  HexPolyZMathlib.norm_det_vandermonde_le hN c α hne hle

/-- Compatibility forwarding theorem for the off-diagonal root-product identity. -/
theorem norm_prod_roots_eq_sq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) :
    ‖((Multiset.map α Finset.univ.val).map
        (fun x => (((Multiset.map α Finset.univ.val).erase x).map
          (fun y => x - y)).prod)).prod‖ = ‖(Matrix.vandermonde α).det‖ ^ 2 :=
  HexPolyZMathlib.norm_prod_roots_eq_sq α hα

/-- Compatibility forwarding theorem for the discriminant/Vandermonde identity. -/
theorem norm_discr_eq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) {f : ℂ[X]}
    (hf : 0 < f.degree) (hsplit : f.Splits)
    (hroots : f.roots = Multiset.map α Finset.univ.val) :
    ‖f.discr‖ = ‖f.leadingCoeff‖ ^ (2 * f.natDegree - 2) *
      ‖(Matrix.vandermonde α).det‖ ^ 2 :=
  HexPolyZMathlib.norm_discr_eq α hα hf hsplit hroots


/-- The closed-form separation exponent dominates the analytic bound:
`√n^{n+2} · L^{n-1} ≤ 2^E` where `E = ((n+2)·⌈log₂ n⌉ + 1)/2 + (n-1)·⌈log₂ L⌉`. -/
theorem pow_le_two_pow_sepExp (n L : ℕ) :
    Real.sqrt n ^ (n + 2) * (L : ℝ) ^ (n - 1)
      ≤ 2 ^ (((n + 2) * Hex.ceilLog2Nat n + 1) / 2 + (n - 1) * Hex.ceilLog2Nat L) := by
  set cn := Hex.ceilLog2Nat n with hcn
  set cL := Hex.ceilLog2Nat L with hcL
  have hn : (n : ℝ) ≤ 2 ^ cn := by exact_mod_cast le_two_pow_ceilLog2Nat n
  have hL : (L : ℝ) ≤ 2 ^ cL := by exact_mod_cast le_two_pow_ceilLog2Nat L
  -- The `L` factor.
  have hLpow : (L : ℝ) ^ (n - 1) ≤ 2 ^ ((n - 1) * cL) := by
    calc (L : ℝ) ^ (n - 1) ≤ ((2 : ℝ) ^ cL) ^ (n - 1) :=
          pow_le_pow_left₀ (Nat.cast_nonneg L) hL (n - 1)
      _ = 2 ^ ((n - 1) * cL) := by rw [← pow_mul, Nat.mul_comm]
  -- The `√n` factor, via squaring.
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt n ^ (n + 2) := by positivity
  have hkey : (n : ℝ) ^ (n + 2) ≤ 2 ^ (2 * (((n + 2) * cn + 1) / 2)) := by
    calc (n : ℝ) ^ (n + 2) ≤ ((2 : ℝ) ^ cn) ^ (n + 2) :=
          pow_le_pow_left₀ (Nat.cast_nonneg n) hn (n + 2)
      _ = 2 ^ ((n + 2) * cn) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (2 * (((n + 2) * cn + 1) / 2)) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  have hnpow : Real.sqrt n ^ (n + 2) ≤ 2 ^ (((n + 2) * cn + 1) / 2) := by
    have hsq : (Real.sqrt n ^ (n + 2)) ^ 2 ≤ (2 ^ (((n + 2) * cn + 1) / 2)) ^ 2 := by
      have e1 : (Real.sqrt n ^ (n + 2)) ^ 2 = (n : ℝ) ^ (n + 2) := by
        rw [← pow_mul, show (n + 2) * 2 = 2 * (n + 2) by ring, pow_mul,
          Real.sq_sqrt (Nat.cast_nonneg n)]
      have e2 : ((2 : ℝ) ^ (((n + 2) * cn + 1) / 2)) ^ 2
          = 2 ^ (2 * (((n + 2) * cn + 1) / 2)) := by rw [← pow_mul, Nat.mul_comm]
      rw [e1, e2]; exact hkey
    have h2nn : (0 : ℝ) ≤ 2 ^ (((n + 2) * cn + 1) / 2) := by positivity
    nlinarith [hsq, hsqrtnn, h2nn]
  calc Real.sqrt n ^ (n + 2) * (L : ℝ) ^ (n - 1)
      ≤ 2 ^ (((n + 2) * cn + 1) / 2) * 2 ^ ((n - 1) * cL) := by
        apply mul_le_mul hnpow hLpow (by positivity) (by positivity)
    _ = 2 ^ (((n + 2) * cn + 1) / 2 + (n - 1) * cL) := by rw [← pow_add]

/-- **Mahler's separation bound.** For a `p` whose rational image is separable
(equivalently squarefree over `ℚ`; `squareFreeRat_iff` discharges this from
`Hex.SquareFreeRat`), any two distinct complex roots of `toPolyℂ p` are more than
`4 · 2^{-sepPrec p}` apart. Vacuous for degree `≤ 1` (where `sepPrec = 0` and there
is at most one root), so the content is the degree `≥ 2` case. -/
theorem sepPrec_separates (p : Hex.ZPoly)
    (hsep : ((toPolynomial p).map (Int.castRingHom ℚ)).Separable) :
    ∀ z₁ z₂ : ℂ, (toPolyℂ p).IsRoot z₁ → (toPolyℂ p).IsRoot z₂ → z₁ ≠ z₂ →
      (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) < ‖z₁ - z₂‖ / 4 := by
  intro z₁ z₂ hr1 hr2 hne
  classical
  set p' := toPolynomial p with hp'
  set f := toPolyℂ p with hf
  have hfmap : f = p'.map (Int.castRingHom ℂ) := rfl
  -- Nonvanishing.
  have hp'0 : p' ≠ 0 := fun h => hsep.ne_zero (by rw [h, Polynomial.map_zero])
  have hf0 : f ≠ 0 := by
    rw [hfmap, ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]; exact hp'0
  have hsplit : f.Splits := IsAlgClosed.splits f
  set ℓ := f.roots.toList with hℓ
  have hz1L : z₁ ∈ ℓ := by
    rw [hℓ, ← Multiset.mem_coe, Multiset.coe_toList]; exact (mem_roots hf0).mpr hr1
  have hz2L : z₂ ∈ ℓ := by
    rw [hℓ, ← Multiset.mem_coe, Multiset.coe_toList]; exact (mem_roots hf0).mpr hr2
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hz1L
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_get.mp hz2L
  have hii : i₀ ≠ i₁ := fun h => hne (by rw [← hi₀, ← hi₁, h])
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.mp hsplit
  have hlen : ℓ.length = f.natDegree := by rw [hℓ, Multiset.length_toList, hcard]
  have hnatf : f.natDegree = ℓ.length := hlen.symm
  have hN2 : 2 ≤ ℓ.length := by
    have h0 := i₀.isLt; have h1 := i₁.isLt
    have : i₀.val ≠ i₁.val := fun h => hii (Fin.ext h)
    omega
  have hnatp' : p'.natDegree = f.natDegree := by
    rw [hfmap]; exact (Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _) p').symm
  have hML : f.mahlerMeasure ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) := by
    have h1 : f.mahlerMeasure ≤ HexPolyZMathlib.l2norm p' := by
      rw [hfmap]; exact HexPolyZMathlib.mahlerMeasure_le_l2norm p'
    have hl2sq : (HexPolyZMathlib.l2norm p') ^ 2 ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ 2 := by
      have hle1 := HexPolyZMathlib.l2norm_toPolynomial_sq_le_coeffNormSq p
      have hle2 : (Hex.ZPoly.coeffNormSq p : ℝ) ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ 2 := by
        rw [Hex.ZPoly.coeffL2NormBound_eq_ceilSqrt_coeffNormSq]
        exact_mod_cast Hex.ZPoly.le_ceilSqrt_sq (Hex.ZPoly.coeffNormSq p)
      calc (HexPolyZMathlib.l2norm p') ^ 2 = (HexPolyZMathlib.l2norm (toPolynomial p)) ^ 2 := by
            rw [hp']
        _ ≤ (Hex.ZPoly.coeffNormSq p : ℝ) := hle1
        _ ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ 2 := hle2
    have hl2nn : (0 : ℝ) ≤ HexPolyZMathlib.l2norm p' := Real.sqrt_nonneg _
    have hLnn : (0 : ℝ) ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, hl2sq, hl2nn, hLnn]
  have hMLpow : f.mahlerMeasure ^ (ℓ.length - 1)
      ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) :=
    pow_le_pow_left₀ (Polynomial.mahlerMeasure_nonneg _) hML (ℓ.length - 1)
  -- Assemble: `1 ≤ √m^{m+2} · L^{m-1} · ‖z₁ − z₂‖`.
  have hbig : (1 : ℝ) ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
      * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := by
    have hshared := HexPolyZMathlib.one_le_mahlerDist
      p' hsep (by simpa only [hfmap] using hr1)
        (by simpa only [hfmap] using hr2) hne
    rw [hnatp', hnatf] at hshared
    calc (1 : ℝ) ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2) *
            f.mahlerMeasure ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := hshared
      _ ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hMLpow (by positivity)
  -- Convert to `1 ≤ 2^E · ‖z₁ − z₂‖` and identify `sepPrec p = E + 3`.
  have hx0 : (0 : ℝ) < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hdeg? : p.degree? = some ℓ.length := by
    have h := natDegree_toPolyℂ p
    rw [show (toPolyℂ p).natDegree = ℓ.length from hnatf] at h
    cases hd : p.degree? with
    | none => exfalso; rw [hd] at h; simp only [Option.getD_none] at h; omega
    | some k => rw [hd] at h; simp only [Option.getD_some] at h; rw [h]
  have hDexp : Real.sqrt ℓ.length ^ (ℓ.length + 2)
      * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1)
      ≤ 2 ^ (((ℓ.length + 2) * Hex.ceilLog2Nat ℓ.length + 1) / 2
          + (ℓ.length - 1) * Hex.ceilLog2Nat (Hex.ZPoly.coeffL2NormBound p)) :=
    pow_le_two_pow_sepExp ℓ.length (Hex.ZPoly.coeffL2NormBound p)
  have hsp : Hex.sepPrec p = ((ℓ.length + 2) * Hex.ceilLog2Nat ℓ.length + 1) / 2
      + (ℓ.length - 1) * Hex.ceilLog2Nat (Hex.ZPoly.coeffL2NormBound p) + 3 := by
    simp only [Hex.sepPrec, hdeg?]
    rw [if_neg (show ¬ ℓ.length ≤ 1 by omega)]
  set E := ((ℓ.length + 2) * Hex.ceilLog2Nat ℓ.length + 1) / 2
      + (ℓ.length - 1) * Hex.ceilLog2Nat (Hex.ZPoly.coeffL2NormBound p) with hEdef
  have hEx : (1 : ℝ) ≤ (2 : ℝ) ^ E * ‖z₁ - z₂‖ := by
    calc (1 : ℝ) ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := hbig
      _ ≤ (2 : ℝ) ^ E * ‖z₁ - z₂‖ := mul_le_mul_of_nonneg_right hDexp (le_of_lt hx0)
  -- Final numeric comparison.
  rw [hsp]
  have h2E : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hExp : (-(((E + 3 : ℕ)) : ℤ)) = -(E : ℤ) - 3 := by push_cast; ring
  rw [hExp]
  have hzpow : (2 : ℝ) ^ (-(E : ℤ) - 3) = ((2 : ℝ) ^ E)⁻¹ / 8 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), _root_.zpow_neg, zpow_natCast]
    norm_num
  rw [hzpow]
  have hinv : ((2 : ℝ) ^ E)⁻¹ ≤ ‖z₁ - z₂‖ := by
    rw [inv_eq_one_div, div_le_iff₀ h2E, mul_comm]; exact hEx
  linarith [hinv, hx0]

end

end HexRealRootsMathlib
