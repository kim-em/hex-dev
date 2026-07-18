/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRoots.Prec
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import HexRealRootsMathlib.Hadamard
public import HexRealRootsMathlib.Discr

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
squarefree `p` are more than `4 · 2^{-sepPrec p}` apart — is the project's
hardest remaining assembly (Mahler 1964: `|disc p| ≥ 1`, the discriminant
root-product formula in `HexRealRootsMathlib.Discr`, Hadamard's inequality on
the Vandermonde matrix in `HexRealRootsMathlib.Hadamard`, and Landau's
inequality `HexPolyZMathlib.mahlerMeasure_le_l2norm`). It is not yet
formalised here; the numeric groundwork (`le_two_pow_ceilLog2Nat`,
`toReal_twoPow`, the `toPolyℂ` cast) lives in this file for the follow-up.
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

The building blocks (`Matrix.norm_det_le_prod_norm_column`,
`Polynomial.discr_eq_prod_roots`, `Polynomial.mahlerMeasure_le_l2norm`) are stated
in ordinary Mathlib generality; the pieces below are Hex-free until the final
assembly. -/

section MahlerSep

open Finset Matrix

/-- The divided-difference entry bound: `‖yⁱ − xⁱ‖ ≤ i · Cⁱ⁻¹ · ‖y − x‖` when
`‖x‖, ‖y‖ ≤ C` and `1 ≤ C`. Follows from the geometric factorisation
`yⁱ − xⁱ = (∑_{l<i} yˡ xⁱ⁻¹⁻ˡ)(y − x)`. -/
theorem norm_pow_sub_pow_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ (i : ℝ) * C ^ (i - 1) * ‖y - x‖ := by
  rw [← geom_sum₂_mul y x i, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ l ∈ Finset.range i, y ^ l * x ^ (i - 1 - l)‖
      ≤ ∑ l ∈ Finset.range i, ‖y ^ l * x ^ (i - 1 - l)‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.range i, C ^ (i - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l ≤ i - 1 := by have := Finset.mem_range.mp hl; omega
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖y‖ ^ l * ‖x‖ ^ (i - 1 - l) ≤ C ^ l * C ^ (i - 1 - l) := by
              gcongr
          _ = C ^ (l + (i - 1 - l)) := by rw [← pow_add]
          _ = C ^ (i - 1) := by rw [Nat.add_sub_cancel' hl']
    _ = (i : ℝ) * C ^ (i - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The L² norm of an ordinary Vandermonde column: `√(∑ᵢ ‖aⁱ‖²) ≤ √N · max(1,‖a‖)^{N-1}`. -/
theorem sqrt_sum_pow_sq_le (a : ℂ) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2) ≤ Real.sqrt N * (max 1 ‖a‖) ^ (N - 1) := by
  have hBnn : (0 : ℝ) ≤ max 1 ‖a‖ := le_trans zero_le_one (le_max_left _ _)
  have hbound : ∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2 ≤ (N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1)) := by
    have : ∀ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2 ≤ (max 1 ‖a‖) ^ (2 * (N - 1)) := by
      intro i
      rw [norm_pow, ← pow_mul]
      calc ‖a‖ ^ ((i : ℕ) * 2) ≤ (max 1 ‖a‖) ^ ((i : ℕ) * 2) := by
            gcongr
            exact le_max_right _ _
        _ ≤ (max 1 ‖a‖) ^ (2 * (N - 1)) := by
            apply pow_le_pow_right₀ (le_max_left _ _)
            have := i.isLt; omega
    calc ∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2
        ≤ ∑ _i : Fin N, (max 1 ‖a‖) ^ (2 * (N - 1)) := Finset.sum_le_sum (fun i _ => this i)
      _ = (N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2)
      ≤ Real.sqrt ((N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1))) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt N * (max 1 ‖a‖) ^ (N - 1) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N), show 2 * (N - 1) = (N - 1) * 2 by ring,
          pow_mul, Real.sqrt_sq (by positivity)]

/-- The L² norm of the isolating (differenced) Vandermonde column:
`√(∑ᵢ ‖yⁱ − xⁱ‖²) ≤ C^{N-2} · ‖y − x‖ · √(∑ᵢ i²)`. -/
theorem sqrt_sum_sub_pow_sq_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2)
      ≤ C ^ (N - 2) * ‖y - x‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
  have hCnn : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hbound : ∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2
      ≤ (C ^ (N - 2) * ‖y - x‖) ^ 2 * ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hentry : ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ≤ ((i : ℕ) : ℝ) * C ^ (N - 2) * ‖y - x‖ := by
      refine (norm_pow_sub_pow_le hx hy hC (i : ℕ)).trans ?_
      have hstep : C ^ ((i : ℕ) - 1) ≤ C ^ (N - 2) := by
        apply pow_le_pow_right₀ hC; have := i.isLt; omega
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)) (norm_nonneg _)
    calc ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2
        ≤ (((i : ℕ) : ℝ) * C ^ (N - 2) * ‖y - x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
      _ = (C ^ (N - 2) * ‖y - x‖) ^ 2 * ((i : ℕ) : ℝ) ^ 2 := by ring
  calc Real.sqrt (∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2)
      ≤ Real.sqrt ((C ^ (N - 2) * ‖y - x‖) ^ 2 * ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = C ^ (N - 2) * ‖y - x‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- `√(∑_{i<N} i²) ≤ (√N)³`. -/
theorem sqrt_sum_sq_le (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) ≤ Real.sqrt N ^ 3 := by
  have hb : ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
    calc ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2
        ≤ ∑ _i : Fin N, (N : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hi 2
      _ = (N : ℝ) ^ 3 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsq : (Real.sqrt N ^ 3) ^ 2 = (N : ℝ) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]
  refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- **Mahler's isolating-column bound.** For a leading coefficient `c` and points
`α : Fin N → ℂ` with `‖α i₀‖ ≤ ‖α i₁‖`, the scaled Vandermonde determinant is
bounded by `√N^{N-1} · √(∑ i²) · (‖c‖ · ∏ max(1,‖α j‖))^{N-1} · ‖α i₁ − α i₀‖`. -/
theorem norm_det_vandermonde_le {N : ℕ} (hN : 2 ≤ N) (c : ℂ) (α : Fin N → ℂ)
    {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁) (hle : ‖α i₀‖ ≤ ‖α i₁‖) :
    ‖c‖ ^ (N - 1) * ‖(Matrix.vandermonde α).det‖ ≤
      Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (‖c‖ * ∏ j, max 1 ‖α j‖) ^ (N - 1) * ‖α i₁ - α i₀‖ := by
  classical
  set B : Fin N → ℝ := fun j => max 1 ‖α j‖ with hBdef
  have hB1 : ∀ j, (1 : ℝ) ≤ B j := fun j => le_max_left _ _
  have hBnorm : ∀ j, ‖α j‖ ≤ B j := fun j => le_max_right _ _
  have hB0 : ∀ j, (0 : ℝ) ≤ B j := fun j => le_trans zero_le_one (hB1 j)
  -- The row-reduced matrix `W`: subtract row `i₀` from row `i₁`.
  set W : Matrix (Fin N) (Fin N) ℂ :=
    (Matrix.vandermonde α).updateRow i₁
      ((Matrix.vandermonde α) i₁ + (-1 : ℂ) • (Matrix.vandermonde α) i₀) with hWdef
  have hWdet : W.det = (Matrix.vandermonde α).det :=
    Matrix.det_updateRow_add_smul_self _ (Ne.symm hne) _
  have hWne : ∀ j, j ≠ i₁ → ∀ i : Fin N, W j i = α j ^ (i : ℕ) := by
    intro j hj i
    rw [hWdef, Matrix.updateRow_ne hj, Matrix.vandermonde_apply]
  have hWeq : ∀ i : Fin N, W i₁ i = α i₁ ^ (i : ℕ) - α i₀ ^ (i : ℕ) := by
    intro i
    rw [hWdef, Matrix.updateRow_self]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.vandermonde_apply, smul_eq_mul, neg_one_mul]
    ring
  -- Hadamard's inequality applied to the transpose.
  have hHad : ‖(Matrix.vandermonde α).det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2) := by
    rw [← hWdet, ← Matrix.det_transpose W]
    exact Matrix.norm_det_le_prod_norm_column Wᵀ
  -- Column bounds.
  have hRi1 : Real.sqrt (∑ i, ‖W i₁ i‖ ^ 2)
      ≤ B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
    rw [show (∑ i, ‖W i₁ i‖ ^ 2) = ∑ i : Fin N, ‖α i₁ ^ (i : ℕ) - α i₀ ^ (i : ℕ)‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hWeq i])]
    exact sqrt_sum_sub_pow_sq_le (le_trans hle (hBnorm i₁)) (hBnorm i₁) (hB1 i₁) N
  have hRj : ∀ j, j ≠ i₁ →
      Real.sqrt (∑ i, ‖W j i‖ ^ 2) ≤ Real.sqrt N * B j ^ (N - 1) := by
    intro j hj
    rw [show (∑ i, ‖W j i‖ ^ 2) = ∑ i : Fin N, ‖α j ^ (i : ℕ)‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hWne j hj i])]
    exact sqrt_sum_pow_sq_le (α j) N
  -- Product of column bounds.
  have herasecard : (univ.erase i₁).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ, Fintype.card_fin]
  have hprodEnn : (0 : ℝ) ≤ ∏ j ∈ univ.erase i₁, B j := Finset.prod_nonneg (fun j _ => hB0 j)
  have hprodbound : ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2)
      ≤ (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2))
        * ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1)) := by
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₁)]
    refine mul_le_mul hRi1 ?_ (Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (pow_nonneg (hB0 i₁) _) (norm_nonneg _)) (Real.sqrt_nonneg _))
    exact Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _)
      (fun j hj => hRj j (Finset.mem_erase.mp hj).1)
  have hprodrw : ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1))
      = Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, herasecard, Finset.prod_pow]
  -- Combine.
  have hcombine : ‖c‖ ^ (N - 1) * ‖(Matrix.vandermonde α).det‖
      ≤ ‖c‖ ^ (N - 1) * (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖
          * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
          * (Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1))) := by
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg c) _)
    calc ‖(Matrix.vandermonde α).det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2) := hHad
      _ ≤ (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2))
            * ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1)) := hprodbound
      _ = _ := by rw [hprodrw]
  refine hcombine.trans ?_
  -- The final algebra: `(B i₁)^{N-2} ≤ (B i₁)^{N-1}` absorbs the leftover factor.
  set K := Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) * ‖c‖ ^ (N - 1)
      * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1) * ‖α i₁ - α i₀‖ with hKdef
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _))
      (pow_nonneg (norm_nonneg _) _)) (pow_nonneg hprodEnn _)) (norm_nonneg _)
  have hBig : ‖c‖ ^ (N - 1) * (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖
        * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1)))
      = K * B i₁ ^ (N - 2) := by rw [hKdef]; ring
  have hTar : Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (‖c‖ * ∏ j, B j) ^ (N - 1) * ‖α i₁ - α i₀‖ = K * B i₁ ^ (N - 1) := by
    rw [show (∏ j, B j) = B i₁ * ∏ j ∈ univ.erase i₁, B j from
      (Finset.mul_prod_erase univ B (Finset.mem_univ i₁)).symm, mul_pow, mul_pow, hKdef]
    ring
  rw [hBig, hTar]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB1 i₁) (by omega)) hKnn

/-- The off-diagonal root-difference product equals `‖det V‖²` in norm. -/
theorem norm_prod_roots_eq_sq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) :
    ‖((Multiset.map α univ.val).map
        (fun x => (((Multiset.map α univ.val).erase x).map (fun y => x - y)).prod)).prod‖
      = ‖(Matrix.vandermonde α).det‖ ^ 2 := by
  classical
  -- Reduce the multiset double product to a `Finset` double product.
  have hD : ((Multiset.map α univ.val).map
      (fun x => (((Multiset.map α univ.val).erase x).map (fun y => x - y)).prod)).prod
        = ∏ i, ∏ j ∈ univ.erase i, (α i - α j) := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Function.comp_apply]
    rw [← Multiset.map_erase α hα, ← Finset.erase_val, Multiset.map_map,
      ← Finset.prod_eq_multiset_prod]
    rfl
  rw [hD, det_vandermonde]
  simp only [norm_prod]
  -- Symmetry of the norm of a difference.
  have hsym : ∀ a b : ℂ, ‖a - b‖ = ‖b - a‖ := fun a b => norm_sub_rev a b
  -- Rewrite the Vandermonde side to `∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖`.
  have hQ : ∏ i, ∏ j ∈ Ioi i, ‖α j - α i‖ = ∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖ :=
    Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hsym _ _))
  rw [hQ]
  -- The lower-triangular product equals the upper-triangular product by symmetry.
  have hPIio : ∏ i, ∏ j ∈ Iio i, ‖α i - α j‖ = ∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖ := by
    rw [Finset.prod_comm' (s := univ) (t := fun i => Iio i) (t' := univ) (s' := fun j => Ioi j)
      (by intro x y; simp only [Finset.mem_univ, true_and, and_true,
        Finset.mem_Iio, Finset.mem_Ioi])]
    exact Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hsym _ _))
  -- Split `univ.erase i = Ioi i ⊔ Iio i` and recombine.
  have hsplit2 : ∀ i : Fin N,
      univ.erase i = (Ioi i).disjUnion (Iio i) (Finset.disjoint_Ioi_Iio i) := by
    intro i; rw [Finset.Ioi_disjUnion_Iio, Finset.compl_singleton]
  calc ∏ i, ∏ j ∈ univ.erase i, ‖α i - α j‖
      = ∏ i, ((∏ j ∈ Ioi i, ‖α i - α j‖) * ∏ j ∈ Iio i, ‖α i - α j‖) :=
        Finset.prod_congr rfl (fun i _ => by rw [hsplit2 i, Finset.prod_disjUnion])
    _ = (∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖) * ∏ i, ∏ j ∈ Iio i, ‖α i - α j‖ :=
        Finset.prod_mul_distrib
    _ = (∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖) ^ 2 := by rw [hPIio, sq]

/-- The discriminant in root-enumeration form: `‖disc f‖ = ‖lc‖^{2n-2} · ‖det V‖²`. -/
theorem norm_discr_eq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) {f : ℂ[X]}
    (hf : 0 < f.degree) (hsplit : f.Splits) (hroots : f.roots = Multiset.map α univ.val) :
    ‖f.discr‖ = ‖f.leadingCoeff‖ ^ (2 * f.natDegree - 2) * ‖(Matrix.vandermonde α).det‖ ^ 2 := by
  classical
  rw [discr_eq_prod_roots hf hsplit]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hroots, norm_prod_roots_eq_sq α hα]

end MahlerSep

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

open Finset Matrix in
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
  -- Symmetric in `z₁, z₂`; reduce to the case `‖z₁‖ ≤ ‖z₂‖`.
  suffices key : ∀ w₁ w₂ : ℂ, (toPolyℂ p).IsRoot w₁ → (toPolyℂ p).IsRoot w₂ →
      w₁ ≠ w₂ → ‖w₁‖ ≤ ‖w₂‖ → (2 : ℝ) ^ (-(Hex.sepPrec p : ℤ)) < ‖w₁ - w₂‖ / 4 by
    rcases le_total ‖z₁‖ ‖z₂‖ with h | h
    · exact key z₁ z₂ hr1 hr2 hne h
    · have hh := key z₂ z₁ hr2 hr1 (Ne.symm hne) h
      rwa [norm_sub_rev] at hh
  clear hr1 hr2 hne z₁ z₂
  intro z₁ z₂ hr1 hr2 hne hnorm
  classical
  set p' := toPolynomial p with hp'
  set f := toPolyℂ p with hf
  have hfmap : f = p'.map (Int.castRingHom ℂ) := rfl
  -- Nonvanishing.
  have hp'0 : p' ≠ 0 := fun h => hsep.ne_zero (by rw [h, Polynomial.map_zero])
  have hf0 : f ≠ 0 := by
    rw [hfmap, ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]; exact hp'0
  -- Splitting and separability over `ℂ`.
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have hsepℂ : f.Separable := by
    have hff : f = (p'.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
      rw [hfmap, Polynomial.map_map, hcomp]
    rw [hff]; exact hsep.map
  have hnd : f.roots.Nodup := nodup_roots hsepℂ
  -- Enumerate the roots as `α : Fin ℓ.length → ℂ`.
  set ℓ := f.roots.toList with hℓ
  have hℓnd : ℓ.Nodup := Multiset.coe_nodup.mp (by rw [hℓ, Multiset.coe_toList]; exact hnd)
  set α : Fin ℓ.length → ℂ := ℓ.get with hαdef
  have hαinj : Function.Injective α := List.nodup_iff_injective_get.mp hℓnd
  have hroots : Multiset.map α univ.val = f.roots := by
    rw [Fin.univ_val_map, hαdef, List.ofFn_get, hℓ, Multiset.coe_toList]
  have hBnn : (0 : ℝ) ≤ ∏ j, max 1 ‖α j‖ :=
    Finset.prod_nonneg (fun j _ => le_trans zero_le_one (le_max_left _ _))
  have hlcBnn : (0 : ℝ) ≤ ‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖ := mul_nonneg (norm_nonneg _) hBnn
  -- Indices of `z₁, z₂`.
  have hz1L : z₁ ∈ ℓ := by
    rw [hℓ, ← Multiset.mem_coe, Multiset.coe_toList]; exact (mem_roots hf0).mpr hr1
  have hz2L : z₂ ∈ ℓ := by
    rw [hℓ, ← Multiset.mem_coe, Multiset.coe_toList]; exact (mem_roots hf0).mpr hr2
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hz1L
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_get.mp hz2L
  have hαi0 : α i₀ = z₁ := hi₀
  have hαi1 : α i₁ = z₂ := hi₁
  have hii : i₀ ≠ i₁ := fun h => hne (by rw [← hαi0, ← hαi1, h])
  -- Degree facts. `m := ℓ.length = f.natDegree ≥ 2`.
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.mp hsplit
  have hlen : ℓ.length = f.natDegree := by rw [hℓ, Multiset.length_toList, hcard]
  have hnatf : f.natDegree = ℓ.length := hlen.symm
  have hN2 : 2 ≤ ℓ.length := by
    have h0 := i₀.isLt; have h1 := i₁.isLt
    have : i₀.val ≠ i₁.val := fun h => hii (Fin.ext h)
    omega
  have hdegf : 0 < f.degree :=
    natDegree_pos_iff_degree_pos.mp (by omega)
  -- Lower bound on the discriminant.
  have hnatp' : p'.natDegree = f.natDegree := by
    rw [hfmap]; exact (Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _) p').symm
  have hdeg' : 0 < p'.degree := natDegree_pos_iff_degree_pos.mp (by rw [hnatp']; omega)
  have hdiscZ : 1 ≤ |p'.discr| := Polynomial.one_le_abs_discr hdeg' hsep
  have hdiscnorm : (1 : ℝ) ≤ ‖f.discr‖ := by
    have hmap : f.discr = ((p'.discr : ℤ) : ℂ) := by
      rw [hfmap, Polynomial.discr_map_of_injective (Int.castRingHom ℂ)
        (RingHom.injective_int _) hdeg']; simp
    rw [hmap, Complex.norm_intCast]; exact_mod_cast hdiscZ
  have hdisceq := norm_discr_eq α hαinj hdegf hsplit hroots.symm
  rw [hnatf] at hdisceq
  -- `A := ‖lc‖^{m-1}·‖det V‖ ≥ 1`.
  set V := (Matrix.vandermonde α).det with hV
  have hAsq : (‖f.leadingCoeff‖ ^ (ℓ.length - 1) * ‖V‖) ^ 2
      = ‖f.leadingCoeff‖ ^ (2 * ℓ.length - 2) * ‖V‖ ^ 2 := by
    rw [mul_pow, ← pow_mul]; congr 2; omega
  have hAnn : (0 : ℝ) ≤ ‖f.leadingCoeff‖ ^ (ℓ.length - 1) * ‖V‖ := by positivity
  have hA1 : (1 : ℝ) ≤ ‖f.leadingCoeff‖ ^ (ℓ.length - 1) * ‖V‖ := by
    have hsq1 : (1 : ℝ) ≤ (‖f.leadingCoeff‖ ^ (ℓ.length - 1) * ‖V‖) ^ 2 := by
      rw [hAsq, ← hdisceq]; exact hdiscnorm
    nlinarith [hsq1, hAnn]
  -- The Mahler/Hadamard bound.
  have hnormα : ‖α i₀‖ ≤ ‖α i₁‖ := by rw [hαi0, hαi1]; exact hnorm
  have hcrux := norm_det_vandermonde_le hN2 f.leadingCoeff α hii hnormα
  -- `√m^{m-1}·√(∑ i²) ≤ √m^{m+2}`.
  have hsqrtstep :
      Real.sqrt ℓ.length ^ (ℓ.length - 1) * Real.sqrt (∑ i : Fin ℓ.length, ((i : ℕ) : ℝ) ^ 2)
        ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2) := by
    calc Real.sqrt ℓ.length ^ (ℓ.length - 1)
          * Real.sqrt (∑ i : Fin ℓ.length, ((i : ℕ) : ℝ) ^ 2)
        ≤ Real.sqrt ℓ.length ^ (ℓ.length - 1) * Real.sqrt ℓ.length ^ 3 :=
          mul_le_mul_of_nonneg_left (sqrt_sum_sq_le ℓ.length) (by positivity)
      _ = Real.sqrt ℓ.length ^ (ℓ.length + 2) := by rw [← pow_add]; congr 1; omega
  -- The Mahler measure identity `M = ‖lc‖ · ∏ max(1,‖α j‖)` and Landau bound `M ≤ L`.
  have hMprod : (f.roots.map (fun a => max 1 ‖a‖)).prod = ∏ j, max 1 ‖α j‖ := by
    rw [← hroots, Multiset.map_map]; rfl
  have hM : ‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖ = f.mahlerMeasure := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hMprod]
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
  have hMLpow : (‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^ (ℓ.length - 1)
      ≤ (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) :=
    pow_le_pow_left₀ hlcBnn (by rw [hM]; exact hML) (ℓ.length - 1)
  have hdiffx : ‖α i₁ - α i₀‖ = ‖z₁ - z₂‖ := by rw [hαi0, hαi1, norm_sub_rev]
  -- Assemble: `1 ≤ √m^{m+2} · L^{m-1} · ‖z₁ − z₂‖`.
  have hbig : (1 : ℝ) ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
      * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := by
    calc (1 : ℝ) ≤ ‖f.leadingCoeff‖ ^ (ℓ.length - 1) * ‖V‖ := hA1
      _ ≤ Real.sqrt ℓ.length ^ (ℓ.length - 1)
            * Real.sqrt (∑ i : Fin ℓ.length, ((i : ℕ) : ℝ) ^ 2)
            * (‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^ (ℓ.length - 1) * ‖α i₁ - α i₀‖ := hcrux
      _ = (Real.sqrt ℓ.length ^ (ℓ.length - 1)
            * Real.sqrt (∑ i : Fin ℓ.length, ((i : ℕ) : ℝ) ^ 2))
            * ((‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^ (ℓ.length - 1) * ‖α i₁ - α i₀‖) := by
          ring
      _ ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * ((‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^ (ℓ.length - 1) * ‖α i₁ - α i₀‖) :=
          mul_le_mul_of_nonneg_right hsqrtstep
            (mul_nonneg (pow_nonneg hlcBnn _) (norm_nonneg _))
      _ = Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * (‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^ (ℓ.length - 1) * ‖α i₁ - α i₀‖ := by ring
      _ ≤ Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖α i₁ - α i₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hMLpow (by positivity)
      _ = Real.sqrt ℓ.length ^ (ℓ.length + 2)
            * (Hex.ZPoly.coeffL2NormBound p : ℝ) ^ (ℓ.length - 1) * ‖z₁ - z₂‖ := by rw [hdiffx]
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
