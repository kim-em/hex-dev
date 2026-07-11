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

end

end HexRealRootsMathlib
