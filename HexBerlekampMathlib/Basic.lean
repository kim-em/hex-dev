/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexBerlekamp.RabinSoundness
public import HexModArithMathlib
public import HexPolyMathlib
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.GaloisField

public section

/-!
Mathlib-facing correctness surface for `HexBerlekamp`.

This module transfers executable `FpPoly p` values to Mathlib polynomials over
`ZMod p` and states the initial Berlekamp-factor and Rabin-test correctness
theorems used by downstream finite-field factorization proofs.
-/

namespace HexBerlekampMathlib

universe u

noncomputable section

open Polynomial

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def fpPolyToPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (HexModArithMathlib.ZMod64.toZMod (f.coeff i))

/-- Rebuild an executable `FpPoly p` from a Mathlib polynomial over `ZMod p`. -/
def polynomialToFpPoly (f : Polynomial (ZMod p)) : Hex.FpPoly p :=
  Hex.DensePoly.ofCoeffs <|
    ((List.range (f.natDegree + 1)).map fun i =>
      HexModArithMathlib.ZMod64.equiv.symm (f.coeff i)).toArray

/-- Coefficient view of the direct finite-field transport `fpPolyToPolynomial`,
the standalone form of `coeff_toMathlibPolynomial` available before the ring
equivalence is assembled. -/
theorem coeff_fpPolyToPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (fpPolyToPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) := by
  rw [fpPolyToPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range f.size) n
    (fun i => HexModArithMathlib.ZMod64.toZMod (f.coeff i))]
  by_cases hn : n ∈ Finset.range f.size
  · rw [if_pos hn]
  · rw [if_neg hn, Hex.DensePoly.coeff_eq_zero_of_size_le f
      (Nat.le_of_not_lt (Finset.mem_range.not.mp hn))]
    exact HexModArithMathlib.ZMod64.toZMod_zero.symm

/-- The finite-field transport `toZMod` distributes over an additive
`List.range` fold from `0`, converting it to the `ZMod p` range sum. -/
private theorem toZMod_foldl_add_eq_sum (term : Nat → Hex.ZMod64 p) (m : Nat) :
    HexModArithMathlib.ZMod64.toZMod
        ((List.range m).foldl (fun acc i => acc + term i) 0) =
      ∑ i ∈ Finset.range m, HexModArithMathlib.ZMod64.toZMod (term i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [HexModArithMathlib.ZMod64.toZMod_add, ih, Finset.sum_range_succ]

/-- The transported diagonal term is the `ZMod p` convolution contribution. -/
private theorem toZMod_diagonalMulCoeffTerm (f g : Hex.FpPoly p) (n i : Nat) :
    HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.diagonalMulCoeffTerm f g n i) =
      if n < i then (0 : ZMod p)
      else HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
        HexModArithMathlib.ZMod64.toZMod (g.coeff (n - i)) := by
  unfold Hex.DensePoly.diagonalMulCoeffTerm
  by_cases hni : n < i
  · simp only [if_pos hni]
    exact HexModArithMathlib.ZMod64.toZMod_zero
  · simp only [if_neg hni, HexModArithMathlib.ZMod64.toZMod_mul]

/-- The executable schoolbook multiplication coefficient, transported to
`ZMod p`, is the truncated convolution sum over the support of `f`. -/
private theorem toZMod_mulCoeffSum_eq_sum (f g : Hex.FpPoly p) (n : Nat) :
    HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.mulCoeffSum f g n) =
      ∑ i ∈ Finset.range f.size,
        (if n < i then (0 : ZMod p)
         else HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
          HexModArithMathlib.ZMod64.toZMod (g.coeff (n - i))) := by
  have hdiag : Hex.DensePoly.mulCoeffSum f g n =
      (List.range f.size).foldl
        (fun acc i => acc + Hex.DensePoly.diagonalMulCoeffTerm f g n i) 0 :=
    Hex.DensePoly.mulCoeffSum_eq_diagonal f g n
  rw [hdiag, toZMod_foldl_add_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact toZMod_diagonalMulCoeffTerm f g n i

/-- The truncated convolution sum over the support of `f` agrees with the
degree-`n` antidiagonal sum, the `ZMod p` side of the multiplication transport. -/
private theorem sum_ite_diagonal_eq_range_succ (f g : Hex.FpPoly p) (n : Nat) :
    (∑ i ∈ Finset.range f.size,
      (if n < i then (0 : ZMod p)
       else HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
        HexModArithMathlib.ZMod64.toZMod (g.coeff (n - i)))) =
      ∑ i ∈ Finset.range (n + 1),
        HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
          HexModArithMathlib.ZMod64.toZMod (g.coeff (n - i)) := by
  set term : Nat → ZMod p := fun i =>
    HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
      HexModArithMathlib.ZMod64.toZMod (g.coeff (n - i)) with hterm
  set F : Nat → ZMod p := fun i => if n < i then 0 else term i with hF
  have hF_size : ∀ i, f.size ≤ i → F i = 0 := by
    intro i hi
    simp only [hF]
    by_cases hni : n < i
    · simp [hni]
    · simp only [hni, if_false, hterm]
      rw [Hex.DensePoly.coeff_eq_zero_of_size_le f hi]
      rw [show HexModArithMathlib.ZMod64.toZMod (Zero.zero : Hex.ZMod64 p) = 0 from
        HexModArithMathlib.ZMod64.toZMod_zero, zero_mul]
  have hF_deg : ∀ i, n < i → F i = 0 := by
    intro i hi; simp [hF, hi]
  have hFterm : ∀ i ∈ Finset.range (n + 1), F i = term i := by
    intro i hi
    have hle : ¬ n < i := by have := Finset.mem_range.mp hi; omega
    simp [hF, hle]
  have e1 : (∑ i ∈ Finset.range f.size, F i) =
      ∑ i ∈ Finset.range (max f.size (n + 1)), F i := by
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp ha) (le_max_left _ _))
    · intro i _ hi
      exact hF_size i (Nat.le_of_not_lt (Finset.mem_range.not.mp hi))
  have e2 : (∑ i ∈ Finset.range (n + 1), F i) =
      ∑ i ∈ Finset.range (max f.size (n + 1)), F i := by
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp ha) (le_max_right _ _))
    · intro i _ hi
      exact hF_deg i (by have := Finset.mem_range.not.mp hi; omega)
  calc (∑ i ∈ Finset.range f.size, F i)
      = ∑ i ∈ Finset.range (n + 1), F i := by rw [e1, ← e2]
    _ = ∑ i ∈ Finset.range (n + 1), term i := Finset.sum_congr rfl hFterm

/--
The executable finite-field polynomial representation is ring-equivalent to
Mathlib polynomials over `ZMod p`.
-/
@[expose]
def fpPolyEquiv : Hex.FpPoly p ≃+* Polynomial (ZMod p) where
  toFun := fpPolyToPolynomial
  invFun := polynomialToFpPoly
  left_inv := by
    intro f
    apply Hex.DensePoly.ext_coeff
    intro n
    rw [polynomialToFpPoly, Hex.DensePoly.coeff_ofCoeffs_list,
      HexPolyMathlib.list_getD_map_range_zero]
    by_cases hn : n < (fpPolyToPolynomial f).natDegree + 1
    · simp only [if_pos hn, coeff_fpPolyToPolynomial,
        HexModArithMathlib.ZMod64.equiv_symm_apply, HexModArithMathlib.ZMod64.ofZMod_toZMod]
    · rw [if_neg hn]
      have hcoeff : (fpPolyToPolynomial f).coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [coeff_fpPolyToPolynomial f n] at hcoeff
      have hzero : f.coeff n = 0 := by
        have := congrArg HexModArithMathlib.ZMod64.ofZMod hcoeff
        rwa [HexModArithMathlib.ZMod64.ofZMod_toZMod,
          HexModArithMathlib.ZMod64.ofZMod_zero] at this
      exact hzero.symm
  right_inv := by
    intro P
    apply Polynomial.ext
    intro n
    rw [coeff_fpPolyToPolynomial, polynomialToFpPoly, Hex.DensePoly.coeff_ofCoeffs_list,
      HexPolyMathlib.list_getD_map_range_zero]
    by_cases hn : n < P.natDegree + 1
    · simp only [if_pos hn, HexModArithMathlib.ZMod64.equiv_symm_apply,
        HexModArithMathlib.ZMod64.toZMod_ofZMod]
    · rw [if_neg hn, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact HexModArithMathlib.ZMod64.toZMod_zero
  map_mul' := by
    intro f g
    apply Polynomial.ext
    intro n
    rw [coeff_fpPolyToPolynomial (f * g) n, Hex.DensePoly.coeff_mul f g n,
      toZMod_mulCoeffSum_eq_sum f g n, Polynomial.coeff_mul]
    simp only [coeff_fpPolyToPolynomial]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => HexModArithMathlib.ZMod64.toZMod (f.coeff i) *
        HexModArithMathlib.ZMod64.toZMod (g.coeff j)) n]
    exact sum_ite_diagonal_eq_range_succ f g n
  map_add' := by
    intro f g
    apply Polynomial.ext
    intro n
    rw [coeff_fpPolyToPolynomial (f + g) n, Polynomial.coeff_add,
      coeff_fpPolyToPolynomial f n, coeff_fpPolyToPolynomial g n,
      Hex.DensePoly.coeff_add f g n
        (inferInstance : Hex.DensePoly.AddZeroLaw (Hex.ZMod64 p)).add_zero_zero]
    exact HexModArithMathlib.ZMod64.toZMod_add _ _

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
@[expose]
def toMathlibPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  fpPolyEquiv f

@[simp, grind =]
theorem fpPolyEquiv_apply (f : Hex.FpPoly p) :
    fpPolyEquiv f = toMathlibPolynomial f := by
  rfl

@[simp, grind =]
theorem fpPolyEquiv_symm_apply (f : Polynomial (ZMod p)) :
    fpPolyEquiv.symm f = polynomialToFpPoly f := by
  rfl

@[simp, grind =]
theorem coeff_toMathlibPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) := by
  show (fpPolyToPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n)
  rw [fpPolyToPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range f.size) n
    (fun i => HexModArithMathlib.ZMod64.toZMod (f.coeff i))]
  by_cases hn : n ∈ Finset.range f.size
  · rw [if_pos hn]
  · rw [if_neg hn, Hex.DensePoly.coeff_eq_zero_of_size_le f
      (Nat.le_of_not_lt (Finset.mem_range.not.mp hn))]
    exact HexModArithMathlib.ZMod64.toZMod_zero.symm

@[simp, grind =]
theorem coeff_toMathlibPolynomial_equiv (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.equiv (f.coeff n) := by
  rw [coeff_toMathlibPolynomial, HexModArithMathlib.ZMod64.equiv_apply]

/-- Coefficient view supplied by `HexPolyMathlib.toPolynomial`. -/
theorem hexPolyMathlib_coeff_bridge
    {R : Type u} [Semiring R] [DecidableEq R] (f : Hex.DensePoly R) (n : Nat) :
    (HexPolyMathlib.toPolynomial f).coeff n = f.coeff n := by
  simp

/--
The direct finite-field transport is the coefficientwise lift along
`ZMod64.equiv`, matching the coefficient view supplied by the generic
`HexPolyMathlib.toPolynomial`.
-/
theorem toMathlibPolynomial_coeff_bridge (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.equiv (f.coeff n) :=
  coeff_toMathlibPolynomial_equiv f n

/-- Monicity of executable finite-field polynomials transfers to Mathlib.

No nontriviality hypothesis is required: when `ZMod p` is trivial every
polynomial is monic, and otherwise the executable leading coefficient `1`
transports to the Mathlib leading coefficient `1`. -/
theorem toMathlibPolynomial_monic (f : Hex.FpPoly p) :
    Hex.DensePoly.Monic f → (toMathlibPolynomial f).Monic := by
  intro hmonic
  -- `f.coeff (size - 1)` is the leading coefficient, also in the degenerate
  -- `size = 0` case where both sides are `0`.
  have hlc : f.coeff (f.size - 1) = f.leadingCoeff := by
    rcases Nat.eq_zero_or_pos f.size with h0 | hpos
    · have hf0 : f = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro n
        rw [Hex.DensePoly.coeff_zero]
        exact Hex.DensePoly.coeff_eq_zero_of_size_le f (by omega)
      rw [hf0, Hex.DensePoly.size_zero, Hex.DensePoly.leadingCoeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le (0 : Hex.FpPoly p) (by simp)
    · exact (Hex.DensePoly.leadingCoeff_eq_coeff_last f hpos).symm
  refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one (f.size - 1) ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro N hN
    rw [coeff_toMathlibPolynomial,
      Hex.DensePoly.coeff_eq_zero_of_size_le f (by omega)]
    exact HexModArithMathlib.ZMod64.toZMod_zero
  · rw [coeff_toMathlibPolynomial, hlc,
      Hex.DensePoly.leadingCoeff_eq_one_of_monic hmonic]
    exact HexModArithMathlib.ZMod64.toZMod_one

/-- The executable Berlekamp basis size is the Mathlib natural degree after
transport. Requires `Nontrivial (ZMod p)`: over a trivial `ZMod p` the
transport collapses to `0` while `basisSize` can be positive (e.g. `p = 1`,
`f = X`). -/
theorem natDegree_toMathlibPolynomial_eq_basisSize
    [Nontrivial (ZMod p)]
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f) :
    (toMathlibPolynomial f).natDegree = Hex.Berlekamp.basisSize f := by
  -- Monicity plus nontriviality forces the leading coefficient `1 ≠ 0`, so the
  -- polynomial is nonzero and `f.size > 0`.
  have hsize_pos : 0 < f.size := by
    rcases Nat.eq_zero_or_pos f.size with h0 | hpos
    · exfalso
      have hf0 : f = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro n
        rw [Hex.DensePoly.coeff_zero]
        exact Hex.DensePoly.coeff_eq_zero_of_size_le f (by omega)
      have h1 : f.leadingCoeff = 1 :=
        Hex.DensePoly.leadingCoeff_eq_one_of_monic hmonic
      rw [hf0, Hex.DensePoly.leadingCoeff_zero] at h1
      -- `h1 : (0 : ZMod64 p) = 1`; transport to `ZMod p` to contradict
      -- `Nontrivial`.
      have hz : (0 : ZMod p) = (1 : ZMod p) := by
        calc (0 : ZMod p)
            = HexModArithMathlib.ZMod64.toZMod (0 : Hex.ZMod64 p) :=
              HexModArithMathlib.ZMod64.toZMod_zero.symm
          _ = HexModArithMathlib.ZMod64.toZMod (1 : Hex.ZMod64 p) :=
              congrArg _ h1
          _ = (1 : ZMod p) := HexModArithMathlib.ZMod64.toZMod_one
      exact one_ne_zero hz.symm
    · exact hpos
  have hlc : f.coeff (f.size - 1) = 1 := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hsize_pos]
    exact hmonic
  have hcoeff_one : (toMathlibPolynomial f).coeff (f.size - 1) = 1 := by
    rw [coeff_toMathlibPolynomial, hlc]
    exact HexModArithMathlib.ZMod64.toZMod_one
  have hub : (toMathlibPolynomial f).natDegree ≤ f.size - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro N hN
    rw [coeff_toMathlibPolynomial,
      Hex.DensePoly.coeff_eq_zero_of_size_le f (by omega)]
    exact HexModArithMathlib.ZMod64.toZMod_zero
  have hlb : f.size - 1 ≤ (toMathlibPolynomial f).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_one]; exact one_ne_zero)
  rw [le_antisymm hub hlb]
  unfold Hex.Berlekamp.basisSize Hex.DensePoly.degree?
  simp [Nat.ne_of_gt hsize_pos]

/-- Formal derivatives commute with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_derivative (f : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.derivative f) =
      Polynomial.derivative (toMathlibPolynomial f) := by
  ext n
  rw [coeff_toMathlibPolynomial,
    Hex.DensePoly.coeff_derivative f n (Lean.Grind.Semiring.mul_zero _),
    HexModArithMathlib.ZMod64.toZMod_mul, HexModArithMathlib.ZMod64.toZMod_natCast,
    Polynomial.coeff_derivative, coeff_toMathlibPolynomial]
  push_cast
  ring

/-- Multiplication commutes with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_mul (f g : Hex.FpPoly p) :
    toMathlibPolynomial (f * g) = toMathlibPolynomial f * toMathlibPolynomial g :=
  map_mul fpPolyEquiv f g

/-- Addition commutes with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_add (f g : Hex.FpPoly p) :
    toMathlibPolynomial (f + g) = toMathlibPolynomial f + toMathlibPolynomial g :=
  map_add fpPolyEquiv f g

/-- Subtraction commutes with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_sub (f g : Hex.FpPoly p) :
    toMathlibPolynomial (f - g) = toMathlibPolynomial f - toMathlibPolynomial g := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_sub, coeff_toMathlibPolynomial, coeff_toMathlibPolynomial,
    coeff_toMathlibPolynomial, Hex.DensePoly.coeff_sub_ring,
    HexModArithMathlib.ZMod64.toZMod_sub]

/-- The constant executable polynomial transports to the Mathlib constant. -/
theorem toMathlibPolynomial_C (c : Hex.ZMod64 p) :
    toMathlibPolynomial (Hex.DensePoly.C c) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c) := by
  apply Polynomial.ext
  intro n
  rw [coeff_toMathlibPolynomial, Hex.DensePoly.coeff_C, Polynomial.coeff_C]
  by_cases hn : n = 0
  · subst hn; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hn, if_neg hn]; exact HexModArithMathlib.ZMod64.toZMod_zero

/-- The monic monomial `X^m` transports to `X^m` over `ZMod p`. -/
theorem toMathlibPolynomial_monomial_one (m : Nat) :
    toMathlibPolynomial (Hex.DensePoly.monomial m (1 : Hex.ZMod64 p)) =
      (Polynomial.X : Polynomial (ZMod p)) ^ m := by
  apply Polynomial.ext
  intro n
  rw [coeff_toMathlibPolynomial, Hex.DensePoly.coeff_monomial, Polynomial.coeff_X_pow]
  by_cases hn : n = m
  · rw [if_pos hn, if_pos hn]; exact HexModArithMathlib.ZMod64.toZMod_one
  · rw [if_neg hn, if_neg hn]; exact HexModArithMathlib.ZMod64.toZMod_zero

/-- The executable indeterminate transports to Mathlib's `X`. -/
theorem toMathlibPolynomial_X :
    toMathlibPolynomial (Hex.FpPoly.X (p := p)) = (Polynomial.X : Polynomial (ZMod p)) := by
  apply Polynomial.ext
  intro n
  rw [coeff_toMathlibPolynomial, Hex.FpPoly.coeff_X, Polynomial.coeff_X]
  by_cases hn : n = 1
  · subst hn; rw [if_pos rfl, if_pos rfl, HexModArithMathlib.ZMod64.toZMod_one]
  · rw [if_neg hn, if_neg (show ¬ (1 = n) by omega), HexModArithMathlib.ZMod64.toZMod_zero]

/-- Divisibility transports along the finite-field polynomial map. -/
theorem toMathlibPolynomial_dvd {f g : Hex.FpPoly p} (h : f ∣ g) :
    toMathlibPolynomial f ∣ toMathlibPolynomial g := by
  obtain ⟨r, hr⟩ := h
  exact ⟨toMathlibPolynomial r, by rw [hr, toMathlibPolynomial_mul]⟩

/-- An executable unit polynomial (a nonzero constant) transports to a Mathlib
unit. -/
theorem isUnit_toMathlibPolynomial_of_isUnitPolynomial
    [Fact (Nat.Prime p)] {g : Hex.FpPoly p}
    (h : Hex.Berlekamp.isUnitPolynomial g = true) :
    IsUnit (toMathlibPolynomial g) := by
  -- `isUnitPolynomial g = true` means `g` has degree `0`, hence size `1`.
  have hdeg : g.degree? = some 0 := by
    unfold Hex.Berlekamp.isUnitPolynomial at h
    split at h <;> first | assumption | simp_all
  have hsize : g.size = 1 := by
    rcases Nat.eq_zero_or_pos g.size with hz | hpos
    · rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr hz] at hdeg
      exact absurd hdeg (by simp)
    · rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hpos] at hdeg
      have hsub : g.size - 1 = 0 := Option.some.inj hdeg
      omega
  -- So `g = C (g.coeff 0)` with `g.coeff 0 ≠ 0`.
  have hgC : g = Hex.DensePoly.C (g.coeff 0) := by
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_C]
    by_cases hi : i = 0
    · subst hi; rw [if_pos rfl]
    · rw [if_neg hi,
        Hex.DensePoly.coeff_eq_zero_of_size_le g (by omega : g.size ≤ i)]
  have hne : g.coeff 0 ≠ 0 := by
    have hlast := Hex.DensePoly.coeff_last_ne_zero_of_pos_size g (by omega : 0 < g.size)
    have key : g.coeff 0 ≠ Zero.zero := by simpa [hsize] using hlast
    exact key
  have htoZ_ne : HexModArithMathlib.ZMod64.toZMod (g.coeff 0) ≠ 0 := by
    intro hzero
    apply hne
    apply HexModArithMathlib.ZMod64.equiv.injective
    rw [HexModArithMathlib.ZMod64.equiv_apply, HexModArithMathlib.ZMod64.equiv_apply,
      HexModArithMathlib.ZMod64.toZMod_zero, hzero]
  have hC_eq : toMathlibPolynomial g =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod (g.coeff 0)) := by
    conv_lhs => rw [hgC]
    exact toMathlibPolynomial_C (g.coeff 0)
  rw [hC_eq]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr htoZ_ne)

/-- Transport executable `FpPoly.Irreducible` to Mathlib `Irreducible` over
`ZMod p`.

The positive Mathlib-degree hypothesis is essential: `FpPoly.Irreducible` holds
vacuously for any nonzero constant (every factorization has a degree-0 factor),
whereas such a constant transports to a Mathlib *unit*, not an irreducible.  At
the Berlekamp use site the emitted factors are nonconstant, so the hypothesis is
available. -/
theorem irreducible_toMathlibPolynomial_of_fpPolyIrreducible
    [Fact (Nat.Prime p)] {f : Hex.FpPoly p}
    (hpos : 0 < (toMathlibPolynomial f).natDegree)
    (hirr : Hex.FpPoly.Irreducible f) :
    Irreducible (toMathlibPolynomial f) := by
  refine ⟨fun h => Polynomial.not_isUnit_of_natDegree_pos _ hpos h, ?_⟩
  intro a b hab
  -- Pull `a`, `b` back through `fpPolyEquiv.symm` to executable factors of `f`.
  have ha : toMathlibPolynomial (fpPolyEquiv.symm a) = a := by
    rw [← fpPolyEquiv_apply, fpPolyEquiv.apply_symm_apply]
  have hb : toMathlibPolynomial (fpPolyEquiv.symm b) = b := by
    rw [← fpPolyEquiv_apply, fpPolyEquiv.apply_symm_apply]
  have hprod : fpPolyEquiv.symm a * fpPolyEquiv.symm b = f := by
    rw [← map_mul, ← hab, ← fpPolyEquiv_apply, fpPolyEquiv.symm_apply_apply]
  -- `FpPoly.Irreducible` forces one pulled-back factor to be a nonzero constant.
  rcases hirr.2 _ _ hprod with hdeg | hdeg
  · exact Or.inl (ha ▸ isUnit_toMathlibPolynomial_of_isUnitPolynomial
      (by unfold Hex.Berlekamp.isUnitPolynomial; rw [hdeg]; rfl))
  · exact Or.inr (hb ▸ isUnit_toMathlibPolynomial_of_isUnitPolynomial
      (by unfold Hex.Berlekamp.isUnitPolynomial; rw [hdeg]; rfl))

/-- The Mathlib primality fact yields the executable prime-modulus witness, so
executable field-dependent lemmas (gcd/Bezout, modular division) become
available in the Mathlib transport layer. -/
theorem primeModulus_of_fact (p : Nat) [Fact (Nat.Prime p)] :
    Hex.ZMod64.PrimeModulus p :=
  Hex.ZMod64.primeModulusOfPrime
    ⟨(Fact.out : Nat.Prime p).two_le,
      fun m hm => (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hm⟩

/-- A passing executable gcd-unit check transports to Mathlib coprimality of the
transported polynomials, via the executable Bezout identity. -/
theorem isCoprime_toMathlibPolynomial_of_isUnitPolynomial_gcd
    [Fact (Nat.Prime p)] {a b : Hex.FpPoly p}
    (h : Hex.Berlekamp.isUnitPolynomial (Hex.DensePoly.gcd a b) = true) :
    IsCoprime (toMathlibPolynomial a) (toMathlibPolynomial b) := by
  haveI : Hex.ZMod64.PrimeModulus p := primeModulus_of_fact p
  obtain ⟨u, hu⟩ := isUnit_toMathlibPolynomial_of_isUnitPolynomial h
  -- Executable Bezout: `left * a + right * b = gcd a b`.
  have hbez : (Hex.DensePoly.xgcd a b).left * a + (Hex.DensePoly.xgcd a b).right * b
      = Hex.DensePoly.gcd a b :=
    (Hex.DensePoly.xgcd_bezout a b).trans (Hex.DensePoly.xgcd_gcd_eq_gcd a b)
  have hbezM :
      toMathlibPolynomial (Hex.DensePoly.xgcd a b).left * toMathlibPolynomial a +
        toMathlibPolynomial (Hex.DensePoly.xgcd a b).right * toMathlibPolynomial b =
        toMathlibPolynomial (Hex.DensePoly.gcd a b) := by
    rw [← toMathlibPolynomial_mul, ← toMathlibPolynomial_mul, ← toMathlibPolynomial_add, hbez]
  refine ⟨↑u⁻¹ * toMathlibPolynomial (Hex.DensePoly.xgcd a b).left,
    ↑u⁻¹ * toMathlibPolynomial (Hex.DensePoly.xgcd a b).right, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hbezM, ← hu]
  exact u.inv_mul

namespace Rabin

/-- The Mathlib polynomial `X^(p^n) - X` used by Rabin's divisibility leg. -/
abbrev frobeniusPolynomial (p n : Nat) : Polynomial (ZMod p) :=
  X ^ (p ^ n) - X

/-- The executable absolute polynomial `X^(p^k) - X` transports to
`frobeniusPolynomial p k`. -/
theorem toMathlibPolynomial_xPowSubX (k : Nat) :
    toMathlibPolynomial (Hex.Berlekamp.xPowSubX (p := p) k) = frobeniusPolynomial p k := by
  unfold Hex.Berlekamp.xPowSubX frobeniusPolynomial
  rw [toMathlibPolynomial_sub, toMathlibPolynomial_monomial_one, toMathlibPolynomial_X]

/-
Divisibility by the modulus is exactly vanishing in the corresponding
`AdjoinRoot` quotient.
-/
omit [Hex.ZMod64.Bounds p] in
theorem adjoinRoot_mk_eq_zero_of_dvd
    (g P : Polynomial (ZMod p)) :
    AdjoinRoot.mk g P = 0 ↔ g ∣ P := by
  exact AdjoinRoot.mk_eq_zero

/--
If an irreducible `g` divides `X^(p^n) - X`, its quotient root maps into the
degree-`n` Galois field over `ZMod p`.
-/
theorem exists_algHom_adjoinRoot_to_galoisField
    [Fact (Nat.Prime p)] {n : Nat} (hn : n ≠ 0)
    {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hg_dvd : g ∣ frobeniusPolynomial p n) :
    Nonempty (AdjoinRoot g →ₐ[ZMod p] GaloisField p n) := by
  haveI : Fact (Irreducible g) := ⟨hg_irreducible⟩
  have hg_ne_zero : g ≠ 0 := hg_irreducible.ne_zero
  have hg_dvd' : g ∣ X ^ Nat.card (ZMod p) ^ n - X := by
    simpa [frobeniusPolynomial, Nat.card_zmod] using hg_dvd
  have hdegree_dvd : g.natDegree ∣ n := by
    exact
      (Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
        (K := ZMod p) (n := n) (f := g) hg_irreducible hg_dvd')
  have hfinrank_dvd :
      Module.finrank (ZMod p) (AdjoinRoot g) ∣
        Module.finrank (ZMod p) (GaloisField p n) := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hg_ne_zero),
      AdjoinRoot.powerBasis_dim hg_ne_zero, GaloisField.finrank p hn]
    exact hdegree_dvd
  exact FiniteField.nonempty_algHom_of_finrank_dvd hfinrank_dvd

/-
The finite-dimensional rank of an `AdjoinRoot` quotient by a nonzero
polynomial is its natural degree.
-/
omit [Hex.ZMod64.Bounds p] in
theorem finrank_adjoinRoot_eq_natDegree
    [Fact (Nat.Prime p)] {g : Polynomial (ZMod p)} (hg : g ≠ 0) :
    Module.finrank (ZMod p) (AdjoinRoot g) = g.natDegree := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hg),
    AdjoinRoot.powerBasis_dim hg]

/--
The Rabin finite-field degree lemma in the local `ZMod p` form used by the
contrapositive proof.
-/
theorem natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
    [Fact (Nat.Prime p)] {n : Nat} {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hg_dvd : g ∣ frobeniusPolynomial p n) :
    g.natDegree ∣ n := by
  have hg_dvd' : g ∣ X ^ Nat.card (ZMod p) ^ n - X := by
    simpa [frobeniusPolynomial, Nat.card_zmod] using hg_dvd
  exact
    (Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      (K := ZMod p) (n := n) (f := g) hg_irreducible hg_dvd')

/-
For an irreducible polynomial, any nontrivial gcd/coprimality failure with
`P` forces divisibility by `P`.
-/
omit [Hex.ZMod64.Bounds p] in
theorem irreducible_dvd_of_not_isCoprime
    [Fact (Nat.Prime p)] {g P : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hnot_coprime : ¬ IsCoprime g P) :
    g ∣ P := by
  by_contra hnot_dvd
  exact hnot_coprime ((hg_irreducible.coprime_iff_not_dvd).2 hnot_dvd)

/--
The Rabin backward direction in the local `ZMod p` form: every irreducible
polynomial of degree dividing `N` divides `X^(p^N) - X`.

Used by the contrapositive direction of `rabinTest_true_irreducible` to lift
divisibility of an irreducible factor `g` from the basis-size Frobenius
polynomial down to the Frobenius polynomial at a maximal proper divisor.
-/
theorem irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
    [Fact (Nat.Prime p)] {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g) {N : Nat}
    (hdvd : g.natDegree ∣ N) :
    g ∣ frobeniusPolynomial p N := by
  haveI : Fact (Irreducible g) := ⟨hg_irreducible⟩
  have hg_ne_zero : g ≠ 0 := hg_irreducible.ne_zero
  haveI : Module.Finite (ZMod p) (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis hg_ne_zero).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = p ^ g.natDegree := by
    rw [← Nat.card_eq_fintype_card,
        ← FiniteField.pow_finrank_eq_natCard p (AdjoinRoot g),
        PowerBasis.finrank (AdjoinRoot.powerBasis hg_ne_zero),
        AdjoinRoot.powerBasis_dim hg_ne_zero]
  have hroot_pow : (AdjoinRoot.root g) ^ (p ^ N) = AdjoinRoot.root g := by
    obtain ⟨k, rfl⟩ := hdvd
    rw [pow_mul]
    have hpow := FiniteField.pow_card_pow (K := AdjoinRoot g) k (AdjoinRoot.root g)
    rwa [hcard] at hpow
  have hgoal : (AdjoinRoot.mk g) (frobeniusPolynomial p N) = 0 := by
    show (AdjoinRoot.mk g) (X ^ p ^ N - X) = 0
    rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, Polynomial.aeval_X, hroot_pow, sub_self]
  exact AdjoinRoot.mk_eq_zero.mp hgoal

/-- Maximal proper divisors are positive. -/
theorem maximalProperDivisors_pos {n d : Nat}
    (hmem : d ∈ Hex.Berlekamp.maximalProperDivisors n) :
    0 < d := by
  unfold Hex.Berlekamp.maximalProperDivisors Hex.Berlekamp.properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨⟨⟨k, _hk, rfl⟩, _hdvd⟩, _hmax⟩
  exact Nat.succ_pos k

/-- Maximal proper divisors are strictly below the ambient degree. -/
theorem maximalProperDivisors_lt {n d : Nat}
    (hmem : d ∈ Hex.Berlekamp.maximalProperDivisors n) :
    d < n := by
  unfold Hex.Berlekamp.maximalProperDivisors Hex.Berlekamp.properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨⟨⟨k, hk, rfl⟩, _hdvd⟩, _hmax⟩
  omega

/--
Divisor arithmetic used by Rabin's reducible contrapositive: a proper divisor
`d` of `n` yields a prime `q` such that `q ∣ n` and `d ∣ n / q`.
-/
theorem exists_prime_divisor_with_divisor_quotient
    {d n : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ q : Nat, Nat.Prime q ∧ q ∣ n / d ∧ q ∣ n ∧ d ∣ n / q := by
  obtain ⟨c, hc⟩ := hd_dvd
  -- `c = n / d ≥ 2`, since `d < n = d * c` with `d > 0` forces `c > 1`.
  have hc_ge : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c <;> omega
    · exact h
  have hnd : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd_pos
  have hc_ne : n / d ≠ 1 := by rw [hnd]; omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hc_ne
  have hq_pos : 0 < q := hq_prime.pos
  -- `c ∣ n` because `n = d * c = c * d`.
  have hc_dvd_n : c ∣ n := ⟨d, by rw [hc, Nat.mul_comm]⟩
  have hq_dvd_c : q ∣ c := by rwa [hnd] at hq_dvd
  have hq_dvd_n : q ∣ n := dvd_trans hq_dvd_c hc_dvd_n
  -- write `c = q * m`, so `n = q * (d * m)` and `n / q = d * m`.
  obtain ⟨m, hm⟩ := hq_dvd_c
  have hnq : n / q = d * m := by
    rw [hc, hm, show d * (q * m) = q * (d * m) from by ring]
    exact Nat.mul_div_cancel_left (d * m) hq_pos
  have hd_dvd_nq : d ∣ n / q := by rw [hnq]; exact ⟨m, rfl⟩
  exact ⟨q, hq_prime, hq_dvd, hq_dvd_n, hd_dvd_nq⟩

/--
The executable Rabin test passing entails the exact Mathlib divisibility and
coprimality checks appearing in Rabin's criterion.
-/
theorem rabinTest_true_to_mathlib_checks
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n)
    (htest : Hex.Berlekamp.rabinTest f hmonic = true) :
    0 < n ∧
      toMathlibPolynomial f ∣ frobeniusPolynomial p n ∧
      ∀ d ∈ Hex.Berlekamp.maximalProperDivisors n,
        IsCoprime (toMathlibPolynomial f) (frobeniusPolynomial p d) := by
  haveI : Hex.ZMod64.PrimeModulus p := primeModulus_of_fact p
  subst hdegree
  simp only [Hex.Berlekamp.rabinTest, Bool.and_eq_true] at htest
  obtain ⟨⟨hpos, hdiv⟩, hwit⟩ := htest
  refine ⟨of_decide_eq_true hpos, ?_, ?_⟩
  · -- Divisibility leg: transport `f ∣ X^(p^n) - X` from the executable side.
    have hisZero : (Hex.Berlekamp.frobeniusDiffMod f hmonic
        (Hex.Berlekamp.basisSize f)).isZero = true := by
      rw [← Hex.Berlekamp.rabinDividesTest_spec]; exact hdiv
    have hdvd := (Hex.Berlekamp.dvd_xPowSubX_iff_frobeniusDiffMod_isZero f hmonic _).mpr hisZero
    rw [← toMathlibPolynomial_xPowSubX]
    exact toMathlibPolynomial_dvd hdvd
  · -- Coprimality leg: transport the gcd-unit witnesses, then reduce
    -- `frobeniusDiffMod` to the absolute `X^(p^d) - X`.
    intro d hd
    have hcop := Hex.Berlekamp.rabinCoprimeTest_of_mem_maximalProperDivisors f hmonic hwit hd
    rw [Hex.Berlekamp.rabinCoprimeTest] at hcop
    have hcopM :
        IsCoprime (toMathlibPolynomial f)
          (toMathlibPolynomial (Hex.Berlekamp.frobeniusDiffMod f hmonic d)) :=
      isCoprime_toMathlibPolynomial_of_isUnitPolynomial_gcd hcop
    have hredM : toMathlibPolynomial f ∣
        (frobeniusPolynomial p d -
          toMathlibPolynomial (Hex.Berlekamp.frobeniusDiffMod f hmonic d)) := by
      have hred := toMathlibPolynomial_dvd
        (Hex.Berlekamp.dvd_xPowSubX_sub_frobeniusDiffMod f hmonic d)
      rwa [toMathlibPolynomial_sub, toMathlibPolynomial_xPowSubX] at hred
    obtain ⟨t, ht⟩ := hredM
    have hfrob_eq : frobeniusPolynomial p d =
        toMathlibPolynomial (Hex.Berlekamp.frobeniusDiffMod f hmonic d) +
          toMathlibPolynomial f * t := by
      rw [← ht]; ring
    rw [hfrob_eq]
    exact hcopM.add_mul_left_right t

/--
The Mathlib Rabin checks imply the executable test surface once the transport
lemmas connect executable remainders and gcds to `Polynomial (ZMod p)`.
-/
theorem rabinTest_true_of_mathlib_checks
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n)
    (hchecks :
      0 < n ∧
        toMathlibPolynomial f ∣ frobeniusPolynomial p n ∧
        ∀ d ∈ Hex.Berlekamp.maximalProperDivisors n,
          IsCoprime (toMathlibPolynomial f) (frobeniusPolynomial p d)) :
    Hex.Berlekamp.rabinTest f hmonic = true := by
  -- Build the executable prime-modulus instance from `Fact (Nat.Prime p)`.
  have hp_hex : Hex.Nat.Prime p := by
    refine ⟨(Fact.out : Nat.Prime p).two_le, ?_⟩
    intro m hmdvd
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  haveI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hp_hex
  obtain ⟨hn_pos, hdvd, hcoprime⟩ := hchecks
  -- Transport executable divisibility along the ring iso, in both directions.
  have transport : ∀ {a b : Hex.FpPoly p}, a ∣ b →
      toMathlibPolynomial a ∣ toMathlibPolynomial b := by
    rintro a b ⟨r, hr⟩
    exact ⟨toMathlibPolynomial r, by rw [hr]; exact map_mul fpPolyEquiv a r⟩
  have untransport : ∀ {a b : Hex.FpPoly p},
      toMathlibPolynomial a ∣ toMathlibPolynomial b → a ∣ b := by
    rintro a b ⟨R, hR⟩
    refine ⟨fpPolyEquiv.symm R, ?_⟩
    apply fpPolyEquiv.injective
    rw [map_mul, fpPolyEquiv.apply_symm_apply]
    exact hR
  rw [Hex.Berlekamp.rabinTest_eq_true_iff]
  refine ⟨by rw [hdegree]; exact hn_pos, ?_, ?_⟩
  · -- Divisibility leg: untransport `M f ∣ frobeniusPolynomial p n` to `f ∣ xPowSubX n`.
    apply untransport
    rw [toMathlibPolynomial_xPowSubX, hdegree]
    exact hdvd
  · -- Coprimality leg: each maximal-proper-divisor witness is accepted.
    rw [List.all_eq_true]
    intro x hx
    rw [Hex.Berlekamp.rabinWitnesses, List.mem_map] at hx
    obtain ⟨d, hd_mem, rfl⟩ := hx
    show Hex.Berlekamp.rabinCoprimeTest f hmonic d = true
    rw [hdegree] at hd_mem
    have hcop_d := hcoprime d hd_mem
    unfold Hex.Berlekamp.rabinCoprimeTest
    -- Let `g` be the executable gcd of `f` and `diff = frobeniusDiffMod f hmonic d`.
    have hg_dvd_f : Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d) ∣ f :=
      Hex.DensePoly.gcd_dvd_left _ _
    have hg_dvd_diff :
        Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d) ∣
          Hex.Berlekamp.frobeniusDiffMod f hmonic d :=
      Hex.DensePoly.gcd_dvd_right _ _
    have hg_dvd_xpow :
        Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d) ∣
          Hex.Berlekamp.xPowSubX (p := p) d :=
      Hex.Berlekamp.dvd_xPowSubX_of_dvd_frobeniusDiffMod hmonic hg_dvd_f hg_dvd_diff
    -- Transport the two divisibilities and read off a Bezout combination of `1`.
    have hMg_dvd_Mf := transport hg_dvd_f
    have hMg_dvd_frob :
        toMathlibPolynomial (Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d)) ∣
          frobeniusPolynomial p d := by
      have h := transport hg_dvd_xpow
      rwa [toMathlibPolynomial_xPowSubX] at h
    obtain ⟨u, v, huv⟩ := hcop_d
    have hMg_dvd_one :
        toMathlibPolynomial (Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d)) ∣
          (1 : Polynomial (ZMod p)) := by
      rw [← huv]
      exact dvd_add (hMg_dvd_Mf.mul_left u) (hMg_dvd_frob.mul_left v)
    have h_one : toMathlibPolynomial (1 : Hex.FpPoly p) = 1 := by
      apply Polynomial.ext
      intro m
      rw [coeff_toMathlibPolynomial,
        show (1 : Hex.FpPoly p) = Hex.DensePoly.C (1 : Hex.ZMod64 p) from rfl,
        Hex.DensePoly.coeff_C, Polynomial.coeff_one]
      by_cases hm : m = 0
      · simp [hm, HexModArithMathlib.ZMod64.toZMod_one]
      · rw [if_neg hm, if_neg hm]; exact HexModArithMathlib.ZMod64.toZMod_zero
    have hg_dvd_one :
        Hex.DensePoly.gcd f (Hex.Berlekamp.frobeniusDiffMod f hmonic d) ∣ (1 : Hex.FpPoly p) := by
      apply untransport
      rw [h_one]
      exact hMg_dvd_one
    exact Hex.Berlekamp.isUnitPolynomial_of_dvd_isUnitPolynomial hg_dvd_one
      Hex.Berlekamp.isUnitPolynomial_one_FpPoly

end Rabin

/--
Executable gcd is associated to Mathlib's gcd after coefficient transport.

`toMathlibPolynomial = fpPolyEquiv` is a ring iso, so executable divisibility
transports both ways; feeding the executable `GcdLaws` through it shows the
transported gcd satisfies Mathlib's gcd universal property. The two are only
*associated*, not equal, because the executable gcd is the last nonzero xgcd
remainder with no monic rescale while Mathlib's gcd is `normalize`-canonical.
-/
theorem toMathlibPolynomial_gcd_associated
    [Fact (Nat.Prime p)] (f g : Hex.FpPoly p) :
    Associated (toMathlibPolynomial (Hex.DensePoly.gcd f g))
      (gcd (toMathlibPolynomial f) (toMathlibPolynomial g)) := by
  have hp_hex : Hex.Nat.Prime p := by
    refine ⟨(Fact.out : Nat.Prime p).two_le, ?_⟩
    intro m hmdvd
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  haveI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hp_hex
  -- The executable `∣` is custom (`∃ r, b = a * r`), so transport it through the
  -- iso by destructuring and re-multiplying rather than via `map_dvd`.
  have transport : ∀ {a b : Hex.FpPoly p}, a ∣ b →
      toMathlibPolynomial a ∣ toMathlibPolynomial b := by
    rintro a b ⟨r, hr⟩
    exact ⟨toMathlibPolynomial r, by rw [hr]; exact map_mul fpPolyEquiv a r⟩
  have untransport : ∀ {a b : Hex.FpPoly p},
      toMathlibPolynomial a ∣ toMathlibPolynomial b → a ∣ b := by
    rintro a b ⟨R, hR⟩
    refine ⟨fpPolyEquiv.symm R, ?_⟩
    apply fpPolyEquiv.injective
    rw [map_mul, fpPolyEquiv.apply_symm_apply]
    exact hR
  apply associated_of_dvd_dvd
  · exact dvd_gcd (transport (Hex.DensePoly.gcd_dvd_left f g))
      (transport (Hex.DensePoly.gcd_dvd_right f g))
  · set d : Hex.FpPoly p :=
      fpPolyEquiv.symm (gcd (toMathlibPolynomial f) (toMathlibPolynomial g)) with hd
    have hsymm :
        toMathlibPolynomial d = gcd (toMathlibPolynomial f) (toMathlibPolynomial g) := by
      rw [hd]; exact fpPolyEquiv.apply_symm_apply _
    have hdf : d ∣ f := by
      apply untransport; rw [hsymm]; exact gcd_dvd_left _ _
    have hdg : d ∣ g := by
      apply untransport; rw [hsymm]; exact gcd_dvd_right _ _
    rw [← hsymm]
    exact transport (Hex.DensePoly.dvd_gcd d f g hdf hdg)

/--
Executable gcd transfers to Mathlib's gcd after coefficient transport, up to
normalization. The executable `Hex.DensePoly.gcd` is the last nonzero xgcd
remainder and is not monic, while Mathlib's `gcd` applies `normalize`; the two
coincide only after normalizing the transport. Coprimality is a unit-gcd
statement, so this up-to-unit shape is the correct primitive for downstream
square-free reasoning.
-/
theorem toMathlibPolynomial_gcd_normalize
    [Fact (Nat.Prime p)] (f g : Hex.FpPoly p) :
    normalize (toMathlibPolynomial (Hex.DensePoly.gcd f g)) =
      gcd (toMathlibPolynomial f) (toMathlibPolynomial g) := by
  rw [normalize_eq_normalize_iff_associated.mpr (toMathlibPolynomial_gcd_associated f g),
    normalize_gcd]

/--
The executable square-free hypothesis used by Berlekamp is the corresponding
Mathlib coprimality condition between the transported polynomial and its
formal derivative.
-/
theorem toMathlibPolynomial_squareFree_coprime
    [Fact (Nat.Prime p)] (f : Hex.FpPoly p)
    (hsquareFree :
      Hex.Berlekamp.isUnitPolynomial
        (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    IsCoprime (toMathlibPolynomial f) (Polynomial.derivative (toMathlibPolynomial f)) := by
  let g : Hex.FpPoly p := Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)
  have hg_size : g.size = 1 := by
    have hdeg : g.degree? = some 0 := by
      unfold Hex.Berlekamp.isUnitPolynomial at hsquareFree
      cases h : g.degree? with
      | none =>
          rw [h] at hsquareFree
          simp at hsquareFree
      | some n =>
          rw [h] at hsquareFree
          cases n with
          | zero => simp
          | succ n => simp at hsquareFree
    have hpos : 0 < g.size := by
      by_contra hnot
      have hzero : g.size = 0 := by omega
      have hnone : g.degree? = none :=
        (Hex.DensePoly.degree?_eq_none_iff g).mpr hzero
      rw [hdeg] at hnone
      contradiction
    have hdeg_size : g.degree? = some (g.size - 1) :=
      Hex.DensePoly.degree?_eq_some_of_pos_size g hpos
    rw [hdeg] at hdeg_size
    injection hdeg_size with hsub
    omega
  have hg_pos : 0 < g.size := by omega
  have hg_coeff_ne : g.coeff 0 ≠ 0 := by
    have hlast := Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hg_pos
    have key : g.coeff 0 ≠ Zero.zero := by simpa [hg_size] using hlast
    exact key
  have hg_coeff_zmod_ne :
      HexModArithMathlib.ZMod64.toZMod (g.coeff 0) ≠ 0 := by
    intro hzero
    apply hg_coeff_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
    apply hinj
    simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  have hg_poly_unit : IsUnit (toMathlibPolynomial g) := by
    have hg_poly_eq :
        toMathlibPolynomial g =
          Polynomial.C (HexModArithMathlib.ZMod64.toZMod (g.coeff 0)) := by
      ext n
      cases n with
      | zero =>
          simp [coeff_toMathlibPolynomial]
      | succ n =>
          rw [coeff_toMathlibPolynomial,
            Hex.DensePoly.coeff_eq_zero_of_size_le g (by omega)]
          rw [Polynomial.coeff_C]
          exact HexModArithMathlib.ZMod64.toZMod_zero (p := p)
    rw [hg_poly_eq]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hg_coeff_zmod_ne)
  have hmath_gcd_unit :
      IsUnit (gcd (toMathlibPolynomial f)
        (Polynomial.derivative (toMathlibPolynomial f))) := by
    rw [← toMathlibPolynomial_derivative f]
    exact (toMathlibPolynomial_gcd_associated f (Hex.DensePoly.derivative f)).isUnit
      hg_poly_unit
  exact (gcd_isUnit_iff_isRelPrime.mp hmath_gcd_unit).isCoprime

/-- A factor with positive executable degree transports to a Mathlib polynomial
of positive `natDegree`: its leading coefficient is nonzero and the (injective)
coefficient transport preserves that, so the top coefficient survives. -/
theorem natDegree_toMathlibPolynomial_pos_of_degree?_pos
    {g : Hex.FpPoly p} (hg : 0 < g.degree?.getD 0) :
    0 < (toMathlibPolynomial g).natDegree := by
  have hsize_pos : 0 < g.size := by
    rcases Nat.eq_zero_or_pos g.size with hz | hpos
    · rw [Hex.DensePoly.degree?] at hg; simp [hz] at hg
    · exact hpos
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hsize_pos, Option.getD_some] at hg
  have hcoeff_ne : g.coeff (g.size - 1) ≠ 0 :=
    Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hsize_pos
  have hcoeff_zmod_ne : (toMathlibPolynomial g).coeff (g.size - 1) ≠ 0 := by
    rw [coeff_toMathlibPolynomial]
    intro hzero
    apply hcoeff_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
    apply hinj
    simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  have hlb : g.size - 1 ≤ (toMathlibPolynomial g).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_zmod_ne
  omega

/--
Every factor emitted by executable Berlekamp factorization on a positive-degree
input is irreducible after transport to Mathlib's polynomial model, assuming the
square-free input in the common-divisor form used by the executable soundness
chain.  The positive-degree input hypothesis is essential: emitted factors of a
constant input are themselves constant, transporting to Mathlib *units* rather
than irreducibles.
-/
theorem irreducible_of_mem_berlekampFactor
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)]
    (hf_pos : 0 < f.degree?.getD 0)
    (hsquareFree : ∀ d, d ∣ f → d ∣ Hex.DensePoly.derivative f →
      Hex.Berlekamp.isUnitPolynomial d = true) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) := by
  intro g hg
  have hg_pos :=
    Hex.Berlekamp.berlekampFactor_factors_pos_degree f hmonic hf_pos g hg
  exact irreducible_toMathlibPolynomial_of_fpPolyIrreducible
    (natDegree_toMathlibPolynomial_pos_of_degree?_pos hg_pos)
    (Hex.Berlekamp.berlekampFactor_factors_irreducible f hmonic hsquareFree g hg)

/--
Every factor emitted by executable Berlekamp factorization is irreducible after
transport to Mathlib's polynomial model.
-/
theorem irreducible_of_mem_berlekampFactor_of_gcd_eq_one
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)]
    (hf_pos : 0 < f.degree?.getD 0)
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) :=
  irreducible_of_mem_berlekampFactor f hmonic hf_pos
    (Hex.Berlekamp.squareFree_common_of_gcd_eq_one hsquareFree)

/--
Mathlib-side re-export of the Mathlib-free Nodup property of the executable
Berlekamp factor list of a monic square-free input.  Discharged from the
polymorphic abstract loop invariant
`Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared` plus the
squareness-implies-unit chain `isUnitPolynomial_of_squareFree_of_squared_dvd`,
matching the proof of the section-level `Hex.Berlekamp.berlekampFactor_factors_nodup`
in `HexBerlekamp/RabinSoundness.lean`.  Stated polymorphic over the field
instance so that downstream Mathlib-side callers (e.g.
`factorsModP_nodup_of_factorsModPBerlekampForm`) can apply it to the
existentially-bound field witness carried by `factorsModPBerlekampForm`.
-/
theorem berlekampFactor_factors_nodup
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)] [Hex.ZMod64.PrimeModulus p]
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    (Hex.Berlekamp.berlekampFactor f hmonic).factors.Nodup := by
  apply Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared
  intro g hgg hpos
  have hunit : Hex.Berlekamp.isUnitPolynomial g = true :=
    Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd
      (Hex.Berlekamp.squareFree_common_of_gcd_eq_one hsquareFree) hgg
  have hdeg : Hex.DensePoly.degree? g = some 0 := by
    unfold Hex.Berlekamp.isUnitPolynomial at hunit
    cases hd : Hex.DensePoly.degree? g with
    | none => rw [hd] at hunit; simp at hunit
    | some k =>
        rw [hd] at hunit
        cases k with
        | zero => rfl
        | succ _ => simp at hunit
  rw [hdeg] at hpos
  simp at hpos

/--
If executable Berlekamp factorization cannot split a monic square-free input,
then the input itself is irreducible after transport to Mathlib.

The executable factor list is never empty; with length at most one, its head is
therefore a member of the Berlekamp output, so the existing per-emitted-factor
irreducibility theorem applies directly.
-/
theorem irreducible_of_berlekampFactor_factors_length_le_one
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)]
    (hf_pos : 0 < f.degree?.getD 0)
    (hsquareFree :
      Hex.Berlekamp.isUnitPolynomial
        (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true)
    (hsmall : (Hex.Berlekamp.berlekampFactor f hmonic).factors.length ≤ 1) :
    Irreducible (toMathlibPolynomial f) := by
  have hsquareFree_common :
      ∀ d, d ∣ f → d ∣ Hex.DensePoly.derivative f →
        Hex.Berlekamp.isUnitPolynomial d = true := by
    intro d hdf hdd
    exact Hex.Berlekamp.isUnitPolynomial_of_dvd_gcd_isUnit hdf hdd hsquareFree
  cases hfactors : (Hex.Berlekamp.berlekampFactor f hmonic).factors with
  | nil =>
      exact False.elim
        (Hex.Berlekamp.berlekampFactor_factors_ne_nil f hmonic hfactors)
  | cons g rest =>
      cases rest with
      | nil =>
          have hg_eq : g = f := by
            have hprod := Hex.Berlekamp.factorProduct_berlekampFactor f hmonic
            simp [hfactors, Hex.Berlekamp.factorProduct_cons] at hprod
            exact hprod
          have hirr_g :
              Irreducible (toMathlibPolynomial g) :=
            irreducible_of_mem_berlekampFactor
              f hmonic hf_pos hsquareFree_common g (by simp [hfactors])
          simpa [hg_eq] using hirr_g
      | cons h rest =>
          simp [hfactors] at hsmall

/--
Forward Rabin soundness: when the executable Rabin test accepts, the
transported Mathlib polynomial is irreducible.
-/
theorem rabinTest_true_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] :
    Hex.Berlekamp.rabinTest f hmonic = true →
      Irreducible (toMathlibPolynomial f) := by
  intro htest
  set fM := toMathlibPolynomial f
  set n := Hex.Berlekamp.basisSize f
  obtain ⟨hpos, hf_dvd, hcoprime⟩ :=
    Rabin.rabinTest_true_to_mathlib_checks f hmonic rfl htest
  have hfM_monic : fM.Monic := toMathlibPolynomial_monic f hmonic
  have hfM_natDegree : fM.natDegree = n :=
    natDegree_toMathlibPolynomial_eq_basisSize f hmonic
  have hfM_pos : 0 < fM.natDegree := hfM_natDegree.symm ▸ hpos
  refine ⟨fun hunit => by
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega, ?_⟩
  intro a b hab
  by_contra hcontr
  push Not at hcontr
  obtain ⟨ha_not_unit, hb_not_unit⟩ := hcontr
  have hfM_ne_zero : fM ≠ 0 := hfM_monic.ne_zero
  have ha_ne_zero : a ≠ 0 := fun h => by
    subst h; simp [zero_mul] at hab; exact hfM_ne_zero hab
  have hb_ne_zero : b ≠ 0 := fun h => by
    subst h; simp [mul_zero] at hab; exact hfM_ne_zero hab
  -- Both factors are nonconstant divisors of a monic polynomial.
  have hb_natDegree_pos : 0 < b.natDegree :=
    Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hfM_monic hb_not_unit
      (hab ▸ dvd_mul_left b a)
  have ha_natDegree_lt : a.natDegree < n := by
    have hsum : a.natDegree + b.natDegree = n := by
      rw [← hfM_natDegree, hab, Polynomial.natDegree_mul ha_ne_zero hb_ne_zero]
    omega
  -- Pick an irreducible factor `g` of `a`; then `g ∣ fM` and `g ∣ X^(p^n) - X`.
  obtain ⟨g, hg_irr, hg_dvd_a⟩ :=
    WfDvdMonoid.exists_irreducible_factor ha_not_unit ha_ne_zero
  have hg_dvd_fM : g ∣ fM := hg_dvd_a.trans (hab ▸ dvd_mul_right a b)
  have hg_natDegree_dvd_n : g.natDegree ∣ n :=
    Rabin.natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
      hg_irr (hg_dvd_fM.trans hf_dvd)
  -- `natDegree g < n` because `natDegree g ≤ natDegree a < n`.
  have hg_natDegree_lt : g.natDegree < n :=
    lt_of_le_of_lt
      (Polynomial.natDegree_le_of_dvd hg_dvd_a ha_ne_zero) ha_natDegree_lt
  -- Route `natDegree g` through some maximal proper divisor of `n`.
  obtain ⟨m, hm_mem, hg_natDegree_dvd_m⟩ :=
    Hex.Berlekamp.exists_maximalProperDivisor_dvd
      hg_irr.natDegree_pos hg_natDegree_dvd_n hg_natDegree_lt
  -- The Rabin coprimality leg at `m` and the new lemma combine to force
  -- `g` to be a unit, contradicting irreducibility.
  exact hg_irr.not_isUnit ((hcoprime m hm_mem).isUnit_of_dvd' hg_dvd_fM
    (Rabin.irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
      hg_irr hg_natDegree_dvd_m))

/--
Rabin's executable test is equivalent to Mathlib irreducibility for the
transported polynomial.
-/
theorem rabin_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] (n : Nat) (hdegree : Hex.Berlekamp.basisSize f = n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  constructor
  · exact rabinTest_true_irreducible f hmonic
  · intro hirr
    set fM := toMathlibPolynomial f
    have hfM_monic : fM.Monic := toMathlibPolynomial_monic f hmonic
    have hfM_natDegree : fM.natDegree = n := by
      simpa [fM, hdegree] using natDegree_toMathlibPolynomial_eq_basisSize f hmonic
    have hn_pos : 0 < n := by
      have hpos : 0 < fM.natDegree :=
        hfM_monic.natDegree_pos_of_not_isUnit hirr.not_isUnit
      simpa [hfM_natDegree] using hpos
    refine Rabin.rabinTest_true_of_mathlib_checks f hmonic hdegree ?_
    refine ⟨hn_pos, ?_, ?_⟩
    · have hdiv : fM.natDegree ∣ n := by
        rw [hfM_natDegree]
      simpa [fM] using
        Rabin.irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
          (p := p) (g := fM) hirr hdiv
    · intro d hd_mem
      by_contra hnot_coprime
      have hdiv_d : fM ∣ Rabin.frobeniusPolynomial p d :=
        Rabin.irreducible_dvd_of_not_isCoprime hirr hnot_coprime
      have hn_dvd_d : n ∣ d := by
        have hdeg_dvd :
            fM.natDegree ∣ d :=
          Rabin.natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
            hirr hdiv_d
        simpa [hfM_natDegree] using hdeg_dvd
      have hd_pos : 0 < d := Rabin.maximalProperDivisors_pos hd_mem
      have hn_le_d : n ≤ d := Nat.le_of_dvd hd_pos hn_dvd_d
      have hd_lt_n : d < n := Rabin.maximalProperDivisors_lt hd_mem
      exact (not_lt_of_ge hn_le_d) hd_lt_n

/--
Rabin's executable test is equivalent to Mathlib irreducibility with the
explicit positive-degree hypothesis used by the finite-field proof.
-/
theorem rabin_irreducible_of_positive_degree
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n) (_hpos : 0 < n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  exact rabin_irreducible f hmonic n hdegree

/--
Accepted executable irreducibility certificates imply Mathlib irreducibility
after transporting the checked polynomial to `Polynomial (ZMod p)`.
-/
theorem checkIrreducibilityCertificate_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)]
    (cert : Hex.Berlekamp.IrreducibilityCertificate) :
    Hex.Berlekamp.checkIrreducibilityCertificate f hmonic cert = true →
      Irreducible (toMathlibPolynomial f) := by
  intro hcheck
  exact rabinTest_true_irreducible f hmonic
    (Hex.Berlekamp.checkIrreducibilityCertificate_rabinTest f hmonic cert hcheck)

/-- Mathlib irreducibility over `Polynomial (ZMod p)` is classically decidable. -/
instance irreducibleDecidablePred (p : Nat) [Fact (Nat.Prime p)] :
    DecidablePred (fun f : Polynomial (ZMod p) => Irreducible f) :=
  Classical.decPred _

end

end HexBerlekampMathlib
