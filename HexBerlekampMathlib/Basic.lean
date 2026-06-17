import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexBerlekamp.RabinSoundness
import HexModArithMathlib
import HexPolyMathlib
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField

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
  rw [fpPolyToPolynomial, Polynomial.finset_sum_coeff]
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
def toMathlibPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  fpPolyEquiv f

@[simp]
theorem fpPolyEquiv_apply (f : Hex.FpPoly p) :
    fpPolyEquiv f = toMathlibPolynomial f := by
  rfl

@[simp]
theorem fpPolyEquiv_symm_apply (f : Polynomial (ZMod p)) :
    fpPolyEquiv.symm f = polynomialToFpPoly f := by
  rfl

@[simp]
theorem coeff_toMathlibPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) := by
  show (fpPolyToPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n)
  rw [fpPolyToPolynomial, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range f.size) n
    (fun i => HexModArithMathlib.ZMod64.toZMod (f.coeff i))]
  by_cases hn : n ∈ Finset.range f.size
  · rw [if_pos hn]
  · rw [if_neg hn, Hex.DensePoly.coeff_eq_zero_of_size_le f
      (Nat.le_of_not_lt (Finset.mem_range.not.mp hn))]
    exact HexModArithMathlib.ZMod64.toZMod_zero.symm

@[simp]
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

namespace Rabin

/-- The Mathlib polynomial `X^(p^n) - X` used by Rabin's divisibility leg. -/
abbrev frobeniusPolynomial (p n : Nat) : Polynomial (ZMod p) :=
  X ^ (p ^ n) - X

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
  sorry

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
  sorry

end Rabin

/--
**Unsound up-to-unit overstatement — use `toMathlibPolynomial_gcd_normalize`.**

This exact equality is false in general: `Hex.DensePoly.gcd` is the last nonzero
`xgcdAux` remainder with no monic rescale (`HexPoly/Euclid.lean:913`), while
Mathlib's `gcd` is `normalize`-canonical. Counterexample over `F₅`:
`gcd(X²−1, 2X−2) = 2X−2` (leadCoeff `2`) executable, but `X−1` in Mathlib. The
two sides are only associated; see `toMathlibPolynomial_gcd_associated` and
`toMathlibPolynomial_gcd_normalize` for the sound primitives.

Retained as an unproved placeholder only because the CI-gated
`HexBerlekampZassenhausMathlib` consumers (`gcd_monicModularImage_derivative_eq_one`,
`toMathlibPolynomial_coprime_of_gcdIsUnit`, the `HotPathDiscriminant`
non-coprimality lemma) still rewrite with it. Removing it requires
re-specifying the `gcd f f' = 1` square-free precondition of
`toMathlibPolynomial_squareFree_coprime` / `irreducible_of_berlekampFactor_factors_length_le_one`
to a `gcdIsUnit`/`IsUnit` hypothesis, then migrating those consumers onto the
sound transport. See the diagnosis on issue #7763.
-/
theorem toMathlibPolynomial_gcd
    [Fact (Nat.Prime p)] (f g : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.gcd f g) =
      gcd (toMathlibPolynomial f) (toMathlibPolynomial g) := by
  sorry

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
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    IsCoprime (toMathlibPolynomial f) (Polynomial.derivative (toMathlibPolynomial f)) := by
  sorry

/--
Every factor emitted by executable Berlekamp factorization is irreducible after
transport to Mathlib's polynomial model, assuming the square-free input in the
common-divisor form used by the executable soundness chain.
-/
theorem irreducible_of_mem_berlekampFactor
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)]
    (_hsquareFree : ∀ d, d ∣ f → d ∣ Hex.DensePoly.derivative f →
      Hex.Berlekamp.isUnitPolynomial d = true) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) := by
  sorry

/--
Every factor emitted by executable Berlekamp factorization is irreducible after
transport to Mathlib's polynomial model.
-/
theorem irreducible_of_mem_berlekampFactor_of_gcd_eq_one
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)] [Hex.ZMod64.PrimeModulus p]
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) :=
  irreducible_of_mem_berlekampFactor f hmonic
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
    [Lean.Grind.Field (Hex.ZMod64 p)] [Hex.ZMod64.PrimeModulus p]
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1)
    (hsmall : (Hex.Berlekamp.berlekampFactor f hmonic).factors.length ≤ 1) :
    Irreducible (toMathlibPolynomial f) := by
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
            irreducible_of_mem_berlekampFactor_of_gcd_eq_one
              f hmonic hsquareFree g (by simp [hfactors])
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
