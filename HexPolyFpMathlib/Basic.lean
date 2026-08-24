/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp
public import HexModArithMathlib
public import HexPolyMathlib
public import Mathlib.Algebra.Ring.MinimalAxioms

public section

/-!
Correspondence between the executable prime-field polynomial representation
`Hex.FpPoly p` and Mathlib's `Polynomial (ZMod p)`.

This is the point where the executable polynomial tower meets Mathlib's own
polynomial type. Everything below it -- `Hex.DensePoly`, `Hex.ZMod64` -- is
Hex's, and everything a Mathlib user starts from is on the other side of
`fpPolyEquiv`.

The equivalence lived in `HexBerlekampMathlib` while Berlekamp factoring was
its only consumer. It is not specific to factoring: `hex-gf2-mathlib` needs it
to state `GF2Poly ≃+* Polynomial (ZMod 2)`, and any library relating an
`FpPoly`-backed construction to Mathlib needs it too. Keeping it here means
those consumers do not depend on a factoring library to reach Mathlib.
-/

namespace HexPolyFpMathlib

noncomputable section

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def fpPolyToPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (HexModArithMathlib.ZMod64.toZMod (f.coeff i))

/-- Rebuild an executable `FpPoly p` from a Mathlib polynomial over `ZMod p`. -/
def polynomialToFpPoly (f : Polynomial (ZMod p)) : Hex.FpPoly p :=
  Hex.DensePoly.ofList <|
    (List.range (f.natDegree + 1)).map fun i =>
      HexModArithMathlib.ZMod64.equiv.symm (f.coeff i)

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
    rw [polynomialToFpPoly, Hex.DensePoly.coeff_ofList,
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
    rw [coeff_fpPolyToPolynomial, polynomialToFpPoly, Hex.DensePoly.coeff_ofList,
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

/-- Applying the ring equivalence is the forward transport. The named forward
map is the normal form: statements about an executable polynomial's Mathlib
image read better without a `RingEquiv` coercion in the way. -/
@[simp, grind =]
theorem fpPolyEquiv_apply (f : Hex.FpPoly p) :
    fpPolyEquiv f = toMathlibPolynomial f := by
  rfl

/-- Applying the inverse of the ring equivalence is `polynomialToFpPoly`, the
partner of {name}`HexPolyFpMathlib.fpPolyEquiv_apply` for the backward
direction. -/
@[simp, grind =]
theorem fpPolyEquiv_symm_apply (f : Polynomial (ZMod p)) :
    fpPolyEquiv.symm f = polynomialToFpPoly f := by
  rfl

/-- Coefficients are preserved by the equivalence with Mathlib polynomials. -/
@[simp, grind =]
theorem coeff_toMathlibPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) :=
  coeff_fpPolyToPolynomial f n

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

/-! # Ring operations across the correspondence

The transport is a ring equivalence, so these follow from it; they are
stated because a caller reaching for one of them should not have to
rediscover which `RingEquiv` lemma to compose. -/

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

/-- The Mathlib primality fact yields the executable prime-modulus witness, so
executable field-dependent lemmas (gcd/Bezout, modular division) become
available in the Mathlib transport layer. -/
theorem primeModulus_of_fact (p : Nat) [Fact (Nat.Prime p)] :
    Hex.ZMod64.PrimeModulus p :=
  Hex.ZMod64.primeModulusOfPrime
    ⟨(Fact.out : Nat.Prime p).two_le,
      fun m hm => (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hm⟩


/-! # Mathlib ring structure on the executable polynomials

`SPEC/design-principles.md` puts Mathlib instances on an executable type in the
companion, transported so that the operations stay the executable ones. This is
also a prerequisite rather than a convenience: without it `Hex.FpPoly p →+* R`
is not a well-formed type, so nothing downstream can build a ring homomorphism
out of the executable polynomials.
-/

/-- The executable prime-field polynomials are a Mathlib commutative ring, with
the executable operations. Built from the laws `HexPolyFp.Ring` proves rather
than transported along {name}`HexPolyFpMathlib.fpPolyEquiv`, which would attach
the right laws to Mathlib's operations instead of these.

`sub` and `neg` are pinned to the executable ones rather than left at the
minimal-axioms defaults (`a - b = a + -b`). `HexPolyFp` already defines `Sub`
and `Neg`, so leaving the defaults would put two different subtractions on the
type and Mathlib's lemmas would not fire on the spelling callers write. -/
instance commRing : CommRing (Hex.FpPoly p) :=
  { CommRing.ofMinimalAxioms
      (R := Hex.FpPoly p)
      Hex.FpPoly.add_assoc
      Hex.FpPoly.zero_add
      Hex.FpPoly.add_left_neg
      Hex.FpPoly.mul_assoc
      Hex.FpPoly.mul_comm
      Hex.FpPoly.one_mul
      Hex.FpPoly.left_distrib with
    sub := fun a b => Hex.DensePoly.sub a b
    neg := fun a => Hex.DensePoly.neg a
    sub_eq_add_neg := Hex.FpPoly.sub_eq_add_neg }

/-- The executable linear power is Mathlib's monoid power. `HexPolyFp` defines
`linearPow` by structural recursion for kernel reduction; the `CommRing` above
supplies `npowRec`. They agree, and saying so once lets `map_pow` be used on
executable powers. -/
theorem linearPow_eq_pow (b : Hex.FpPoly p) : ∀ k, Hex.FpPoly.linearPow b k = b ^ k
  | 0 => by
      rw [Hex.FpPoly.linearPow_zero, pow_zero]
  | k + 1 => by
      rw [Hex.FpPoly.linearPow_succ, linearPow_eq_pow b k, pow_succ]

end

end HexPolyFpMathlib
