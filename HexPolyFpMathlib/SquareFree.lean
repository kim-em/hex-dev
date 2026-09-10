/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFpMathlib.Basic
public import Mathlib.FieldTheory.Separable

public section

/-!
The headline correctness theorem for hex-poly-fp: the executable Yun
square-free decomposition, transported through `fpPolyEquiv`, reconstructs the
input in `Polynomial (ZMod p)` from factors that are `Squarefree` and pairwise
`IsCoprime`, each carried with a positive multiplicity.

The executable layer (`HexPolyFp.SquareFree`) proves the same post-condition
Mathlib-free, phrasing square-freeness and coprimality through the monic
normalization of the executable gcd reducing to `1`. This module converts each
of those gcd-unit certificates into the corresponding Mathlib predicate — a
unit gcd yields a Bezout identity, hence `IsCoprime`; coprimality with the
formal derivative is `Polynomial.Separable`, hence `Squarefree` — and restates
the weighted factor product as a Mathlib list product.
-/

namespace HexPolyFpMathlib

open Polynomial

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Mathlib's `Nat.Prime` fact yields the executable prime predicate, so the
executable square-free decomposition (which consumes `Hex.Nat.Prime p`) can be
invoked in a context carrying only the Mathlib-side hypothesis. -/
theorem hexPrime_of_fact (p : Nat) [Fact (Nat.Prime p)] : Hex.Nat.Prime p :=
  ⟨(Fact.out : Nat.Prime p).two_le,
    fun m hm => (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hm⟩

/-- The square-and-multiply loop computes `acc * base ^ k`, with the exponent
laws now supplied by the Mathlib `CommRing` on `Hex.FpPoly p`. -/
private theorem pow_go_eq_mul_pow (acc base : Hex.FpPoly p) (k : Nat) :
    Hex.FpPoly.pow.go acc base k = acc * base ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [Hex.FpPoly.pow.go.eq_def]
      by_cases hk : k = 0
      · simp [hk]
      · rw [dite_eq_right hk]
        have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
        show Hex.FpPoly.pow.go (if k % 2 = 1 then acc * base else acc)
          (base * base) (k / 2) = acc * base ^ k
        rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
        · have hnot : ¬ k % 2 = 1 := by omega
          have hk2 : 2 * (k / 2) = k := by omega
          rw [ite_eq_right hnot, ih _ hlt, ← sq, ← pow_mul, hk2]
        · have hk2 : 2 * (k / 2) + 1 = k := by omega
          rw [ite_eq_left hmod, ih _ hlt, ← sq, ← pow_mul, mul_assoc, ← pow_succ', hk2]

/-- The executable square-and-multiply power is Mathlib's monoid power, the
sibling of `linearPow_eq_pow` for the exponentiation the compiled square-free
path actually runs. -/
theorem pow_eq_pow (f : Hex.FpPoly p) (n : Nat) : Hex.FpPoly.pow f n = f ^ n := by
  rw [Hex.FpPoly.pow, pow_go_eq_mul_pow, one_mul]

/-- The executable weighted factor product is the Mathlib list product of the
factors raised to their multiplicities, still on the executable side of the
correspondence. -/
theorem weightedProduct_eq_prod (factors : List (Hex.FpPoly.SquareFreeFactor p)) :
    Hex.FpPoly.weightedProduct factors =
      (factors.map fun sf => sf.factor ^ sf.multiplicity).prod := by
  rw [Hex.FpPoly.weightedProduct]
  simp only [pow_eq_pow]
  rw [List.prod_eq_foldl, List.foldl_map]

/-- The weighted factor product transports to the Mathlib list product of the
transported factors raised to their multiplicities. -/
theorem toMathlibPolynomial_weightedProduct
    (factors : List (Hex.FpPoly.SquareFreeFactor p)) :
    toMathlibPolynomial (Hex.FpPoly.weightedProduct factors) =
      (factors.map fun sf => toMathlibPolynomial sf.factor ^ sf.multiplicity).prod := by
  rw [weightedProduct_eq_prod, ← fpPolyEquiv_apply, map_list_prod fpPolyEquiv,
    List.map_map]
  simp only [Function.comp_def, map_pow, fpPolyEquiv_apply]

/-- A polynomial whose monic normalization is `1` is a nonzero constant, so its
transport is a Mathlib unit. The zero case is impossible (`normalizeMonic`
sends `0` to `(0, 0)`), and otherwise `normalizeMonic` exhibits an explicit
constant multiplier reaching `1`. -/
private theorem isUnit_toMathlibPolynomial_of_normalizeMonic_eq_one
    [Fact (Nat.Prime p)] {g : Hex.FpPoly p}
    (h : (Hex.FpPoly.normalizeMonic g).2 = 1) :
    IsUnit (toMathlibPolynomial g) := by
  cases hz : g.isZero with
  | true =>
      exfalso
      rw [show (Hex.FpPoly.normalizeMonic g).2 = 0 by
        simp [Hex.FpPoly.normalizeMonic, hz]] at h
      have h0 := congrArg toMathlibPolynomial h
      rw [← fpPolyEquiv_apply, ← fpPolyEquiv_apply, map_zero, map_one] at h0
      exact zero_ne_one h0
  | false =>
      have hC : Hex.DensePoly.C (Hex.DensePoly.leadingCoeff g)⁻¹ * g = 1 := by
        rw [Hex.FpPoly.C_mul_eq_scale, ← h]
        simp [Hex.FpPoly.normalizeMonic, hz]
      have hM := congrArg toMathlibPolynomial hC
      rw [toMathlibPolynomial_mul, toMathlibPolynomial_C, toMathlibPolynomial_one] at hM
      exact isUnit_of_mul_isUnit_right (hM ▸ isUnit_one)

/-- The executable square-free layer's coprimality certificate — the monic
normalization of the executable gcd reducing to `1` — transports to Mathlib
coprimality, via the executable Bezout identity. This is the hex-poly-fp
counterpart of hex-berlekamp-mathlib's
`isCoprime_toMathlibPolynomial_of_isUnitPolynomial_gcd`, keyed on the gcd-unit
phrasing the Yun theorems emit rather than Berlekamp's `isUnitPolynomial`. -/
theorem isCoprime_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one
    [Fact (Nat.Prime p)] {a b : Hex.FpPoly p}
    (h : (Hex.FpPoly.normalizeMonic (Hex.DensePoly.gcd a b)).2 = 1) :
    IsCoprime (toMathlibPolynomial a) (toMathlibPolynomial b) := by
  have : Hex.ZMod64.PrimeModulus p := primeModulus_of_fact p
  obtain ⟨u, hu⟩ := isUnit_toMathlibPolynomial_of_normalizeMonic_eq_one h
  have hbez : (Hex.DensePoly.xgcd a b).left * a + (Hex.DensePoly.xgcd a b).right * b
      = Hex.DensePoly.gcd a b :=
    (Hex.DensePoly.xgcd_bezout a b).trans (Hex.DensePoly.xgcd_gcd_eq_gcd a b)
  have hbezM :
      toMathlibPolynomial (Hex.DensePoly.xgcd a b).left * toMathlibPolynomial a +
        toMathlibPolynomial (Hex.DensePoly.xgcd a b).right * toMathlibPolynomial b =
        toMathlibPolynomial (Hex.DensePoly.gcd a b) := by
    rw [← toMathlibPolynomial_mul, ← toMathlibPolynomial_mul, ← toMathlibPolynomial_add,
      hbez]
  refine ⟨↑u⁻¹ * toMathlibPolynomial (Hex.DensePoly.xgcd a b).left,
    ↑u⁻¹ * toMathlibPolynomial (Hex.DensePoly.xgcd a b).right, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hbezM, ← hu]
  exact u.inv_mul

/-- The executable square-freeness certificate — the monic normalization of
`gcd g (derivative g)` reducing to `1` — transports to Mathlib
`Squarefree`: coprimality with the formal derivative is `Polynomial.Separable`,
and separable polynomials are square-free. -/
theorem squarefree_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one
    [Fact (Nat.Prime p)] {g : Hex.FpPoly p}
    (h : (Hex.FpPoly.normalizeMonic
      (Hex.DensePoly.gcd g (Hex.DensePoly.derivative g))).2 = 1) :
    Squarefree (toMathlibPolynomial g) := by
  have hco := isCoprime_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one h
  rw [toMathlibPolynomial_derivative] at hco
  exact (show (toMathlibPolynomial g).Separable from hco).squarefree

/-- Headline correctness theorem for hex-poly-fp: the executable Yun
square-free decomposition is a genuine square-free decomposition in
`Polynomial (ZMod p)`.

For a prime modulus and any input `f`, writing `d` for the decomposition:

- **reconstruction** — the constant `C d.unit` times the product of the
  transported factors, each raised to its recorded multiplicity, is the
  transport of `f`;
- **square-freeness** — every transported factor is `Squarefree`;
- **pairwise coprimality** — the transported factors are pairwise `IsCoprime`;
- **positive multiplicities** — every recorded multiplicity is positive.

No nonzeroness or degree hypothesis on `f` is required: the executable
theorems cover the degenerate cases (for `f = 0` the emitted unit is `0`),
and the statement transports them unchanged. Built from the Mathlib-free
post-conditions `squareFreeDecomposition_weightedProduct`,
`squareFreeDecomposition_factors_squareFree`,
`squareFreeDecomposition_pairwise_coprime`, and
`squareFreeDecomposition_multiplicity_pos`, with the gcd-unit certificates
converted through the executable Bezout identity. -/
theorem squareFreeDecomposition_correct
    [Fact (Nat.Prime p)] (hp : Hex.Nat.Prime p) (f : Hex.FpPoly p) :
    let d := Hex.FpPoly.squareFreeDecomposition hp f
    Polynomial.C (HexModArithMathlib.ZMod64.toZMod d.unit) *
        (d.factors.map fun sf => toMathlibPolynomial sf.factor ^ sf.multiplicity).prod =
      toMathlibPolynomial f ∧
    (∀ sf ∈ d.factors, Squarefree (toMathlibPolynomial sf.factor)) ∧
    d.factors.Pairwise (fun a b =>
      IsCoprime (toMathlibPolynomial a.factor) (toMathlibPolynomial b.factor)) ∧
    (∀ sf ∈ d.factors, 0 < sf.multiplicity) := by
  intro d
  refine ⟨?_, ?_, ?_, Hex.FpPoly.squareFreeDecomposition_multiplicity_pos hp f⟩
  · have hrec : Hex.DensePoly.C
        (Hex.FpPoly.squareFreeDecomposition hp f).unit *
        Hex.FpPoly.weightedProduct (Hex.FpPoly.squareFreeDecomposition hp f).factors = f :=
      Hex.FpPoly.squareFreeDecomposition_weightedProduct hp f
    have hM := congrArg toMathlibPolynomial hrec
    rw [toMathlibPolynomial_mul, toMathlibPolynomial_C,
      toMathlibPolynomial_weightedProduct] at hM
    exact hM
  · intro sf hsf
    exact squarefree_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one
      (Hex.FpPoly.squareFreeDecomposition_factors_squareFree hp f sf hsf)
  · have hpair : (Hex.FpPoly.squareFreeDecomposition hp f).factors.Pairwise
        (fun a b =>
          (Hex.FpPoly.normalizeMonic (Hex.DensePoly.gcd a.factor b.factor)).2 = 1) :=
      Hex.FpPoly.squareFreeDecomposition_pairwise_coprime hp f
    exact hpair.imp fun hab =>
      isCoprime_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one hab

/-! # Axiom hygiene

The headline theorem's proof cone must stay on the three standard axioms:
no `sorry`, no `native_decide`. -/

/--
info: 'HexPolyFpMathlib.squareFreeDecomposition_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms squareFreeDecomposition_correct

end HexPolyFpMathlib
