/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.QuadraticNorm
public import HexBerlekampZassenhausMathlib.SquareClass
public import HexPolyZMathlib.PolynomialEquivalence
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.LinearCombination

public section
set_option backward.proofsInPublic true

/-!
# The iterated quadratic norm as a sign-pattern product

The executable {name}`Hex.quadNorm` computes in the dense-array coordinate: it
carries a pair of `Hex.ZPoly`s standing for `g(X - t) = p + q · t` in
`ℤ[t]/(t² - d)`, and materializes only the rational part `p² - d q²` of the
product with the conjugate. This module identifies that with the honest
polynomial statement over any commutative ring carrying a square root `r` of `d`:

* `map_quadNorm` — one norm is `g(X - r) · g(X + r)`;
* `map_iteratedNorm` — the iterate is `∏_ε (X - c - ∑ᵢ εᵢ rᵢ)`, the polynomial
  the multiquadratic tower theorem is about;
* `associated_toPolynomial_of_check` — a successful
  {name}`Hex.QuadraticNormCertificate.check` pins the input to that product up to
  the unit `-1`.

The independence half of the check is in
`HexBerlekampZassenhausMathlib.SquareClass`; the field theory that turns the two
halves into irreducibility is the multiquadratic tower theorem, whose paper proof
is in `reports/hexbz-quadratic-norm-certificate.md`.
-/

/-! ## The executable independence test

`Hex.SquareClass.Independent` is the field-theoretic hypothesis; this section
proves the executable `2ⁿ - 1` subproduct test decides it. The arithmetic
content is that an integer is a rational square exactly when it is a perfect
square, so `Nat.sqrt` settles each subproduct with no factorization of the
radicands and no number field constructed. -/

namespace Hex.SquareClass

/-- {name}`Hex.isPerfectSquare` decides `IsSquare` on `ℤ`. -/
theorem isPerfectSquare_eq_true_iff (m : ℤ) : Hex.isPerfectSquare m = true ↔ IsSquare m := by
  cases m with
  | ofNat n =>
      have hnat : (Nat.sqrt n * Nat.sqrt n = n) ↔ IsSquare n :=
        ⟨fun h => ⟨Nat.sqrt n, h.symm⟩, fun ⟨r, hr⟩ =>
          (Nat.exists_mul_self n).1 ⟨r, hr.symm⟩⟩
      simp only [Hex.isPerfectSquare, beq_iff_eq, Int.ofNat_eq_natCast,
        Int.isSquare_natCast_iff]
      exact hnat
  | negSucc n =>
      simp only [Hex.isPerfectSquare, Bool.false_eq_true, false_iff]
      rintro ⟨r, hr⟩
      have hneg : (Int.negSucc n) < 0 := Int.negSucc_lt_zero n
      rw [hr] at hneg
      exact absurd (mul_self_nonneg r) (not_le.2 hneg)

/-- There are `2ⁿ - 1` subproducts, one per nonempty sublist. Stated additively
so no truncated subtraction appears. -/
theorem length_squareClassProducts (l : List ℤ) :
    (Hex.squareClassProducts l).length + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [Hex.squareClassProducts]
  | cons d ds ih =>
      have hflat : ∀ (m : List ℤ),
          (m.flatMap fun x => [x, d * x]).length = 2 * m.length := by
        intro m
        induction m with
        | nil => simp
        | cons x m ihm =>
            rw [List.flatMap_cons, List.length_append, ihm]
            show 2 + 2 * m.length = 2 * (x :: m).length
            rw [List.length_cons]
            omega
      have hcons : (Hex.squareClassProducts (d :: ds)).length
          = 1 + 2 * (Hex.squareClassProducts ds).length := by
        show (d :: (Hex.squareClassProducts ds).flatMap (fun m => [m, d * m])).length = _
        rw [List.length_cons, hflat]
        omega
      rw [hcons, List.length_cons, pow_succ]
      omega

/-- The enumerated subproducts are exactly the products of the nonempty sublists. -/
theorem mem_squareClassProducts (l : List ℤ) (m : ℤ) :
    m ∈ Hex.squareClassProducts l ↔ ∃ t : List ℤ, t.Sublist l ∧ t ≠ [] ∧ t.prod = m := by
  induction l generalizing m with
  | nil =>
      simp only [Hex.squareClassProducts, List.not_mem_nil, false_iff, not_exists]
      rintro t ⟨hsub, hne, -⟩
      exact hne (List.sublist_nil.1 hsub)
  | cons d ds ih =>
      simp only [Hex.squareClassProducts, List.mem_cons, List.mem_flatMap]
      constructor
      · rintro (heq | ⟨k, hk, hmem⟩)
        · exact ⟨[d], (List.nil_sublist ds).cons_cons d, by simp, by simp [heq]⟩
        · obtain ⟨t, hsub, hne, rfl⟩ := ih k |>.1 hk
          simp only [List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · exact ⟨t, hsub.cons d, hne, rfl⟩
          · exact ⟨d :: t, hsub.cons_cons d, by simp, by simp⟩
      · rintro ⟨t, hsub, hne, rfl⟩
        cases hsub with
        | cons _ hsub' =>
            right
            refine ⟨t.prod, (ih t.prod).2 ⟨t, hsub', hne, rfl⟩, ?_⟩
            simp
        | cons_cons _ hsub' =>
            rename_i t'
            by_cases ht' : t' = []
            · subst ht'
              left
              simp
            · right
              refine ⟨t'.prod, (ih t'.prod).2 ⟨t', hsub', ht', rfl⟩, ?_⟩
              simp

/-- The executable check decides independence: this is the whole arithmetic trust
surface of the certificate's first half. -/
theorem independentSquareClasses_iff (ds : Array ℤ) :
    Hex.independentSquareClasses ds = true ↔ Independent ds.toList := by
  rw [independent_iff_sublists]
  simp only [List.mem_sublists]
  simp only [Hex.independentSquareClasses, List.all_eq_true, Bool.not_eq_true']
  constructor
  · intro h t hsub hne hsq
    have hmem : t.prod ∈ Hex.squareClassProducts ds.toList :=
      (mem_squareClassProducts ds.toList t.prod).2 ⟨t, hsub, hne, rfl⟩
    have := h _ hmem
    rw [← isPerfectSquare_eq_true_iff] at hsq
    simp [hsq] at this
  · intro h m hmem
    obtain ⟨t, hsub, hne, rfl⟩ := (mem_squareClassProducts ds.toList m).1 hmem
    have := h t hsub hne
    rw [← isPerfectSquare_eq_true_iff] at this
    simpa using this

end Hex.SquareClass

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial
open HexPolyZMathlib (toPolynomial coeff_toPolynomial toPolynomial_add toPolynomial_sub
  toPolynomial_mul toPolynomial_C equiv)

variable {K : Type*} [CommRing K]

/-- `Zero.zero` is the numeral `0`; the dense coefficient lemmas are stated with
the former and the `Polynomial` lemmas with the latter. -/
private theorem int_zero : (Zero.zero : ℤ) = 0 := rfl

/-- The structure map `ℤ → K` is the integer cast. -/
private theorem algebraMap_int (n : ℤ) : algebraMap ℤ K n = (n : K) := by simp

/-! ## Dense-array bridges

Four coefficientwise identifications the correspondence runs on. `shift` and
`scale` are the executable array passes; `ofList` is how the Horner recursion
reads its input, and `ofCoeffs #[-c, 1]` is what the iteration starts from. -/

/-- Prepending one zero coefficient is multiplication by `X`. -/
theorem toPolynomial_shift_one (p : Hex.ZPoly) :
    toPolynomial (Hex.DensePoly.shift 1 p) = X * toPolynomial p := by
  ext k
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_shift]
  cases k with
  | zero => simp [int_zero]
  | succ k => simp

/-- Coefficientwise scaling is multiplication by a constant. -/
theorem toPolynomial_scale (c : ℤ) (p : Hex.ZPoly) :
    toPolynomial (Hex.DensePoly.scale c p) = C c * toPolynomial p := by
  ext k
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_scale c p k (mul_zero c),
    Polynomial.coeff_C_mul, coeff_toPolynomial]

/-- Reading one more coefficient off the front is one Horner step. -/
theorem toPolynomial_ofList_cons (a : ℤ) (as : List ℤ) :
    toPolynomial (Hex.DensePoly.ofList (a :: as))
      = C a + X * toPolynomial (Hex.DensePoly.ofList as) := by
  ext k
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_ofList]
  cases k with
  | zero =>
      rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.mul_coeff_zero,
        Polynomial.coeff_X_zero, zero_mul]
      simp
  | succ k =>
      rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
        coeff_toPolynomial, Hex.DensePoly.coeff_ofList]
      simp

/-- The polynomial the iteration starts from. -/
theorem toPolynomial_linear (c : ℤ) :
    toPolynomial (Hex.DensePoly.ofCoeffs #[-c, 1] : Hex.ZPoly) = X - C c := by
  ext k
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_ofCoeffs, Polynomial.coeff_sub,
    Polynomial.coeff_X, Polynomial.coeff_C]
  match k with
  | 0 => simp [Array.getD]
  | 1 => simp [Array.getD]
  | (n + 2) => simp [Array.getD, int_zero]

/-! ## One quadratic norm -/

/-- The synthetic shift is correct: with `r² = d` in `K`, the pair `(p, q)` that
{name}`Hex.quadShift` builds off the coefficient list `l` satisfies
`p + r · q = g(X - r)` over `K`, where `g` is the polynomial with those
coefficients.

Everything else follows from this by substituting `-r` for `r` and multiplying. -/
theorem quadShift_spec (d : ℤ) {r : K} (hr : r ^ 2 = (d : K)) (l : List ℤ) :
    (toPolynomial (Hex.quadShift d l).1).map (algebraMap ℤ K)
        + C r * (toPolynomial (Hex.quadShift d l).2).map (algebraMap ℤ K)
      = ((toPolynomial (Hex.DensePoly.ofList l)).map (algebraMap ℤ K)).comp (X - C r) := by
  have hrr : (C r : Polynomial K) * C r = C ((d : K)) := by
    rw [← Polynomial.C_mul, ← sq, hr]
  induction l with
  | nil => simp [Hex.quadShift_nil]
  | cons a as ih =>
      rw [Hex.quadShift_cons, Hex.quadStep, toPolynomial_ofList_cons]
      simp only [toPolynomial_add, toPolynomial_sub, toPolynomial_C,
        toPolynomial_shift_one, toPolynomial_scale, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp, algebraMap_int]
      linear_combination ((X : Polynomial K) - C r) * ih
        + ((toPolynomial (Hex.quadShift d as).2).map (algebraMap ℤ K)) * hrr

/-- The norm correspondence: over a commutative ring `K` carrying a square root
`r` of `d`, the executable quadratic norm is `g(X - r) · g(X + r)`. -/
theorem map_quadNorm (g : Hex.ZPoly) (d : ℤ) (r : K) (hr : r ^ 2 = (d : K)) :
    (toPolynomial (Hex.quadNorm d g)).map (algebraMap ℤ K)
      = ((toPolynomial g).map (algebraMap ℤ K)).comp (X - C r)
        * ((toPolynomial g).map (algebraMap ℤ K)).comp (X + C r) := by
  have hrr : (C r : Polynomial K) * C r = C ((d : K)) := by
    rw [← Polynomial.C_mul, ← sq, hr]
  have hlist : Hex.DensePoly.ofList g.toArray.toList = g := Hex.DensePoly.ofList_toList g
  have hneg : (-r) ^ 2 = (d : K) := by rw [neg_pow]; simpa using hr
  have hplus := quadShift_spec d hr g.toArray.toList
  have hminus := quadShift_spec d hneg g.toArray.toList
  rw [hlist] at hplus hminus
  rw [map_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at hminus
  rw [Hex.quadNorm_eq, ← hplus, ← hminus]
  simp only [toPolynomial_sub, toPolynomial_mul, toPolynomial_scale,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, algebraMap_int]
  linear_combination
    (((toPolynomial (Hex.quadShift d g.toArray.toList).2).map (algebraMap ℤ K))
      * ((toPolynomial (Hex.quadShift d g.toArray.toList).2).map (algebraMap ℤ K))) * hrr

/-! ## The iterate as a sign-pattern product -/

/-- The `2ⁿ` signed sums `∑ᵢ εᵢ rᵢ`, in the order the tower builds them. -/
def signedSums (rs : List K) : List K :=
  rs.foldl (fun ss r => ss.flatMap fun s => [s + r, s - r]) [0]

/-- `F(c; d₁, …, dₙ) = ∏_{ε ∈ {±1}ⁿ} (X - c - ∑ᵢ εᵢ rᵢ)`, the polynomial the
multiquadratic tower theorem is about, written over the square roots `rs`. -/
def signPatternPoly (c : K) (rs : List K) : Polynomial K :=
  ((signedSums rs).map fun s => X - C (c + s)).prod

/-- Each level doubles the number of sign patterns. -/
private theorem length_flatMap_pair (r : K) (ss : List K) :
    (ss.flatMap fun s => [s + r, s - r]).length = 2 * ss.length := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; ring

/-- There are `2ⁿ` sign patterns, so the certified polynomial has `2ⁿ` roots
counted with multiplicity. -/
@[simp] theorem length_signedSums (rs : List K) :
    (signedSums rs).length = 2 ^ rs.length := by
  have h : ∀ (rs ss : List K),
      (rs.foldl (fun ss r => ss.flatMap fun s => [s + r, s - r]) ss).length
        = 2 ^ rs.length * ss.length := by
    intro rs
    induction rs with
    | nil => intro ss; simp
    | cons r rs ih =>
        intro ss
        rw [List.foldl_cons, ih, length_flatMap_pair]
        simp [pow_succ]
        ring
  rw [signedSums]
  simpa using h rs [0]

/-- Every sign-pattern product is monic. -/
private theorem monic_prod_map (a : K) (ss : List K) :
    ((ss.map fun s => X - C (a + s)).prod).Monic := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      rw [List.map_cons, List.prod_cons]
      exact (monic_X_sub_C (a + s)).mul ih

private theorem natDegree_prod_map [Nontrivial K] (a : K) (ss : List K) :
    ((ss.map fun s => X - C (a + s)).prod).natDegree = ss.length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      rw [List.map_cons, List.prod_cons,
        (monic_X_sub_C (a + s)).natDegree_mul (monic_prod_map a ss), ih,
        natDegree_X_sub_C, List.length_cons]
      omega

/-- The sign-pattern product is monic. -/
theorem monic_signPatternPoly (c : K) (rs : List K) : (signPatternPoly c rs).Monic :=
  monic_prod_map c (signedSums rs)

/-- The sign-pattern product has degree `2ⁿ`, so the correspondence is not
vacuous: the certified polynomial really has the doubled degree at every level. -/
theorem natDegree_signPatternPoly [Nontrivial K] (c : K) (rs : List K) :
    (signPatternPoly c rs).natDegree = 2 ^ rs.length := by
  rw [signPatternPoly, natDegree_prod_map, length_signedSums]

/-- One level of the tower doubles the sign patterns. -/
private theorem prod_comp_step (a r : K) (ss : List K) :
    ((ss.map fun s => X - C (a + s)).prod).comp (X - C r)
        * ((ss.map fun s => X - C (a + s)).prod).comp (X + C r)
      = ((ss.flatMap fun s => [s + r, s - r]).map fun s => X - C (a + s)).prod := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      have hminus : ((X : Polynomial K) - C (a + s)).comp (X - C r)
          = X - C (a + (s + r)) := by
        simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
          Polynomial.add_comp, map_add]
        ring
      have hplus : ((X : Polynomial K) - C (a + s)).comp (X + C r)
          = X - C (a + (s - r)) := by
        simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
          Polynomial.add_comp, map_add, map_sub]
        ring
      simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one,
        Polynomial.mul_comp, hminus, hplus]
      rw [← ih]
      ring

/-- Folding the norms over the radicands folds the sign patterns over the roots. -/
private theorem foldl_comp_eq_prod (a : K) (rs ss : List K) :
    rs.foldl (fun P r => P.comp (X - C r) * P.comp (X + C r))
        ((ss.map fun s => X - C (a + s)).prod)
      = ((rs.foldl (fun ss r => ss.flatMap fun s => [s + r, s - r]) ss).map
          fun s => X - C (a + s)).prod := by
  induction rs generalizing ss with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl_cons]
      rw [prod_comp_step]
      exact ih _

/-- Each successive norm is one composition pair, for any starting polynomial. -/
theorem map_foldl_quadNorm (g : Hex.ZPoly) {ds : List ℤ} {rs : List K}
    (h : List.Forall₂ (fun (d : ℤ) (r : K) => r ^ 2 = (d : K)) ds rs) :
    (toPolynomial (ds.foldl (fun g d => Hex.quadNorm d g) g)).map (algebraMap ℤ K)
      = rs.foldl (fun P r => P.comp (X - C r) * P.comp (X + C r))
          ((toPolynomial g).map (algebraMap ℤ K)) := by
  induction h generalizing g with
  | nil => simp
  | @cons d r _ _ hdr _ ih =>
      simp only [List.foldl_cons]
      rw [ih (Hex.quadNorm d g), map_quadNorm g d r hdr]

/-- The iterated quadratic norm is the sign-pattern product: over any commutative
ring carrying square roots `rs` of the radicands `ds`, the executable
{name}`Hex.iteratedNorm` maps to `∏_ε (X - c - ∑ᵢ εᵢ rᵢ)`. -/
theorem map_iteratedNorm (c : ℤ) (ds : Array ℤ) {rs : List K}
    (h : List.Forall₂ (fun (d : ℤ) (r : K) => r ^ 2 = (d : K)) ds.toList rs) :
    (toPolynomial (Hex.iteratedNorm c ds)).map (algebraMap ℤ K)
      = signPatternPoly ((c : K)) rs := by
  have hbase :
      (toPolynomial (Hex.DensePoly.ofCoeffs #[-c, 1] : Hex.ZPoly)).map (algebraMap ℤ K)
        = X - C ((c : K)) := by
    rw [toPolynomial_linear]; simp
  have hstart : (([0] : List K).map fun s => X - C ((c : K) + s)).prod
      = X - C ((c : K)) := by simp
  unfold Hex.iteratedNorm signPatternPoly signedSums
  rw [← Array.foldl_toList, map_foldl_quadNorm _ h, hbase, ← hstart,
    foldl_comp_eq_prod]

/-! ## The certificate -/

/-- Coefficient equality is polynomial equality: the identification half of the
check compares dense coefficient arrays, and that comparison is exactly equality
in `Polynomial ℤ`. -/
theorem toPolynomial_inj {p q : Hex.ZPoly} (h : toPolynomial p = toPolynomial q) : p = q :=
  equiv.injective h

/-- A successful check certifies independent square classes. -/
theorem independent_of_check {cert : Hex.QuadraticNormCertificate} {f : Hex.ZPoly}
    (h : cert.check f = true) :
    Hex.SquareClass.Independent cert.radicands.toList := by
  rw [Hex.QuadraticNormCertificate.check, Bool.and_eq_true] at h
  exact (Hex.SquareClass.independentSquareClasses_iff _).1 h.1

/-- A successful check identifies the input with the iterated norm, up to sign. -/
theorem normalizePrimitiveSign_eq_of_check {cert : Hex.QuadraticNormCertificate}
    {f : Hex.ZPoly} (h : cert.check f = true) :
    Hex.ZPoly.normalizePrimitiveSign f = Hex.iteratedNorm cert.translation cert.radicands := by
  rw [Hex.QuadraticNormCertificate.check, Bool.and_eq_true] at h
  exact (beq_iff_eq.1 h.2).symm

/-- The identification half, in `Polynomial ℤ`: a successful check pins the input
to the iterated norm up to the unit `-1`. -/
theorem toPolynomial_eq_or_neg_of_check {cert : Hex.QuadraticNormCertificate}
    {f : Hex.ZPoly} (h : cert.check f = true) :
    toPolynomial f = toPolynomial (Hex.iteratedNorm cert.translation cert.radicands) ∨
      toPolynomial f
        = -toPolynomial (Hex.iteratedNorm cert.translation cert.radicands) := by
  have hnorm := normalizePrimitiveSign_eq_of_check h
  rw [Hex.ZPoly.normalizePrimitiveSign] at hnorm
  split at hnorm
  · right
    rw [← hnorm, toPolynomial_scale]
    simp
  · left
    rw [hnorm]

/-- A successful check makes the input an associate of the iterated norm, so the
two are irreducible together. -/
theorem associated_toPolynomial_of_check {cert : Hex.QuadraticNormCertificate}
    {f : Hex.ZPoly} (h : cert.check f = true) :
    Associated (toPolynomial f)
      (toPolynomial (Hex.iteratedNorm cert.translation cert.radicands)) := by
  rcases toPolynomial_eq_or_neg_of_check h with heq | heq
  · exact heq ▸ Associated.refl _
  · exact heq ▸ ⟨-1, by simp⟩

end

end HexBerlekampZassenhausMathlib
