import HexBerlekampZassenhausMathlib.IntReductionMod
import HexBerlekampZassenhausMathlib.Resultant

/-!
`isGoodPrime`-failure divisibility for the BHKS hot-path discriminant.

When the executable good-prime check `Hex.isGoodPrime f p` fails for a
prime `p ≥ 3`, the modulus divides the integer product
`lc(f) · resultant(toPolynomial f, (toPolynomial f).derivative)` taken at
the `(natDegree, natDegree − 1)` size arguments. This is the per-prime
divisibility ingredient that SPEC D2's `choosePrimeData?_none_implies_huge`
(issue #6509) combines with the hot-path enumeration coverage facts in
`HexBerlekampZassenhaus.Basic` to discharge the "no good prime" branch.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

variable {p : Nat}

/-- A bridged executable polynomial transports to a unit in `(ZMod p)[X]`
exactly when its executable size is one. This is the size half of the
contrapositive of `toMathlibPolynomial_coprime_of_gcdIsUnit`. -/
private theorem size_eq_one_of_toMathlibPolynomial_isUnit
    [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    {g : Hex.FpPoly p}
    (h : IsUnit (HexBerlekampMathlib.toMathlibPolynomial g)) :
    g.size = 1 := by
  rcases Nat.lt_or_ge g.size 1 with hlt | hge
  · -- `g.size = 0`: the transport is the zero polynomial, not a unit.
    exfalso
    have hsize_zero : g.size = 0 := by omega
    have hzero : HexBerlekampMathlib.toMathlibPolynomial g = 0 := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
        Hex.DensePoly.coeff_eq_zero_of_size_le _ (show g.size ≤ n by omega)]
      exact HexModArithMathlib.ZMod64.toZMod_zero
    exact not_isUnit_zero (hzero ▸ h)
  · -- `g.size ≥ 1`: rule out `g.size ≥ 2` via the positive-natDegree witness.
    by_contra hne
    have hpos : 0 < g.size := by omega
    have hge2 : 2 ≤ g.size := by omega
    have hcoeff_ne : g.coeff (g.size - 1) ≠ 0 :=
      Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hpos
    have hcoeff_zmod_ne :
        HexModArithMathlib.ZMod64.toZMod (g.coeff (g.size - 1)) ≠ 0 := by
      intro hzero
      apply hcoeff_ne
      have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
      apply hinj
      simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
    have hcoeff_poly_ne :
        (HexBerlekampMathlib.toMathlibPolynomial g).coeff (g.size - 1) ≠ 0 := by
      rw [HexBerlekampMathlib.coeff_toMathlibPolynomial]
      exact hcoeff_zmod_ne
    have hpos_natDeg :
        0 < (HexBerlekampMathlib.toMathlibPolynomial g).natDegree := by
      have hle := Polynomial.le_natDegree_of_ne_zero hcoeff_poly_ne
      omega
    exact Polynomial.not_isUnit_of_natDegree_pos _ hpos_natDeg h

/-- Contrapositive of `toMathlibPolynomial_coprime_of_gcdIsUnit`: when the
executable `gcdIsUnit` check on `gcd(f, f')` fails, the Mathlib-transported
`f` and its formal derivative are not coprime. -/
private theorem toMathlibPolynomial_not_coprime_of_gcdIsUnit_false
    [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p)
    (hsqf :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = false) :
    ¬ IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial f)
        (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) := by
  intro hcop
  let g : Hex.FpPoly p := Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)
  have hmath_gcd_unit :
      IsUnit
        (gcd
          (HexBerlekampMathlib.toMathlibPolynomial f)
          (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  have hg_unit : IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) := by
    rw [← HexBerlekampMathlib.toMathlibPolynomial_derivative] at hmath_gcd_unit
    exact
      (HexBerlekampMathlib.toMathlibPolynomial_gcd_associated
        f (Hex.DensePoly.derivative f)).symm.isUnit hmath_gcd_unit
  have hg_size : g.size = 1 :=
    size_eq_one_of_toMathlibPolynomial_isUnit hg_unit
  have hsqf' : Hex.gcdIsUnit g = true := by
    unfold Hex.gcdIsUnit
    simp [hg_size]
  exact Bool.false_ne_true (hsqf.symm.trans hsqf')

/-- Failure of `Hex.isGoodPrime f p` at a prime `p ≥ 3` forces the modulus
to divide the integer product
`lc(f) · resultant(fInt, fInt.derivative, n, n − 1)`, where
`fInt = HexPolyZMathlib.toPolynomial f` and `n = fInt.natDegree`. This is
the per-prime ingredient for SPEC D2's
`choosePrimeData?_none_implies_huge` (issue #6509). -/
theorem isGoodPrime_false_implies_dvd_resultant_deriv
    (f : Hex.ZPoly) (p : Nat) [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (hge : 3 ≤ p)
    (hfalse : Hex.isGoodPrime f p = false) :
    (p : Int) ∣ ((Hex.DensePoly.leadingCoeff f) *
      Polynomial.resultant
        (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial f).derivative
        (HexPolyZMathlib.toPolynomial f).natDegree
        ((HexPolyZMathlib.toPolynomial f).natDegree - 1)) := by
  set fInt : Polynomial Int := HexPolyZMathlib.toPolynomial f with hfInt_def
  set n : Nat := fInt.natDegree with hn_def
  set phi : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hphi_def
  -- Reduce to a `ZMod p` zero statement and distribute the cast across the product.
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul]
  -- A useful identification: the `Int → ZMod p` cast of `lc(f)` equals the
  -- transported executable `leadingCoeffModP`.
  have hlc_cast :
      ((Hex.DensePoly.leadingCoeff f : Int) : ZMod p) =
        HexModArithMathlib.ZMod64.toZMod (Hex.ZPoly.leadingCoeffModP f p) := by
    have hcast :
        (Int.castRingHom (ZMod p)) fInt.leadingCoeff =
          HexModArithMathlib.ZMod64.toZMod (Hex.ZPoly.leadingCoeffModP f p) :=
      IntReductionMod.intCast_zmod_leadingCoeff_eq_toZMod_leadingCoeffModP f
    rw [HexPolyMathlib.leadingCoeff_toPolynomial] at hcast
    simpa using hcast
  -- Case-split on whether the leading coefficient survives reduction modulo `p`.
  by_cases hlcz : Hex.ZPoly.leadingCoeffModP f p = 0
  · -- Case A: `lc(f) ≡ 0 (mod p)`. The product is `0 * _`.
    have hlc_zero : ((Hex.DensePoly.leadingCoeff f : Int) : ZMod p) = 0 := by
      rw [hlc_cast, hlcz, HexModArithMathlib.ZMod64.toZMod_zero]
    rw [hlc_zero, zero_mul]
  · -- Case B: `lc(f) ≢ 0 (mod p)`. Then `gcdIsUnit (gcd fModP fModP') = false`.
    have hgcd_false :
        Hex.gcdIsUnit
            (Hex.DensePoly.gcd (Hex.ZPoly.modP p f)
              (Hex.DensePoly.derivative (Hex.ZPoly.modP p f))) = false := by
      have hraw := hfalse
      unfold Hex.isGoodPrime at hraw
      have h1 : decide (3 ≤ p) = true := decide_eq_true hge
      have h2 : (Hex.ZPoly.leadingCoeffModP f p != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        exact hlcz
      simp only [h1, h2, Bool.true_and, Bool.and_true] at hraw
      exact hraw
    -- Mathlib-side names.
    set fModP : Hex.FpPoly p := Hex.ZPoly.modP p f with hfModP_def
    set fBar : Polynomial (ZMod p) :=
      HexBerlekampMathlib.toMathlibPolynomial fModP with hfBar_def
    -- The composite `fInt.map phi` agrees with the Mathlib transport of `fModP`.
    have hfmap : fInt.map phi = fBar := by
      rw [hfBar_def, hfModP_def,
        IntReductionMod.toMathlibPolynomial_modP_eq_map_intCast_zmod (p := p) f]
    -- The reduction preserves natural degree because the leading coefficient survives.
    have hnatdeg : fBar.natDegree = n := by
      rw [← hfmap]
      exact IntReductionMod.natDegree_map_intCast_zmod_eq_of_leadingCoeffModP_ne_zero
        f hlcz
    -- The transported `fBar` is not coprime to its formal derivative.
    have hnotcop :
        ¬ IsCoprime fBar (Polynomial.derivative fBar) :=
      toMathlibPolynomial_not_coprime_of_gcdIsUnit_false fModP hgcd_false
    -- The leading coefficient is nonzero in `ZMod p`, so `fBar ≠ 0`.
    have hlc_ne : ((Hex.DensePoly.leadingCoeff f : Int) : ZMod p) ≠ 0 := by
      rw [hlc_cast]
      intro hz
      apply hlcz
      have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
      apply hinj
      simpa using hz.trans (HexModArithMathlib.ZMod64.toZMod_zero (p := p)).symm
    have hfBar_ne : fBar ≠ 0 := by
      intro hf_zero
      apply hlc_ne
      -- The transported polynomial vanishes ⟹ its coefficient at `n` vanishes
      -- ⟹ `phi (fInt.leadingCoeff) = 0` ⟹ `(lc(f) : ZMod p) = 0`.
      have hbar_coeff_zero : fBar.coeff n = 0 := by rw [hf_zero]; simp
      have hcoeff_eq :
          fBar.coeff n = ((Hex.DensePoly.leadingCoeff f : Int) : ZMod p) := by
        rw [← hfmap, Polynomial.coeff_map, show n = fInt.natDegree from hn_def,
            Polynomial.coeff_natDegree, HexPolyMathlib.leadingCoeff_toPolynomial]
        rfl
      exact hcoeff_eq.symm.trans hbar_coeff_zero
    -- The default-arg resultant `resultant fBar fBar.derivative` vanishes.
    have hres_default_zero :
        Polynomial.resultant fBar fBar.derivative = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      exact ⟨Or.inl hfBar_ne, hnotcop⟩
    -- Bridge to the explicit degree-pair resultant.
    have hdernat_le : fBar.derivative.natDegree ≤ n - 1 := by
      have := Polynomial.natDegree_derivative_le fBar
      omega
    -- Apply resultant_add_right_deg with k = (n - 1) - fBar.derivative.natDegree.
    have hres_pair_zero :
        Polynomial.resultant fBar fBar.derivative n (n - 1) = 0 := by
      have hk_eq :
          fBar.derivative.natDegree + ((n - 1) - fBar.derivative.natDegree) =
            n - 1 := by omega
      have hres_eq :
          Polynomial.resultant fBar fBar.derivative n (n - 1) =
            fBar.coeff n ^ ((n - 1) - fBar.derivative.natDegree) *
              Polynomial.resultant fBar fBar.derivative n
                fBar.derivative.natDegree := by
        conv_lhs => rw [← hk_eq]
        exact Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl
      have hdefault :
          Polynomial.resultant fBar fBar.derivative n
              fBar.derivative.natDegree =
            Polynomial.resultant fBar fBar.derivative := by
        rw [show n = fBar.natDegree from hnatdeg.symm]
      rw [hres_eq, hdefault, hres_default_zero, mul_zero]
    -- Push the cast through the resultant.
    have hres_cast :
        ((Polynomial.resultant fInt fInt.derivative n (n - 1) : Int) : ZMod p) =
          Polynomial.resultant fBar fBar.derivative n (n - 1) := by
      have hrm :
          phi (Polynomial.resultant fInt fInt.derivative n (n - 1)) =
            Polynomial.resultant (fInt.map phi) (fInt.derivative.map phi) n
              (n - 1) :=
        (Polynomial.resultant_map_map _ _ _ _ phi).symm
      have hdm : fInt.derivative.map phi = (fInt.map phi).derivative :=
        (Polynomial.derivative_map _ _).symm
      rw [hdm, hfmap] at hrm
      simpa [hphi_def] using hrm
    rw [hres_cast, hres_pair_zero, mul_zero]

/-- SPEC D2 composition: when the executable prime search `Hex.choosePrimeData?`
fails to select any small prime, every prime `p` in the SPEC hot-path interval
`[3, 500]` divides the integer product
`lc(f) · resultant(toPolynomial f, (toPolynomial f).derivative)` at the
`(natDegree, natDegree − 1)` size arguments. Combined with B1's
`bhksBound`-dominates-Mignotte chain, the conclusion forces the input
polynomial's discriminant-like quantity to be "huge", which is the form
consumed by the leaf-correctness wiring.

The proof composes the executable provenance helper
`Hex.mem_hotPathCandidates_isGoodPrime_false_of_choosePrimeData?_none` with
the per-prime divisibility bridge `isGoodPrime_false_implies_dvd_resultant_deriv`
and the hot-path coverage lemma `Hex.exists_mem_hotPathCandidates_of_prime`.

The `Primitive` / `SquareFreeRat` hypotheses are downstream consumer
preconditions; the divisibility conclusion itself holds for arbitrary `f`. -/
theorem choosePrimeData?_none_implies_huge
    (f : Hex.ZPoly) (_hp : Hex.ZPoly.Primitive f) (_hs : Hex.ZPoly.SquareFreeRat f)
    (hf : Hex.choosePrimeData? f = none)
    (p : Nat) (hp_range : 3 ≤ p ∧ p ≤ 500) (hp_prime : Nat.Prime p) :
    (p : Int) ∣ ((Hex.DensePoly.leadingCoeff f) *
      Polynomial.resultant
        (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial f).derivative
        (HexPolyZMathlib.toPolynomial f).natDegree
        ((HexPolyZMathlib.toPolynomial f).natDegree - 1)) := by
  -- Bridge Mathlib `Nat.Prime` to the Mathlib-free `Hex.Nat.Prime` used by the
  -- hot-path enumeration coverage lemma.
  have hp_hex : Hex.Nat.Prime p := by
    refine ⟨hp_prime.two_le, ?_⟩
    intro m hmdvd
    rcases hp_prime.eq_one_or_self_of_dvd m hmdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Pull a hot-path candidate `c` with `c.p = p`.
  obtain ⟨c, hc, hcp⟩ :=
    Hex.exists_mem_hotPathCandidates_of_prime hp_hex hp_range.1 hp_range.2
  -- `choosePrimeData? f = none` forces `isGoodPrime f c.p = false` for every
  -- hot-path candidate.
  have hgood_false : @Hex.isGoodPrime f c.p c.bounds = false :=
    Hex.mem_hotPathCandidates_isGoodPrime_false_of_choosePrimeData?_none hf hc
  -- Transport the conclusion along `c.p = p`.
  subst hcp
  letI : Hex.ZMod64.Bounds c.p := c.bounds
  letI : Fact (Nat.Prime c.p) := ⟨hp_prime⟩
  exact isGoodPrime_false_implies_dvd_resultant_deriv f c.p hp_range.1 hgood_false

end

end HexBerlekampZassenhausMathlib
