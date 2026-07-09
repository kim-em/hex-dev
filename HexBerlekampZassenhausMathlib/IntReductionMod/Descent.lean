/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.ToMonicUniqueness
public import HexBerlekampMathlib.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Radical
public import Mathlib.RingTheory.Polynomial.GaussLemma

public section
set_option backward.proofsInPublic true

/-!
Reduction-mod-`p` irreducibility descent for primitive integer
polynomials: the mod-`p` irreducibility criterion, gcd/unit/coprime
lemmas for choosePrimeData, and normalizeForFactor primitivity with
square-free transport.
-/
namespace HexBerlekampZassenhausMathlib

namespace IntReductionMod

open Polynomial

variable {p : ℕ}

private theorem precision_of_le
    {B L p : Nat} (hp : 2 ≤ p) (hBL : B ≤ L) :
    2 * B < p ^ Hex.precisionForCoeffBound L p := by
  have hspec : 2 * L < p ^ Hex.precisionForCoeffBound L p :=
    Hex.precisionForCoeffBound_spec hp L
  omega

theorem exhaustiveLiftBound_precision
    (core : Hex.ZPoly) (B p : Nat) (hp : 2 ≤ p) :
    2 * B <
      p ^ Hex.precisionForCoeffBound (Hex.ZPoly.exhaustiveLiftBound core B) p :=
  precision_of_le hp (Hex.ZPoly.le_exhaustiveLiftBound core B)

theorem exhaustiveLiftBound_monic_precision
    (core : Hex.ZPoly) (B p : Nat) (hp : 2 ≤ p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
      p ^ Hex.precisionForCoeffBound (Hex.ZPoly.exhaustiveLiftBound core B) p :=
  precision_of_le hp (Hex.ZPoly.monicBound_le_exhaustiveLiftBound core B)

/--
The executable coefficientwise reduction `Hex.ZPoly.modP` agrees with
Mathlib's coefficient map from `ℤ[X]` to `(ZMod p)[X]` after transporting the
resulting `FpPoly` through the Berlekamp transport.
-/
theorem toMathlibPolynomial_modP_eq_map_intCast_zmod
    [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p f) =
      (HexPolyZMathlib.toPolynomial f).map (Int.castRingHom (ZMod p)) := by
  exact
    HexPolyZMathlib.eq_map_intCast_of_coeff_eq_toZMod_modP p f
      (fun n => HexBerlekampMathlib.coeff_toMathlibPolynomial _ n)

/--
The Mathlib `ZMod p`-cast of the leading coefficient of a `Hex.ZPoly` agrees
with the executable `ZMod64`-valued `leadingCoeffModP` after transport along
`ZMod64.toZMod`. This is the integer-side companion to the modular `modP`
lemma: it lets a downstream caller chain the executable good-prime
hypothesis through to the Mathlib `Polynomial.map` natural-degree lemma.
-/
theorem intCast_zmod_leadingCoeff_eq_toZMod_leadingCoeffModP
    [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    (Int.castRingHom (ZMod p)) (HexPolyZMathlib.toPolynomial f).leadingCoeff =
      HexModArithMathlib.ZMod64.toZMod (Hex.ZPoly.leadingCoeffModP f p) := by
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  show ((Hex.DensePoly.leadingCoeff f : ℤ) : ZMod p) = _
  rw [← HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast p
        (Hex.DensePoly.leadingCoeff f)]
  rfl

/--
The Mathlib `ZMod p`-cast of the leading coefficient of a `Hex.ZPoly` is
nonzero exactly when the executable `leadingCoeffModP` is. This packages the
direction needed by the integer-factor degree-preservation step in
`checkIrreducibleCert_sound`.
-/
theorem intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
    [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    (Int.castRingHom (ZMod p)) (HexPolyZMathlib.toPolynomial f).leadingCoeff ≠ 0 ↔
      Hex.ZPoly.leadingCoeffModP f p ≠ 0 := by
  rw [intCast_zmod_leadingCoeff_eq_toZMod_leadingCoeffModP]
  constructor
  · intro h heq
    apply h
    rw [heq, HexModArithMathlib.ZMod64.toZMod_zero]
  · intro h heq
    apply h
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
    apply hinj
    simpa using heq.trans HexModArithMathlib.ZMod64.toZMod_zero.symm

/--
Reduction modulo `p` preserves natural degree when the executable
`leadingCoeffModP` data records a nonzero leading coefficient. This is the
issue-spec `_of_unit_lc_mod_p` shape: the executable good-prime check supplies
the `leadingCoeffModP ≠ 0` hypothesis, and `natDegree` is preserved along the
Mathlib `Polynomial.map` reduction.
-/
theorem natDegree_map_intCast_zmod_eq_of_leadingCoeffModP_ne_zero
    [Hex.ZMod64.Bounds p] (f : Hex.ZPoly)
    (hadm : Hex.ZPoly.leadingCoeffModP f p ≠ 0) :
    ((HexPolyZMathlib.toPolynomial f).map (Int.castRingHom (ZMod p))).natDegree =
      (HexPolyZMathlib.toPolynomial f).natDegree :=
  HexPolyZMathlib.natDegree_map_intCast_zmod_eq_of_leadingCoeff_ne_zero p f
    ((intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
      (p := p) (f := f)).mpr hadm)

/--
Reduction-mod-`p` Gauss lemma over `ℤ`: a primitive integer polynomial whose
modular reduction is irreducible and whose leading coefficient is not killed
by the reduction is itself irreducible.
-/
theorem irreducible_of_isPrimitive_of_irreducible_map_intCast_zmod
    [Fact (Nat.Prime p)]
    {f : Polynomial ℤ}
    (hprim : f.IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    Irreducible f := by
  haveI : IsDomain (ZMod p) := inferInstance
  set φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hφ_def
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hirr.not_isUnit (IsUnit.map (mapRingHom φ) hunit)
  · intro a b hfab
    have hf_lc_ne : f.leadingCoeff ≠ 0 := by
      intro h
      apply hlc_map_ne
      rw [h]
      exact map_zero _
    have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf_lc_ne
    have ha_ne : a ≠ 0 := by
      intro h
      rw [h, zero_mul] at hfab
      exact hf_ne hfab
    have hb_ne : b ≠ 0 := by
      intro h
      rw [h, mul_zero] at hfab
      exact hf_ne hfab
    have hfab_map :
        f.map φ = a.map φ * b.map φ := by
      rw [hfab, Polynomial.map_mul]
    have hlc_mul :
        f.leadingCoeff = a.leadingCoeff * b.leadingCoeff := by
      have ha_lc_ne : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha_ne
      have hb_lc_ne : b.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hb_ne
      have hmul_ne : a.leadingCoeff * b.leadingCoeff ≠ 0 :=
        mul_ne_zero ha_lc_ne hb_lc_ne
      rw [hfab]
      exact leadingCoeff_mul' hmul_ne
    have hlc_map_mul :
        φ f.leadingCoeff = φ a.leadingCoeff * φ b.leadingCoeff := by
      rw [hlc_mul, map_mul]
    have ha_lc_map_ne : φ a.leadingCoeff ≠ 0 := by
      intro h
      apply hlc_map_ne
      rw [hlc_map_mul, h, zero_mul]
    have hb_lc_map_ne : φ b.leadingCoeff ≠ 0 := by
      intro h
      apply hlc_map_ne
      rw [hlc_map_mul, h, mul_zero]
    have ha_natDegree_map :
        (a.map φ).natDegree = a.natDegree :=
      natDegree_map_of_leadingCoeff_ne_zero φ ha_lc_map_ne
    have hb_natDegree_map :
        (b.map φ).natDegree = b.natDegree :=
      natDegree_map_of_leadingCoeff_ne_zero φ hb_lc_map_ne
    rcases hirr.isUnit_or_isUnit hfab_map with ha_map_unit | hb_map_unit
    · left
      have ha_dvd : a ∣ f := ⟨b, hfab⟩
      have ha_prim : a.IsPrimitive := isPrimitive_of_dvd hprim ha_dvd
      have ha_map_natDeg_zero : (a.map φ).natDegree = 0 := by
        rcases Polynomial.isUnit_iff.mp ha_map_unit with ⟨r, _, hr_eq⟩
        rw [← hr_eq, natDegree_C]
      have ha_natDeg_zero : a.natDegree = 0 := by
        rw [← ha_natDegree_map]
        exact ha_map_natDeg_zero
      have ha_const : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha_natDeg_zero
      have ha_coeff_unit : IsUnit (a.coeff 0) := by
        apply ha_prim
        rw [← ha_const]
      rw [ha_const]
      exact (isUnit_C).mpr ha_coeff_unit
    · right
      have hb_dvd : b ∣ f := ⟨a, by rw [hfab]; ring⟩
      have hb_prim : b.IsPrimitive := isPrimitive_of_dvd hprim hb_dvd
      have hb_map_natDeg_zero : (b.map φ).natDegree = 0 := by
        rcases Polynomial.isUnit_iff.mp hb_map_unit with ⟨r, _, hr_eq⟩
        rw [← hr_eq, natDegree_C]
      have hb_natDeg_zero : b.natDegree = 0 := by
        rw [← hb_natDegree_map]
        exact hb_map_natDeg_zero
      have hb_const : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb_natDeg_zero
      have hb_coeff_unit : IsUnit (b.coeff 0) := by
        apply hb_prim
        rw [← hb_const]
      rw [hb_const]
      exact (isUnit_C).mpr hb_coeff_unit

/--
`Hex.ZPoly`-level transfer of `irreducible_of_isPrimitive_of_irreducible_map_intCast_zmod`.

Given a `Hex.ZPoly` core whose Mathlib image is primitive, with a prime `p`
whose action via `Int.castRingHom (ZMod p)` does not kill the leading
coefficient, and with the reduction Mathlib-irreducible, the original core is
`Hex.ZPoly.Irreducible` via the existing equivalence.
-/
theorem Hex_ZPoly_Irreducible_of_irreducible_map_intCast_zmod
    [Fact (Nat.Prime p)]
    {core : Hex.ZPoly}
    (hprim : (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod p))
          (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hirr :
      Irreducible
        ((HexPolyZMathlib.toPolynomial core).map (Int.castRingHom (ZMod p)))) :
    Hex.ZPoly.Irreducible core :=
  (HexBerlekampZassenhausMathlib.Hex.ZPoly.polynomialIrreducible_iff_irreducible core).mp
    (irreducible_of_isPrimitive_of_irreducible_map_intCast_zmod
      hprim hlc_map_ne hirr)

/--
Small-mod singleton branch core irreducibility, stated at the executable
`Hex.ZPoly` level.

The branch-specific executable facts identify the relevant modular image as
`Hex.ZPoly.modP p core`; the coefficientwise commutation lemma rewrites its
Mathlib irreducibility into the `Polynomial.map (Int.castRingHom (ZMod p))`
hypothesis consumed by the primitive Gauss transfer above.
-/
theorem Hex_ZPoly_Irreducible_of_irreducible_modP
    [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    {core : Hex.ZPoly}
    (hprim : (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod p))
          (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hirr_modP :
      Irreducible
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p core))) :
    Hex.ZPoly.Irreducible core :=
  Hex_ZPoly_Irreducible_of_irreducible_map_intCast_zmod
    hprim hlc_map_ne
    (by
      simpa [toMathlibPolynomial_modP_eq_map_intCast_zmod] using hirr_modP)

/--
Variant of `Hex_ZPoly_Irreducible_of_irreducible_modP` for the
`PrimeChoiceData` surface used by the Berlekamp-Zassenhaus branches.

The executable prime-choice record stores the modular image as `fModP`; callers
provide the existing equality identifying it with `Hex.ZPoly.modP p core`.
-/
theorem Hex_ZPoly_Irreducible_of_primeChoice_fModP
    (primeData : Hex.PrimeChoiceData) [Fact (Nat.Prime primeData.p)]
    {core : Hex.ZPoly}
    (hfModP_eq :
      primeData.fModP =
        @Hex.ZPoly.modP primeData.p primeData.bounds core)
    (hprim : (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod primeData.p))
          (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hirr_fModP :
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p
          primeData.bounds primeData.fModP)) :
    Hex.ZPoly.Irreducible core := by
  letI := primeData.bounds
  refine Hex_ZPoly_Irreducible_of_irreducible_modP
    (p := primeData.p) (core := core) hprim hlc_map_ne ?_
  simpa [hfModP_eq] using hirr_fModP

/--
Small-mod singleton branch irreducibility package for the selected
square-free core.

The branch hypotheses mirror the executable shape: the fast path
reassembles from the singleton square-free core when the selected modular
factor list has size at most one.  The mathematical irreducibility payload is
kept as an explicit `PrimeChoiceData.fModP` irreducibility hypothesis, so the
eventual Berlekamp singleton theorem can replace it directly.
-/
theorem squareFreeCore_irreducible_of_small_mod_singleton
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (_hselected : Hex.choosePrimeData? core = some primeData)
    (_hsmall : primeData.factorsModP.size ≤ 1)
    (hprime : Nat.Prime primeData.p)
    (hfModP_eq :
      primeData.fModP =
        @Hex.ZPoly.modP primeData.p primeData.bounds core)
    (hprim :
      (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod primeData.p))
        (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hirr_fModP :
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p
          primeData.bounds primeData.fModP)) :
    Hex.ZPoly.Irreducible core := by
  haveI : Fact (Nat.Prime primeData.p) := ⟨hprime⟩
  exact Hex_ZPoly_Irreducible_of_primeChoice_fModP
    (primeData := primeData)
    (core := core)
    hfModP_eq hprim hlc_map_ne hirr_fModP

set_option maxHeartbeats 4000000 in
/-- A bridged executable polynomial that transports to a unit has executable
size one, hence passes the `gcdIsUnit` size check when used as a gcd. -/
private theorem size_eq_one_of_toMathlibPolynomial_isUnit
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    {g : Hex.FpPoly p}
    (h : IsUnit (HexBerlekampMathlib.toMathlibPolynomial g)) :
    g.size = 1 := by
  rcases Nat.lt_or_ge g.size 1 with hlt | hge
  · exfalso
    have hsize_zero : g.size = 0 := by omega
    have hzero : HexBerlekampMathlib.toMathlibPolynomial g = 0 := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
        Hex.DensePoly.coeff_eq_zero_of_size_le _ (show g.size ≤ n by omega)]
      exact HexModArithMathlib.ZMod64.toZMod_zero
    exact not_isUnit_zero (hzero ▸ h)
  · by_contra hne
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

/-- The Zassenhaus `gcdIsUnit` size check implies Berlekamp's nonzero-constant
unit-polynomial predicate. -/
private theorem isUnitPolynomial_of_gcdIsUnit
    {p : Nat} [Hex.ZMod64.Bounds p] {g : Hex.FpPoly p}
    (h : Hex.gcdIsUnit g = true) :
    Hex.Berlekamp.isUnitPolynomial g = true := by
  unfold Hex.gcdIsUnit at h
  change (g.size == 1) = true at h
  have hsize : g.size = 1 := beq_iff_eq.mp h
  unfold Hex.Berlekamp.isUnitPolynomial
  have hpos : 0 < g.size := by omega
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hpos, hsize]
  rfl

set_option maxHeartbeats 4000000 in
/--
The executable square-free check records that the raw Euclidean gcd is a
nonzero constant.  After transport to Mathlib this is enough to give
coprimality, without requiring the raw executable representative to be
definitionally equal to `1`.
-/
private theorem toMathlibPolynomial_coprime_of_gcdIsUnit
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p)
    (hsquareFree :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    IsCoprime
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) :=
  HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime f
    (isUnitPolynomial_of_gcdIsUnit hsquareFree)

/--
Scaling a nonzero modular image to its monic representative preserves the
executable square-free gcd check used by Berlekamp.
-/
private theorem gcd_monicModularImage_derivative_isUnit
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    Hex.gcdIsUnit
      (Hex.DensePoly.gcd (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))) = true := by
  let u : Hex.ZMod64 p := (Hex.DensePoly.leadingCoeff f)⁻¹
  have hmonic_eq : Hex.monicModularImage f = Hex.DensePoly.scale u f := by
    unfold Hex.monicModularImage
    simp [hzero, u]
  have hcop :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) := by
    have hcop_f :
        IsCoprime
          (HexBerlekampMathlib.toMathlibPolynomial f)
          (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) :=
      toMathlibPolynomial_coprime_of_gcdIsUnit f hsquareFree
    have hu_ne : HexModArithMathlib.ZMod64.toZMod u ≠ 0 := by
      have hp_hex : Hex.Nat.Prime p := by
        constructor
        · exact (Fact.out : Nat.Prime p).two_le
        · intro m hmdvd
          rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h
      have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ 0 :=
        fpPoly_leadingCoeff_ne_zero_of_size_pos f
          ((Hex.DensePoly.isZero_eq_false_iff _).mp hzero)
      intro hu_zero
      have hone_hex : u * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p) := by
        show (Hex.DensePoly.leadingCoeff f)⁻¹ * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p)
        exact Hex.ZMod64.inv_mul_eq_one_of_prime hp_hex hlead_ne
      have hone_z :
          HexModArithMathlib.ZMod64.toZMod u *
              HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff f) =
            (1 : ZMod p) := by
        rw [← HexModArithMathlib.ZMod64.toZMod_mul, hone_hex,
          HexModArithMathlib.ZMod64.toZMod_one]
      rw [hu_zero, zero_mul] at hone_z
      exact zero_ne_one hone_z
    have hC_unit :
        IsUnit (Polynomial.C (HexModArithMathlib.ZMod64.toZMod u)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu_ne)
    rw [hmonic_eq, toMathlibPolynomial_scale, Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left hC_unit
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))).mpr hcop_f
  let g : Hex.FpPoly p :=
    Hex.DensePoly.gcd (Hex.monicModularImage f)
      (Hex.DensePoly.derivative (Hex.monicModularImage f))
  have hunit_math :
      IsUnit
        (gcd
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
          (Polynomial.derivative
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  have hunit_transport :
      IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) := by
    rw [← HexBerlekampMathlib.toMathlibPolynomial_derivative] at hunit_math
    exact
      (HexBerlekampMathlib.toMathlibPolynomial_gcd_associated
        (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))).symm.isUnit
        hunit_math
  have hg_size : g.size = 1 :=
    size_eq_one_of_toMathlibPolynomial_isUnit hunit_transport
  unfold Hex.gcdIsUnit
  change (g.size == 1) = true
  exact beq_iff_eq.mpr hg_size

set_option maxHeartbeats 4000000

/--
Small-mod singleton irreducibility composed without the explicit
`hirr_fModP` hypothesis.

Given a `choosePrimeData?` success witness and a singleton-bounded
modular-factor count, the executable `factorsModP` array packaged by
`choosePrimeData?_factorsModP_berlekamp_form` is the Berlekamp factor
output for the monic modular image; the `irreducible_of_berlekampFactor_factors_length_le_one`
no-split lemma then turns this into Mathlib irreducibility of the monic
modular image, which transfers along `toMathlibPolynomial_scale` to
Mathlib irreducibility of `fModP` and finally to integer-level
irreducibility of `core`.

The square-free precondition on the monic modular image is supplied
explicitly. Use
`squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP`
when the selected prime's executable `squareFreeModP` check should provide it.
-/
theorem squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hprim :
      (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod primeData.p))
        (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hsquareFree_monic :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)))) = true) :
    Hex.ZPoly.Irreducible core := by
  letI := primeData.bounds
  have hprime_hex : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  have hprime : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime_hex.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime_hex.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  letI : Hex.ZMod64.PrimeModulus primeData.p := Hex.ZMod64.primeModulusOfPrime hprime_hex
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime_hex)
  letI := hfield
  -- Translate factorsModP.size ≤ 1 into bfact.factors.length ≤ 1.
  have hfactors_len_le :
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        (Hex.monicModularImage_monic hprime_hex (Hex.ZPoly.modP primeData.p core) hzero)
        hfield).factors.length ≤ 1 := by
    have hsize :
        (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          (Hex.monicModularImage_monic hprime_hex (Hex.ZPoly.modP primeData.p core) hzero)
          hfield).factors.length =
          primeData.factorsModP.size := by
      rw [hfactors_eq]
      simp [List.length_map]
    omega
  -- Positivity of the monic modular image from the positive-degree input.
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  have hform : Hex.factorsModPBerlekampForm core primeData :=
    ⟨hprime_hex, hzero, hfactors_eq⟩
  have hmonicImg_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)).degree?.getD 0 :=
    monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm
      core primeData hform hgood hcore_pos
  -- Apply the no-split lemma to obtain Mathlib irreducibility of the monic image.
  have hirr_monic :
      Irreducible
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))) :=
    HexBerlekampMathlib.irreducible_of_berlekampFactor_factors_length_le_one
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (Hex.monicModularImage_monic hprime_hex (Hex.ZPoly.modP primeData.p core) hzero)
      hmonicImg_pos
      (isUnitPolynomial_of_gcdIsUnit hsquareFree_monic) hfactors_len_le
  -- Express monicModularImage fModP as scale (leadingCoeff fModP)⁻¹ fModP.
  have hmonicImg_eq :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) =
      Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹
        (Hex.ZPoly.modP primeData.p core) := by
    unfold Hex.monicModularImage
    simp [hzero]
  -- Push through the Mathlib transport using toMathlibPolynomial_scale.
  rw [hmonicImg_eq, toMathlibPolynomial_scale] at hirr_monic
  -- The scaling constant is a unit (nonzero in the field).
  have hfsize : 0 < (Hex.ZPoly.modP primeData.p core).size :=
    (Hex.DensePoly.isZero_eq_false_iff _).mp hzero
  have hlead_ne :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core) ≠ 0 :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos (Hex.ZPoly.modP primeData.p core) hfsize
  have h_one_ne_zero : (1 : Hex.ZMod64 primeData.p) ≠ 0 := by
    intro h
    have htoNat : (1 : Hex.ZMod64 primeData.p).toNat =
        (0 : Hex.ZMod64 primeData.p).toNat := congrArg Hex.ZMod64.toNat h
    rw [show ((1 : Hex.ZMod64 primeData.p).toNat) = 1 % primeData.p from
            Hex.ZMod64.toNat_one,
        show ((0 : Hex.ZMod64 primeData.p).toNat) = 0 from Hex.ZMod64.toNat_zero,
        Nat.mod_eq_of_lt (by have := hprime_hex.two_le; omega : 1 < primeData.p)]
      at htoNat
    omega
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹ ≠ 0 := by
    intro hinv
    have hone :=
      Hex.ZMod64.inv_mul_eq_one_of_prime hprime_hex hlead_ne
    have hinv' :
        Hex.ZMod64.inv (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core)) =
          (0 : Hex.ZMod64 primeData.p) := hinv
    rw [hinv'] at hone
    have hzeromul :
        (0 : Hex.ZMod64 primeData.p) *
          Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core) =
        (0 : Hex.ZMod64 primeData.p) :=
      Lean.Grind.Semiring.zero_mul _
    rw [hzeromul] at hone
    exact h_one_ne_zero hone.symm
  have hinv_zmod_ne :
      HexModArithMathlib.ZMod64.toZMod
        (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹ ≠ 0 := by
    intro h
    apply hinv_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := primeData.p)).injective
    apply hinj
    simpa using h.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  -- Polynomial.C of a nonzero element of a field is a unit.
  have hC_unit :
      IsUnit (Polynomial.C
        (HexModArithMathlib.ZMod64.toZMod
          (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hinv_zmod_ne)
  -- An irreducible polynomial times a unit is irreducible iff the polynomial is.
  have hirr_fModP :
      Irreducible
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP primeData.p core)) := by
    have hassoc :
        Associated
          (Polynomial.C
            (HexModArithMathlib.ZMod64.toZMod
              (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹) *
              HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP primeData.p core))
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP primeData.p core)) :=
      (associated_isUnit_mul_left_iff hC_unit).mpr (Associated.refl _)
    exact hassoc.irreducible hirr_monic
  -- Conclude integer-level irreducibility via the existing transfer.
  exact Hex_ZPoly_Irreducible_of_irreducible_modP
    (p := primeData.p) (core := core)
    hprim hlc_map_ne hirr_fModP

set_option maxHeartbeats 4000000

/--
Small-mod singleton irreducibility for a selected good-prime record, deriving
the Berlekamp square-free precondition for the monic modular image from the
selected prime's executable `squareFreeModP` check.
-/
theorem squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hprim :
      (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod primeData.p))
        (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0) :
    Hex.ZPoly.Irreducible core := by
  letI := primeData.bounds
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  have hsquareFree : Hex.squareFreeModP core primeData.p :=
    Hex.isGoodPrime_squareFreeModP core primeData.p hgood
  have hsquareFree_modP :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd (@Hex.ZPoly.modP primeData.p primeData.bounds core)
          (Hex.DensePoly.derivative
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))) = true := by
    simpa [Hex.squareFreeModP] using hsquareFree
  obtain ⟨hzero, _hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hprime_hex : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  have hprime : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime_hex.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime_hex.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  have hsquareFree_monic :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)))) = true :=
    gcd_monicModularImage_derivative_isUnit
      (p := primeData.p) (Hex.ZPoly.modP primeData.p core) hzero hsquareFree_modP
  exact squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData
    core primeData hselected hcore_pos hsmall hprim hlc_map_ne hsquareFree_monic

/-- The Mathlib image over `ZMod p` of the monic modular reduction selected by a
successful `choosePrimeData?` run is squarefree.

The executable `isGoodPrime` check certifies `squareFreeModP core p`
(`gcdIsUnit (gcd (modP core) (modP core)') = true`);
`gcd_monicModularImage_derivative_isUnit` lifts this to the monic image's
coprimality with its derivative, which is exactly `Polynomial.Separable` over the
field `ZMod p`, hence `Squarefree`.  This is the modular squarefreeness datum the
mod-`p` disjointness lemma `modPFactorSubset_disjoint_of_not_associated` needs but
`modPSubsetPartitionHypotheses_of_choosePrimeData` fills with `trivial`. -/
theorem squarefree_toMathlibPolynomial_monicModPImage_of_goodPrime
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hprime_hex : Hex.Nat.Prime primeData.p)
    (hgood :
      letI := primeData.bounds
      @Hex.isGoodPrime core primeData.p primeData.bounds = true) :
    Squarefree
      (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))) := by
  letI := primeData.bounds
  have hsquareFree : Hex.squareFreeModP core primeData.p :=
    Hex.isGoodPrime_squareFreeModP core primeData.p hgood
  have hsquareFree_modP :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd (@Hex.ZPoly.modP primeData.p primeData.bounds core)
          (Hex.DensePoly.derivative
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))) = true := by
    simpa [Hex.squareFreeModP] using hsquareFree
  have hzero : (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  have hprime : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime_hex.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime_hex.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  have hsquareFree_monic :
      Hex.gcdIsUnit
        (Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)))) = true :=
    gcd_monicModularImage_derivative_isUnit
      (p := primeData.p) (Hex.ZPoly.modP primeData.p core) hzero hsquareFree_modP
  have hsep :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial
            (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))) :=
    HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (isUnitPolynomial_of_gcdIsUnit hsquareFree_monic)
  have hsf :
      Squarefree
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))) :=
    Polynomial.Separable.squarefree hsep
  rwa [monicModPImage_eq_monicModularImage]

/-- **modP pairwise-disjointness from a `choosePrimeData?` witness.**

Specialisation of `modPFactorSubset_disjoint_of_not_associated` to the executable
`choosePrimeData?` boundary: the selected prime is `isGoodPrime`, which supplies
both the nonzero mod-`p` core (`isGoodPrime_modP_isZero_false`) and the modular
squarefreeness (`squarefree_toMathlibPolynomial_monicModPImage_of_choosePrimeData`)
that the bare `ModPSubsetPartitionHypotheses … True True` package fills with
`trivial`. -/
theorem modPFactorSubset_disjoint_of_modPFactorization
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (hval : ModPFactorization core primeData)
    (hcore_pos : 0 < core.degree?.getD 0)
    {f g : Hex.ZPoly} {S T : ModPFactorSubset primeData}
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f)) (hf_dvd : f ∣ core)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g)) (hg_dvd : g ∣ core)
    (hS : RepresentsIntegerFactorModP primeData f S)
    (hT : RepresentsIntegerFactorModP primeData g T)
    (hnotassoc :
      ¬ Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g)) :
    Disjoint S T := by
  letI := primeData.bounds
  have hprime_hex : Hex.Nat.Prime primeData.p := hval.prime
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    hval.good
  have hcore_modP_nz :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  exact modPFactorSubset_disjoint_of_not_associated hprime_hex
    (modPSubsetPartitionHypotheses_of_modPFactorization core primeData hcore_pos hval)
    hcore_modP_nz
    (squarefree_toMathlibPolynomial_monicModPImage_of_goodPrime core primeData
      hval.prime hval.good)
    hf_irr hf_dvd hg_irr hg_dvd hS hT hnotassoc

/-! ### Base discharges for the small-mod singleton branch

The two lemmas below feed `squareFreeCore_irreducible_of_small_mod_singleton`
its `hprim` and `hlc_map_ne` side-conditions from the executable invariants
that `normalizeForFactor` and `choosePrimeData?` already maintain. They
form the base lemmas for the small-mod singleton arm of the HO-1 capstone
`factorize_irreducible_of_nonUnit` (issue #4170, decomposed in #4544).
-/

/--
Identification of the executable `Hex.ZPoly.Primitive` predicate with Mathlib's
`Polynomial.IsPrimitive` on the transported polynomial.

If the integer-coefficient gcd of `f` is `1`, then any integer `r` whose
constant polynomial `C r` divides `toPolynomial f` must divide every
coefficient of `f`, hence divides the executable `content f = 1`, hence
`|r| = 1`, hence `r` is a unit.
-/
theorem toPolynomial_isPrimitive_of_zpoly_primitive
    {f : Hex.ZPoly} (hprim : Hex.ZPoly.Primitive f) :
    (HexPolyZMathlib.toPolynomial f).IsPrimitive := by
  intro r hdvd
  have hcoeff : ∀ n, r ∣ f.coeff n := by
    intro n
    have h :=
      (Polynomial.C_dvd_iff_dvd_coeff r (HexPolyZMathlib.toPolynomial f)).mp hdvd n
    rwa [HexPolyZMathlib.coeff_toPolynomial] at h
  have hnatAbs_dvd : ∀ n, (r.natAbs : ℤ) ∣ f.coeff n := fun n =>
    Int.natAbs_dvd.mpr (hcoeff n)
  have hr_dvd_content : (r.natAbs : ℤ) ∣ Hex.ZPoly.content f :=
    Hex.ZPoly.dvd_content_of_nat_dvd_coeff f r.natAbs hnatAbs_dvd
  rw [show Hex.ZPoly.content f = 1 from hprim] at hr_dvd_content
  have hone : r.natAbs ∣ 1 := by exact_mod_cast hr_dvd_content
  exact Int.isUnit_iff_natAbs_eq.mpr (Nat.eq_one_of_dvd_one hone)

/-- The product `squareFreeCore * repeatedPart` extracted from a nonzero
integer polynomial by `Hex.normalizeForFactor` is executably primitive. -/
theorem normalizeForFactor_squareFreeCore_mul_repeatedPart_primitive_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.Primitive
      ((Hex.normalizeForFactor f).squareFreeCore *
        (Hex.normalizeForFactor f).repeatedPart) := by
  have hcore_ne :
      (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core ≠ 0 :=
    Hex.extractXPower_core_ne_zero_of_ne_zero f hf
  simpa [Hex.normalizeForFactor] using
    Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive
      _ hcore_ne

/--
The square-free core extracted by `normalizeForFactor` is primitive
over `Polynomial ℤ` whenever the input integer polynomial is nonzero.

The proof routes through the executable `Hex.ZPoly.Primitive` predicate
on `squareFreeCore * repeatedPart` (from
`primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`),
transports it to `Polynomial ℤ` via
`toPolynomial_isPrimitive_of_zpoly_primitive`, and drops to the square-free
factor via Mathlib's `Polynomial.isPrimitive_of_dvd`.

This discharges the `hprim` hypothesis required by
`squareFreeCore_irreducible_of_small_mod_singleton`.
-/
theorem normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).IsPrimitive := by
  have hprod_prim :=
    normalizeForFactor_squareFreeCore_mul_repeatedPart_primitive_of_ne_zero f hf
  have hprod_isPrim :
      (HexPolyZMathlib.toPolynomial
          ((Hex.normalizeForFactor f).squareFreeCore *
            (Hex.normalizeForFactor f).repeatedPart)).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive hprod_prim
  rw [HexPolyZMathlib.toPolynomial_mul] at hprod_isPrim
  exact isPrimitive_of_dvd hprod_isPrim
    ⟨HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart, rfl⟩

/--
The repeated part extracted by `normalizeForFactor` is primitive over
`Polynomial ℤ` whenever the input integer polynomial is nonzero.

This is the companion Gauss-descent input to
`normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive` for the
structural divisibility theorem consumed by the exponent-extraction
successor.
-/
theorem normalizeForFactor_repeatedPart_toPolynomial_isPrimitive
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).repeatedPart).IsPrimitive := by
  have hprod_prim :=
    normalizeForFactor_squareFreeCore_mul_repeatedPart_primitive_of_ne_zero f hf
  have hprod_isPrim :
      (HexPolyZMathlib.toPolynomial
          ((Hex.normalizeForFactor f).squareFreeCore *
            (Hex.normalizeForFactor f).repeatedPart)).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive hprod_prim
  rw [HexPolyZMathlib.toPolynomial_mul] at hprod_isPrim
  exact isPrimitive_of_dvd hprod_isPrim
    ⟨HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore, by
      rw [mul_comm]⟩

/--
The repeated part extracted by `normalizeForFactor` is already
`normalize`-fixed after transport to `Polynomial ℤ`.

This packages the executable nonnegative-leading-coefficient invariant in the
form expected by UFD uniqueness arguments.
-/
theorem normalizeForFactor_repeatedPart_toPolynomial_normalize
    (f : Hex.ZPoly) (_hf : f ≠ 0) :
    normalize (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).repeatedPart) =
      HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart := by
  have hlc_nonneg :
      0 ≤ (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).repeatedPart).leadingCoeff := by
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    unfold Hex.normalizeForFactor
    exact Hex.ZPoly.leadingCoeff_repeatedPart_nonneg _
  rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq, if_pos hlc_nonneg,
    Units.val_one, Polynomial.C_1, mul_one]

private theorem isPrimitive_pow {p : Polynomial ℤ} (hp : p.IsPrimitive) (N : Nat) :
    (p ^ N).IsPrimitive := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      simpa [pow_succ] using ih.mul hp

/-! ### Squarefree transport for the square-free core

The lemmas below identify the executable `Hex.ZPoly.SquareFreeRat` invariant
(from `Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore`) to
Mathlib's `Squarefree` over `Polynomial ℤ` via the rational image.  The
chain is:

1. `toPolynomial_derivative` — `HexPolyMathlib.toPolynomial` intertwines
   the executable `Hex.DensePoly.derivative` with `Polynomial.derivative`.
2. `toPolynomial_toRatPoly_eq_map_intCast` — `HexPolyMathlib.toPolynomial`
   applied to the rational view of an integer polynomial agrees with the
   integer-side `toPolynomial` composed with `Polynomial.map`
   `(Int.castRingHom ℚ)`.
3. `isCoprime_toPolynomial_map_intCast_derivative_of_squareFreeRat` — the
   executable square-free invariant transports to coprimeness with the
   formal derivative over `Polynomial ℚ`, using
   `HexPolyMathlib.toPolynomial_gcd_associated` over the field `ℚ`.
4. `squarefree_of_isPrimitive_of_squarefree_map_intCast` — the Gauss-style
   descent: a primitive integer polynomial is squarefree whenever its
   rational image is.

The main theorem then combines `_isPrimitive` with the executable
square-free invariant for `normalizeForFactor f`. -/

/--
The executable formal derivative on `Hex.DensePoly R` agrees with Mathlib's
`Polynomial.derivative` under the `HexPolyMathlib.toPolynomial` transport, for
any commutative semiring with decidable equality.
-/
theorem toPolynomial_derivative
    {R : Type*} [CommSemiring R] [DecidableEq R] (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.derivative p) =
      Polynomial.derivative (HexPolyMathlib.toPolynomial p) := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial,
      Hex.DensePoly.coeff_derivative p n (mul_zero _),
      Polynomial.coeff_derivative,
      HexPolyMathlib.coeff_toPolynomial]
  push_cast
  ring

/--
The rational view of an integer polynomial through the executable
`Hex.ZPoly.toRatPoly` agrees with the integer-side `toPolynomial`
post-composed with `Polynomial.map (Int.castRingHom ℚ)`.  This is the
identity that lets the executable `SquareFreeRat` invariant be read as
a Mathlib statement about the rational image of `toPolynomial f`.
-/
theorem toPolynomial_toRatPoly_eq_map_intCast (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) =
      (HexPolyZMathlib.toPolynomial f).map (Int.castRingHom ℚ) := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_map,
      HexPolyZMathlib.coeff_toPolynomial, Hex.ZPoly.coeff_toRatPoly]
  rfl

/--
The executable `Hex.ZPoly.SquareFreeRat` invariant transports to
`IsCoprime` of the rational image of `toPolynomial f` with its formal
derivative.  This is the field-side discharge of the squarefree
predicate: once the executable rational gcd is shown to be a unit (which
follows from `(gcd …).size ≤ 1` together with `f ≠ 0`), the
gcd-associatedness lemma `HexPolyMathlib.toPolynomial_gcd_associated`
forces the Mathlib gcd to be a unit too, which is `IsCoprime`.
-/
theorem isCoprime_toPolynomial_map_intCast_derivative_of_squareFreeRat
    (f : Hex.ZPoly) (hf : f ≠ 0) (hsf : Hex.ZPoly.SquareFreeRat f) :
    IsCoprime ((HexPolyZMathlib.toPolynomial f).map (Int.castRingHom ℚ))
      ((HexPolyZMathlib.toPolynomial f).map (Int.castRingHom ℚ)).derivative := by
  -- Re-express the goal in `HexPolyMathlib` terms over `Polynomial ℚ`.
  have hp_eq :
      (HexPolyZMathlib.toPolynomial f).map (Int.castRingHom ℚ) =
        HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) :=
    (toPolynomial_toRatPoly_eq_map_intCast f).symm
  have hp'_eq :
      ((HexPolyZMathlib.toPolynomial f).map (Int.castRingHom ℚ)).derivative =
        HexPolyMathlib.toPolynomial
          (Hex.DensePoly.derivative (Hex.ZPoly.toRatPoly f)) := by
    rw [hp_eq, ← toPolynomial_derivative]
  rw [hp'_eq, hp_eq]
  -- Reduce coprimeness to the Mathlib gcd being a unit.
  rw [← EuclideanDomain.gcd_isUnit_iff]
  -- The Mathlib gcd is associated to the transported executable gcd.
  have hassoc :=
    HexPolyMathlib.toPolynomial_gcd_associated
      (Hex.ZPoly.toRatPoly f) (Hex.DensePoly.derivative (Hex.ZPoly.toRatPoly f))
  refine (hassoc.isUnit_iff).mp ?_
  -- The transported executable gcd is `C (G.coeff 0)` with `G.coeff 0 ≠ 0`.
  set G := Hex.DensePoly.gcd (Hex.ZPoly.toRatPoly f)
    (Hex.DensePoly.derivative (Hex.ZPoly.toRatPoly f)) with hG_def
  have hsize : G.size ≤ 1 := hsf
  -- `G ≠ 0` because it divides the nonzero `toRatPoly f`.
  have hg_ne : Hex.ZPoly.toRatPoly f ≠ 0 := by
    intro hg
    apply hf
    apply Hex.DensePoly.ext_coeff
    intro n
    have hcoeff : ((f.coeff n : Int) : Rat) = 0 := by
      rw [← Hex.ZPoly.coeff_toRatPoly, hg, Hex.DensePoly.coeff_zero]
    rw [Hex.DensePoly.coeff_zero]
    exact_mod_cast hcoeff
  have hG_ne : G ≠ 0 := by
    intro hG_zero
    apply hg_ne
    have hdvd : G ∣ Hex.ZPoly.toRatPoly f :=
      Hex.DensePoly.gcd_dvd_left _ _
    rw [hG_zero] at hdvd
    rcases hdvd with ⟨r, hr⟩
    rw [hr, Hex.DensePoly.zero_mul]
  have hG_size_pos : 0 < G.size := by
    rcases Nat.eq_zero_or_pos G.size with h | h
    · exfalso
      apply hG_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le G (by omega)
    · exact h
  have hG_size_eq : G.size = 1 := le_antisymm hsize hG_size_pos
  -- Last (= only) coefficient of `G` is nonzero, so `toPolynomial G = C (G.coeff 0)`.
  have hG_coeff_zero_ne : G.coeff 0 ≠ 0 := by
    have h := Hex.DensePoly.coeff_last_ne_zero_of_pos_size G hG_size_pos
    have key : G.coeff 0 ≠ Zero.zero := by simpa [hG_size_eq] using h
    exact key
  have hG_eq_C :
      HexPolyMathlib.toPolynomial G = Polynomial.C (G.coeff 0) := by
    apply Polynomial.ext
    intro n
    rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_C]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le G (by
        cases n with
        | zero => exact absurd rfl hn
        | succ k => omega)
  rw [hG_eq_C]
  exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hG_coeff_zero_ne)

/--
Gauss-style descent for squarefreeness: a primitive integer polynomial is
squarefree iff its rational image is, and in particular the implication
from rational to integer follows.

Given `p : Polynomial ℤ` primitive and `Squarefree (p.map (Int.castRingHom ℚ))`,
any square factor `q² ∣ p` lifts to `(q.map …)² ∣ p.map …`, forcing
`q.map …` to be a unit; the injective cast then pins `q` to a nonzero
constant `C n`, and primitivity of `p` plus `C (n * n) ∣ p` forces `n * n`
(hence `n`, hence `q`) to be a unit in `ℤ[X]`.
-/
theorem squarefree_of_isPrimitive_of_squarefree_map_intCast
    {p : Polynomial ℤ} (hp : p.IsPrimitive)
    (hsf : Squarefree (p.map (Int.castRingHom ℚ))) :
    Squarefree p := by
  intro q hq
  -- Map the square factorisation to `Polynomial ℚ`.
  have hmap :
      (q.map (Int.castRingHom ℚ)) * (q.map (Int.castRingHom ℚ)) ∣
        p.map (Int.castRingHom ℚ) := by
    rw [← Polynomial.map_mul]
    exact Polynomial.map_dvd _ hq
  have hunit_Q : IsUnit (q.map (Int.castRingHom ℚ)) := hsf _ hmap
  -- A unit in `Polynomial ℚ` has `natDegree 0`.
  have hnd_map : (q.map (Int.castRingHom ℚ)).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hunit_Q
  -- The integer cast `Int.castRingHom ℚ` is injective, so `q.natDegree = 0`.
  have hcast_inj : Function.Injective (Int.castRingHom ℚ) :=
    Int.cast_injective
  have hnd_q : q.natDegree = 0 := by
    rw [← Polynomial.natDegree_map_eq_of_injective hcast_inj q]
    exact hnd_map
  -- So `q = C n` for some `n : ℤ`.
  obtain ⟨n, hn⟩ : ∃ n, q = Polynomial.C n :=
    ⟨q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hnd_q⟩
  -- Then `C (n * n) ∣ p`, and primitivity forces `IsUnit (n * n)`.
  have hCnn_dvd : Polynomial.C (n * n) ∣ p := by
    rw [show Polynomial.C (n * n) = q * q by rw [hn, ← Polynomial.C_mul]]
    exact hq
  have hnn_unit : IsUnit (n * n) :=
    (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hp) _ hCnn_dvd
  have hn_unit : IsUnit n := by
    rw [show n * n = n ^ 2 by ring] at hnn_unit
    exact (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hnn_unit
  -- Hence `q = C n` is a unit in `Polynomial ℤ`.
  rw [hn]
  exact Polynomial.isUnit_C.mpr hn_unit

/--
The square-free core extracted by `normalizeForFactor` is squarefree over
`Polynomial ℤ` whenever the input integer polynomial is nonzero.

The proof composes the rational-side squarefreeness obtained from the
executable `Hex.ZPoly.SquareFreeRat` invariant
(`primitiveSquareFreeDecomposition_squareFreeCore`,
`HexPolyZ/Basic.lean:2997`) via `Separable.squarefree` with the
Gauss-style descent
`squarefree_of_isPrimitive_of_squarefree_map_intCast`, using the
existing primitivity lemma
`normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`.

This discharges the explicit `hcore_sqfree` hypothesis previously threaded
through `liftedFactorSubsetPartition_outerBound_of_choosePrimeData`
(`HexBerlekampZassenhausMathlib`); the outer-bound
specialisation is rewired to consume `f ≠ 0` directly. -/
theorem normalizeForFactor_squareFreeCore_toPolynomial_squarefree
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Squarefree
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore) := by
  -- The square-free core of `normalizeForFactor f` is nonzero.  We argue
  -- from primitivity of the product `squareFreeCore * repeatedPart`:
  -- if the core were zero, the product would be zero, contradicting
  -- primitivity (the zero polynomial has zero content).
  have hcore_sq_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 := by
    intro hzero
    have hprod_prim :=
      normalizeForFactor_squareFreeCore_mul_repeatedPart_primitive_of_ne_zero f hf
    have hprod_ne :
        (Hex.normalizeForFactor f).squareFreeCore *
          (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
      Hex.ZPoly.ne_zero_of_primitive _ hprod_prim
    apply hprod_ne
    rw [hzero, Hex.DensePoly.zero_mul]
  have hsf_rat :
      Hex.ZPoly.SquareFreeRat (Hex.normalizeForFactor f).squareFreeCore := by
    have :=
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
        (by
          simpa [Hex.normalizeForFactor] using hcore_sq_ne)
    simpa [Hex.normalizeForFactor] using this
  -- Build coprimeness with the derivative over `Polynomial ℚ`.
  have hcoprime :=
    isCoprime_toPolynomial_map_intCast_derivative_of_squareFreeRat
      (Hex.normalizeForFactor f).squareFreeCore hcore_sq_ne hsf_rat
  -- Squarefree of the rational image via `Separable.squarefree`.
  have hsf_Q :
      Squarefree
        ((HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore).map
          (Int.castRingHom ℚ)) :=
    Polynomial.Separable.squarefree hcoprime
  -- Gauss descent: primitive + squarefree over ℚ ⇒ squarefree over ℤ.
  exact squarefree_of_isPrimitive_of_squarefree_map_intCast
    (normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive f hf) hsf_Q

/--
Identification of the executable `isGoodPrime` invariant with the Mathlib
`Int.castRingHom (ZMod p)`-cast leading-coefficient nonvanishing
required by the reduction-mod-`p` machinery.

The good-prime predicate carries `leadingCoeffAdmissible`, i.e. the
executable `leadingCoeffModP` is nonzero; the iff lemma
`intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero`
translates that into the Mathlib cast form.
-/
theorem leadingCoeff_castRingHom_ne_zero_of_isGoodPrime
    [Hex.ZMod64.Bounds p] (f : Hex.ZPoly)
    (hgood : Hex.isGoodPrime f p = true) :
    (Int.castRingHom (ZMod p)) (HexPolyZMathlib.toPolynomial f).leadingCoeff ≠ 0 :=
  (intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
    (p := p) (f := f)).mpr (Hex.isGoodPrime_leadingCoeffAdmissible f p hgood)

/--
Variant of `leadingCoeff_castRingHom_ne_zero_of_isGoodPrime` specialised
to a `choosePrimeData?`-selected good prime.

Discharges the `hlc_map_ne` hypothesis required by
`squareFreeCore_irreducible_of_small_mod_singleton` when the executable
prime selection succeeds: the chosen prime's `ZMod`-cast leading
coefficient is nonzero because `choosePrimeData?_isGoodPrime` certifies
the `isGoodPrime` invariant.
-/
theorem choosePrimeData?_leadingCoeff_castRingHom_ne_zero
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? f = some primeData) :
    (Int.castRingHom (ZMod primeData.p))
        (HexPolyZMathlib.toPolynomial f).leadingCoeff ≠ 0 := by
  letI := primeData.bounds
  exact
    leadingCoeff_castRingHom_ne_zero_of_isGoodPrime f
      (Hex.choosePrimeData?_isGoodPrime f primeData hselected)

/--
Reverse identification from Mathlib's `Polynomial.IsPrimitive` on the transported
polynomial to the executable `Hex.ZPoly.Primitive` predicate.

Apply `IsPrimitive` at the constant polynomial `C (content f)` (which divides
`toPolynomial f` because `content f` divides every integer coefficient), to
conclude `IsUnit (content f)` in `ℤ`. Combined with the non-negativity of
`Hex.ZPoly.content` (it is `Int.ofNat` of `DensePoly.contentNat`), this forces
`content f = 1`.
-/
theorem zpoly_primitive_of_toPolynomial_isPrimitive
    {f : Hex.ZPoly}
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive) :
    Hex.ZPoly.Primitive f := by
  show Hex.ZPoly.content f = 1
  have hC_dvd :
      Polynomial.C (Hex.ZPoly.content f) ∣ HexPolyZMathlib.toPolynomial f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [HexPolyZMathlib.coeff_toPolynomial]
    exact Hex.ZPoly.content_dvd_coeff f n
  have hIsUnit : IsUnit (Hex.ZPoly.content f) := hprim _ hC_dvd
  have hcontent_nonneg : 0 ≤ Hex.ZPoly.content f := by
    show 0 ≤ Hex.DensePoly.content f
    unfold Hex.DensePoly.content
    exact Int.natCast_nonneg _
  rcases Int.isUnit_iff.mp hIsUnit with hone | hneg
  · exact hone
  · rw [hneg] at hcontent_nonneg; omega

/--
The square-free core extracted by `normalizeForFactor` is executably
primitive whenever the input integer polynomial is nonzero.

The proof transports
`normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive` back to
`Hex.ZPoly` via `zpoly_primitive_of_toPolynomial_isPrimitive`.
-/
theorem normalizeForFactor_squareFreeCore_primitive_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore :=
  zpoly_primitive_of_toPolynomial_isPrimitive
    (normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive f hf)

/--
Helper for the coprime inductive step of
`gcd_derivative_associated_divRadical_of_charZero`. In any `GCDMonoid`,
divisibility into a product factors through the component gcds:
`g ∣ x * y → g ∣ gcd g x * gcd g y`. Two applications of
`dvd_gcd_mul_of_dvd_mul` (in `Mathlib/Algebra/GCDMonoid/Basic.lean`) deliver
the result without needing coprimality of `x` and `y`.
-/
private lemma dvd_gcd_mul_gcd_of_dvd_mul {α : Type*} [EuclideanDomain α]
    [DecidableEq α] {g x y : α} (h : g ∣ x * y) :
    g ∣ EuclideanDomain.gcd g x * EuclideanDomain.gcd g y := by
  letI : GCDMonoid α := EuclideanDomain.gcdMonoid α
  show g ∣ gcd g x * gcd g y
  have h1 : g ∣ gcd g x * y := dvd_gcd_mul_of_dvd_mul h
  rw [mul_comm] at h1
  have h2 : g ∣ gcd g y * gcd g x := dvd_gcd_mul_of_dvd_mul h1
  rwa [mul_comm] at h2

/--
**#4617 base task (HO-1, sub-issue of #4610).**

For a polynomial `p` over a characteristic-zero field `K`, the executable gcd
`gcd p p'` is associated to `divRadical p = p / radical p`.

Mathlib already supplies the easy direction
`divRadical p ∣ gcd p p'` (via `divRadical_dvd_self` and
`divRadical_dvd_derivative` in `Mathlib/RingTheory/Polynomial/Radical.lean`).
The reverse direction `gcd p p' ∣ divRadical p` is the char-0 multiplicity
fact: for a prime `q` in `K[X]` and `p = q^e * f` coprime to `q`, in
char-0 the derivative `p'` has `q`-multiplicity exactly `e - 1`, so
`gcd p p'` has `q`-multiplicity `min(e, e-1) = e - 1`.

The proof goes by `UniqueFactorizationMonoid.induction_on_coprime`. The
prime-power case uses `dvd_prime_pow` to extract a candidate exponent and
discharges the saturating case by combining char-0 with separability
(`PerfectField.separable_of_irreducible` from `PerfectField.ofCharZero`).
The coprime case uses the `GCDMonoid` lemma `dvd_gcd_mul_of_dvd_mul`
applied twice to factor divisibility through component gcds, then chains
each component to the inductive hypothesis via `IsCoprime.dvd_of_dvd_mul_right`.
No new `axiom`, `native_decide`, `sorry`, `TODO`, or `FIXME`.
-/
theorem Polynomial.gcd_derivative_associated_divRadical_of_charZero
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (p : Polynomial K) :
    Associated (EuclideanDomain.gcd p (Polynomial.derivative p))
      (EuclideanDomain.divRadical p) := by
  induction p using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    rw [Polynomial.derivative_zero, EuclideanDomain.gcd_zero_left,
      EuclideanDomain.divRadical, UniqueFactorizationMonoid.radical_zero,
      EuclideanDomain.div_one]
  | @h1 u hu =>
    obtain ⟨c, _hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [Polynomial.derivative_C, EuclideanDomain.gcd_zero_right,
      EuclideanDomain.divRadical, UniqueFactorizationMonoid.radical_of_isUnit hu,
      EuclideanDomain.div_one]
  | @hpr q k hq =>
    cases k with
    | zero =>
      rw [pow_zero, Polynomial.derivative_one, EuclideanDomain.gcd_zero_right,
        EuclideanDomain.divRadical, UniqueFactorizationMonoid.radical_one,
        EuclideanDomain.div_one]
    | succ k =>
      have hq_ne : q ≠ 0 := hq.ne_zero
      have hnorm_q_ne : normalize q ≠ 0 := by rwa [Ne, normalize_eq_zero]
      -- (a) divRadical (q^(k+1)) is associated to q^k.
      have hdivR_assoc :
          Associated (EuclideanDomain.divRadical (q ^ (k + 1))) (q ^ k) := by
        have hradq :
            UniqueFactorizationMonoid.radical (q ^ (k + 1)) = normalize q :=
          UniqueFactorizationMonoid.radical_pow_of_prime hq (Nat.succ_ne_zero _)
        have heq : normalize q * EuclideanDomain.divRadical (q ^ (k + 1))
            = q * q ^ k := by
          have hmd := EuclideanDomain.radical_mul_divRadical (a := q ^ (k + 1))
          rw [hradq] at hmd
          rw [hmd, pow_succ, mul_comm]
        exact Associated.of_mul_left (Associated.of_eq heq)
          (normalize_associated q) hnorm_q_ne
      -- (b) gcd q^(k+1) (derivative q^(k+1)) is associated to q^k.
      have hgcd_assoc : Associated
          (EuclideanDomain.gcd (q ^ (k + 1)) (Polynomial.derivative (q ^ (k + 1))))
          (q ^ k) := by
        set g := EuclideanDomain.gcd (q ^ (k + 1))
          (Polynomial.derivative (q ^ (k + 1))) with hg_def
        -- (b.i) q^k ∣ g.
        have hqk_dvd_g : q ^ k ∣ g := by
          refine EuclideanDomain.dvd_gcd ?_ ?_
          · exact pow_dvd_pow q (Nat.le_succ k)
          · rw [Polynomial.derivative_pow_succ]
            exact (dvd_mul_left _ _).mul_right _
        -- (b.ii) g ∣ q^k.
        have hg_dvd_qk : g ∣ q ^ k := by
          have hg_dvd_pow : g ∣ q ^ (k + 1) := EuclideanDomain.gcd_dvd_left _ _
          obtain ⟨m, hm_le, hm_assoc⟩ := (dvd_prime_pow hq (k + 1)).1 hg_dvd_pow
          have hm_lt : m < k + 1 := by
            rcases lt_or_eq_of_le hm_le with h | h
            · exact h
            · exfalso
              subst h
              have hg_dvd_deriv : g ∣ Polynomial.derivative (q ^ (k + 1)) :=
                EuclideanDomain.gcd_dvd_right _ _
              have hpow_dvd_deriv : q ^ (k + 1) ∣
                  Polynomial.derivative (q ^ (k + 1)) :=
                hm_assoc.symm.dvd.trans hg_dvd_deriv
              rw [Polynomial.derivative_pow_succ] at hpow_dvd_deriv
              have hcancel : q ∣ Polynomial.C ((k : K) + 1) *
                  Polynomial.derivative q := by
                rw [show q ^ (k + 1) = q ^ k * q from pow_succ q k,
                  mul_comm (Polynomial.C _) (q ^ k), mul_assoc] at hpow_dvd_deriv
                exact (mul_dvd_mul_iff_left (pow_ne_zero _ hq_ne)).mp
                  hpow_dvd_deriv
              have hk1_ne : ((k : K) + 1) ≠ 0 := by
                exact_mod_cast Nat.succ_ne_zero k
              have hC_unit : IsUnit (Polynomial.C ((k : K) + 1)) :=
                Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk1_ne)
              have hq_dvd_deriv : q ∣ Polynomial.derivative q :=
                (IsUnit.dvd_mul_left hC_unit).mp hcancel
              have hsep : (q : Polynomial K).Separable :=
                PerfectField.separable_of_irreducible hq.irreducible
              have hcop : IsCoprime q (Polynomial.derivative q) := hsep
              exact hq.not_unit (hcop.isUnit_of_dvd' dvd_rfl hq_dvd_deriv)
          have hm_le_k : m ≤ k := Nat.lt_succ_iff.mp hm_lt
          exact hm_assoc.dvd.trans (pow_dvd_pow q hm_le_k)
        exact associated_of_dvd_dvd hg_dvd_qk hqk_dvd_g
      exact hgcd_assoc.trans hdivR_assoc.symm
  | @hcp x y hxy ihx ihy =>
    have hcop : IsCoprime x y := hxy.isCoprime
    have hdivR_xy :
        EuclideanDomain.divRadical (x * y) =
          EuclideanDomain.divRadical x * EuclideanDomain.divRadical y :=
      EuclideanDomain.divRadical_mul hcop
    set g := EuclideanDomain.gcd (x * y) (Polynomial.derivative (x * y))
      with hg_def
    -- Forward: divRadical (xy) ∣ g (from Mathlib).
    have hfwd : EuclideanDomain.divRadical (x * y) ∣ g := by
      refine EuclideanDomain.dvd_gcd ?_ ?_
      · exact EuclideanDomain.divRadical_dvd_self _
      · exact divRadical_dvd_derivative _
    -- Reverse: g ∣ divRadical (xy).
    have hrev : g ∣ EuclideanDomain.divRadical (x * y) := by
      rw [hdivR_xy]
      have hg_dvd_xy : g ∣ x * y := EuclideanDomain.gcd_dvd_left _ _
      have hg_dvd_prod : g ∣ EuclideanDomain.gcd g x * EuclideanDomain.gcd g y :=
        dvd_gcd_mul_gcd_of_dvd_mul hg_dvd_xy
      set gx := EuclideanDomain.gcd g x with hgx_def
      set gy := EuclideanDomain.gcd g y with hgy_def
      have hgx_dvd_divR : gx ∣ EuclideanDomain.divRadical x := by
        have hgx_x : gx ∣ x := EuclideanDomain.gcd_dvd_right _ _
        have hgx_g : gx ∣ g := EuclideanDomain.gcd_dvd_left _ _
        have hgx_deriv_xy : gx ∣ Polynomial.derivative (x * y) :=
          hgx_g.trans (EuclideanDomain.gcd_dvd_right _ _)
        rw [Polynomial.derivative_mul] at hgx_deriv_xy
        have hgx_xdy : gx ∣ x * Polynomial.derivative y := hgx_x.mul_right _
        have hgx_dxy : gx ∣ Polynomial.derivative x * y :=
          (dvd_add_left hgx_xdy).mp hgx_deriv_xy
        have hcop_gxy : IsCoprime gx y :=
          IsCoprime.of_isCoprime_of_dvd_left hcop hgx_x
        have hgx_dx : gx ∣ Polynomial.derivative x :=
          hcop_gxy.dvd_of_dvd_mul_right hgx_dxy
        exact (EuclideanDomain.dvd_gcd hgx_x hgx_dx).trans ihx.dvd
      have hgy_dvd_divR : gy ∣ EuclideanDomain.divRadical y := by
        have hgy_y : gy ∣ y := EuclideanDomain.gcd_dvd_right _ _
        have hgy_g : gy ∣ g := EuclideanDomain.gcd_dvd_left _ _
        have hgy_deriv_xy : gy ∣ Polynomial.derivative (x * y) :=
          hgy_g.trans (EuclideanDomain.gcd_dvd_right _ _)
        rw [Polynomial.derivative_mul] at hgy_deriv_xy
        have hgy_dxy : gy ∣ Polynomial.derivative x * y := hgy_y.mul_left _
        have hgy_xdy : gy ∣ x * Polynomial.derivative y :=
          (dvd_add_right hgy_dxy).mp hgy_deriv_xy
        have hcop_gyx : IsCoprime gy x :=
          IsCoprime.of_isCoprime_of_dvd_left hcop.symm hgy_y
        have hgy_dy : gy ∣ Polynomial.derivative y := by
          rw [mul_comm] at hgy_xdy
          exact hcop_gyx.dvd_of_dvd_mul_right hgy_xdy
        exact (EuclideanDomain.dvd_gcd hgy_y hgy_dy).trans ihy.dvd
      exact hg_dvd_prod.trans (mul_dvd_mul hgx_dvd_divR hgy_dvd_divR)
    exact associated_of_dvd_dvd hrev hfwd


end IntReductionMod
end HexBerlekampZassenhausMathlib
