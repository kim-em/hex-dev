import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampMathlib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
Reduction-mod-`p` irreducibility lemma for primitive integer polynomials, used
by the Berlekamp-Zassenhaus small-mod singleton branch.

The classical statement: if `f : ℤ[X]` is primitive and `f` reduced modulo a
prime `p` is irreducible in `(ZMod p)[X]` with the leading coefficient
surviving the reduction, then `f` is irreducible in `ℤ[X]`. The argument is
the standard Gauss-style reduction: any factorization `f = g * h` with both
factors non-unit pushes through `Polynomial.map`; controlling natural degree
across the reduction shows the image factors are also non-unit; primitivity
then promotes a degree-zero ℤ-factor to a unit.
-/

namespace HexBerlekampZassenhausMathlib

namespace IntReductionMod

open Polynomial

variable {p : ℕ}

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

The branch hypotheses mirror the executable shape:
`factorWithBound_entry_mem_small_mod_singleton_raw` shows that the fast path
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
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) := by
  let g : Hex.FpPoly p := Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)
  have hg_size : g.size = 1 := by
    unfold Hex.gcdIsUnit at hsquareFree
    change (g.size == 1) = true at hsquareFree
    exact beq_iff_eq.mp hsquareFree
  have hg_pos : 0 < g.size := by omega
  have hg_coeff_ne : g.coeff 0 ≠ 0 := by
    have hlast := Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hg_pos
    simpa [hg_size] using hlast
  have hg_coeff_zmod_ne :
      HexModArithMathlib.ZMod64.toZMod (g.coeff 0) ≠ 0 := by
    intro hzero
    apply hg_coeff_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
    apply hinj
    simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  have hg_poly_unit :
      IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) := by
    have hg_poly_eq :
        HexBerlekampMathlib.toMathlibPolynomial g =
          Polynomial.C (HexModArithMathlib.ZMod64.toZMod (g.coeff 0)) := by
      ext n
      cases n with
      | zero =>
          simp [HexBerlekampMathlib.coeff_toMathlibPolynomial]
      | succ n =>
          rw [HexBerlekampMathlib.coeff_toMathlibPolynomial,
            Hex.DensePoly.coeff_eq_zero_of_size_le g (by omega)]
          rw [Polynomial.coeff_C]
          exact HexModArithMathlib.ZMod64.toZMod_zero (p := p)
    rw [hg_poly_eq]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hg_coeff_zmod_ne)
  have hmath_gcd :
      gcd
        (HexBerlekampMathlib.toMathlibPolynomial f)
        (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) =
          HexBerlekampMathlib.toMathlibPolynomial g := by
    rw [← HexBerlekampMathlib.toMathlibPolynomial_derivative f]
    rw [← HexBerlekampMathlib.toMathlibPolynomial_gcd f (Hex.DensePoly.derivative f)]
  exact (gcd_isUnit_iff_isRelPrime.mp (by
    rw [hmath_gcd]
    exact hg_poly_unit)).isCoprime

/--
Scaling a nonzero modular image to its monic representative preserves the
executable square-free gcd check used by Berlekamp.
-/
private theorem gcd_monicModularImage_derivative_eq_one
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    Hex.DensePoly.gcd (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f)) = 1 := by
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
        simpa [u] using Hex.ZMod64.inv_mul_eq_one_of_prime hp_hex hlead_ne
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
    rw [hmonic_eq, toMathlibPolynomial_scale]
    rw [Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left hC_unit
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))).mpr hcop_f
  have hmath_gcd :
      gcd
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) = 1 := by
    have hunit :
        IsUnit
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) :=
      gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
    have hnorm :
        normalize
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) =
        gcd
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
          (Polynomial.derivative
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) :=
      normalize_gcd _ _
    have hone :
        normalize
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) = 1 :=
      normalize_eq_one.mpr hunit
    simpa [hnorm] using hone
  apply HexBerlekampMathlib.fpPolyEquiv.injective
  change
    HexBerlekampMathlib.toMathlibPolynomial
        (Hex.DensePoly.gcd (Hex.monicModularImage f)
          (Hex.DensePoly.derivative (Hex.monicModularImage f))) =
      HexBerlekampMathlib.toMathlibPolynomial (1 : Hex.FpPoly p)
  rw [HexBerlekampMathlib.toMathlibPolynomial_gcd,
      HexBerlekampMathlib.toMathlibPolynomial_derivative,
      toMathlibPolynomial_one]
  exact hmath_gcd

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
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hprim :
      (HexPolyZMathlib.toPolynomial core).IsPrimitive)
    (hlc_map_ne :
      (Int.castRingHom (ZMod primeData.p))
        (HexPolyZMathlib.toPolynomial core).leadingCoeff ≠ 0)
    (hsquareFree_monic :
      Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))) = 1) :
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
  -- Apply the no-split lemma to obtain Mathlib irreducibility of the monic image.
  have hirr_monic :
      Irreducible
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))) :=
    HexBerlekampMathlib.irreducible_of_berlekampFactor_factors_length_le_one
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (Hex.monicModularImage_monic hprime_hex (Hex.ZPoly.modP primeData.p core) hzero)
      hsquareFree_monic hfactors_len_le
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
      Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))) = 1 :=
    gcd_monicModularImage_derivative_eq_one
      (p := primeData.p) (Hex.ZPoly.modP primeData.p core) hzero hsquareFree_modP
  exact squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData
    core primeData hselected hsmall hprim hlc_map_ne hsquareFree_monic

/-- The Mathlib image over `ZMod p` of the monic modular reduction selected by a
successful `choosePrimeData?` run is squarefree.

The executable `isGoodPrime` check certifies `squareFreeModP core p`
(`gcdIsUnit (gcd (modP core) (modP core)') = true`);
`gcd_monicModularImage_derivative_eq_one` lifts this to the monic image's
coprimality with its derivative, which is exactly `Polynomial.Separable` over the
field `ZMod p`, hence `Squarefree`.  This is the modular squarefreeness datum the
mod-`p` disjointness lemma `modPFactorSubset_disjoint_of_not_associated` needs but
`modPSubsetPartitionHypotheses_of_choosePrimeData` fills with `trivial`. -/
theorem squarefree_toMathlibPolynomial_monicModPImage_of_choosePrimeData
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData) :
    Squarefree
      (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))) := by
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
      Hex.DensePoly.gcd
        (@Hex.monicModularImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))
        (Hex.DensePoly.derivative
          (@Hex.monicModularImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))) = 1 :=
    gcd_monicModularImage_derivative_eq_one
      (p := primeData.p) (Hex.ZPoly.modP primeData.p core) hzero hsquareFree_modP
  have hsep :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial
            (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))) :=
    HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) hsquareFree_monic
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
theorem modPFactorSubset_disjoint_of_choosePrimeData
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (hselected : Hex.choosePrimeData? core = some primeData)
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
  have hprime_hex : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  have hcore_modP_nz :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  exact modPFactorSubset_disjoint_of_not_associated hprime_hex
    (modPSubsetPartitionHypotheses_of_choosePrimeData core primeData hselected)
    hcore_modP_nz
    (squarefree_toMathlibPolynomial_monicModPImage_of_choosePrimeData core primeData
      hselected)
    hf_irr hf_dvd hg_irr hg_dvd hS hT hnotassoc

/-! ### Base discharges for the small-mod singleton branch

The two lemmas below feed `squareFreeCore_irreducible_of_small_mod_singleton`
its `hprim` and `hlc_map_ne` side-conditions from the executable invariants
that `normalizeForFactor` and `choosePrimeData?` already maintain. They
form the base lemmas for the small-mod singleton arm of the HO-1 capstone
`factor_irreducible_of_nonUnit` (issue #4170, decomposed in #4544).
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
    simpa [hG_size_eq] using h
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
(`HexBerlekampZassenhausMathlib/Basic.lean`); the outer-bound
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

/-! ### Rational repeatedPart-divides-squareFreeCore-power transport (#4675)

Base helpers consumed by the integer Gauss descent of #4618 (via
the sibling #4676). The abstract Polynomial-ℚ structure factoring out of
the executable rational decomposition: `divRadical` divides a power of
`radical` (in any UFD), `toPolynomial` of a coefficient-scaled
`DensePoly` is a constant multiplication, and the char-0 gcd-divRadical
identity composes with the radical-power inequality to produce
`R ∣ S ^ N` from associatedness with `gcd(P, P')` and a factorisation
`P ~ S * R`.

The specialisation to `(normalizeForFactor f).{repeatedPart, squareFreeCore}`
remains in a successor sub-issue. -/

/--
Local UFD helper: in a Euclidean-domain UFD with a normalization monoid,
the `divRadical` of a nonzero element divides some power of its
`radical`.

Proof: `exists_squarefree_dvd_pow_of_ne_zero` provides a squarefree `y`
with `y ∣ a` and `a ∣ y ^ n`. Squarefree elements are radical, so
`y ∣ radical y`, and `y ∣ a` lifts to `radical y ∣ radical a`; hence
`y ∣ radical a` and `y ^ n ∣ (radical a) ^ n`. Transitivity through
`divRadical_dvd_self` gives `divRadical a ∣ (radical a) ^ n`.
-/
private theorem divRadical_dvd_radical_pow_of_ne_zero
    {E : Type*} [EuclideanDomain E] [NormalizationMonoid E]
    [UniqueFactorizationMonoid E] {a : E} (ha : a ≠ 0) :
    ∃ N : Nat, EuclideanDomain.divRadical a ∣
      (UniqueFactorizationMonoid.radical a) ^ N := by
  obtain ⟨y, n, hy_sf, hy_dvd, ha_dvd⟩ :=
    exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨n, ?_⟩
  have hy_ne : y ≠ 0 := hy_sf.ne_zero
  have hy_dvd_rad : y ∣ UniqueFactorizationMonoid.radical y :=
    hy_sf.isRadical.dvd_radical hy_ne
  have hrad_dvd_rad :
      UniqueFactorizationMonoid.radical y ∣
        UniqueFactorizationMonoid.radical a :=
    UniqueFactorizationMonoid.radical_dvd_radical hy_dvd ha
  have hy_dvd_rad_a : y ∣ UniqueFactorizationMonoid.radical a :=
    hy_dvd_rad.trans hrad_dvd_rad
  have hyn_dvd :
      y ^ n ∣ (UniqueFactorizationMonoid.radical a) ^ n :=
    pow_dvd_pow_of_dvd hy_dvd_rad_a n
  exact (EuclideanDomain.divRadical_dvd_self a).trans
    (ha_dvd.trans hyn_dvd)

/--
`HexPolyMathlib.toPolynomial` intertwines coefficient scaling with Mathlib's
constant-multiplication, for any semiring base. This is the rational analogue
of the integer-side `Hex.ZPoly.C_mul_eq_scale` used to lift the executable
`DensePoly.scale` to a `Polynomial.C` multiplication, without needing a
`GcdMonoid` or `Semiring` instance beyond what `toPolynomial` already requires.
-/
private theorem toPolynomial_scale {R : Type*} [CommSemiring R] [DecidableEq R]
    (c : R) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p) =
      Polynomial.C c * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial,
    Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, HexPolyMathlib.coeff_toPolynomial]

/--
The abstract divisibility step for #4675: given a nonzero `Polynomial K`
(with `K` a characteristic-zero field) decomposed as `P ~ S * R` where
`R` is associated to the executable gcd `gcd P P'`, the polynomial `R`
divides some power of `S`.

This packages the char-0 gcd-divRadical identity together with the UFD
helper `divRadical_dvd_radical_pow_of_ne_zero` and the `Associated.of_mul_right`
cancellation step.
-/
private theorem rp_dvd_sf_pow_of_associated
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    {P R S : Polynomial K} (hP : P ≠ 0)
    (hR_gcd : Associated R
      (EuclideanDomain.gcd P (Polynomial.derivative P)))
    (hP_eq : Associated P (S * R)) :
    ∃ N : Nat, R ∣ S ^ N := by
  have hR_divR : Associated R (EuclideanDomain.divRadical P) :=
    hR_gcd.trans (Polynomial.gcd_derivative_associated_divRadical_of_charZero P)
  obtain ⟨N, hdivR_pow⟩ := divRadical_dvd_radical_pow_of_ne_zero hP
  have h1 : Associated P (S * EuclideanDomain.divRadical P) :=
    hP_eq.trans (Associated.mul_left S hR_divR)
  have h2 : Associated (UniqueFactorizationMonoid.radical P *
      EuclideanDomain.divRadical P) (S * EuclideanDomain.divRadical P) := by
    have hrad : UniqueFactorizationMonoid.radical P *
        EuclideanDomain.divRadical P = P :=
      EuclideanDomain.radical_mul_divRadical
    rw [hrad]; exact h1
  have hdivR_ne : EuclideanDomain.divRadical P ≠ 0 :=
    EuclideanDomain.divRadical_ne_zero hP
  have hS_rad : Associated (UniqueFactorizationMonoid.radical P) S :=
    Associated.of_mul_right h2 Associated.rfl hdivR_ne
  refine ⟨N, ?_⟩
  exact hR_divR.dvd.trans (hdivR_pow.trans (pow_dvd_pow_of_dvd hS_rad.dvd N))

/--
Identify `(primitiveSquareFreeDecomposition p).repeatedPart = 1` when the
executable rational derivative vanishes (Case B of the executable structure).
Isolated as a private helper so the unfold-then-case-split block lives
behind a clean interface and avoids `whnf` heartbeat issues in callers.
-/
private theorem psd_repeatedPart_eq_one_of_derivative_isZero
    (p : Hex.ZPoly)
    (hpp_isZero_false : (Hex.ZPoly.primitivePart p).isZero = false)
    (hderiv : (Hex.DensePoly.derivative
      (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))).isZero = true) :
    (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart = 1 := by
  unfold Hex.ZPoly.primitiveSquareFreeDecomposition
  simp [hpp_isZero_false, hderiv]

/--
Identify `(primitiveSquareFreeDecomposition p).repeatedPart` as the
rational primitive part of `gcd ratPrimitive ratPrimitive.derivative`
in Case C (executable rational derivative nonzero). Private helper
mirroring `psd_repeatedPart_eq_one_of_derivative_isZero`.
-/
private theorem psd_repeatedPart_eq_ratPolyPrimitivePart_gcd_of_derivative_not_isZero
    (p : Hex.ZPoly)
    (hpp_isZero_false : (Hex.ZPoly.primitivePart p).isZero = false)
    (hderiv : (Hex.DensePoly.derivative
      (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))).isZero = false) :
    (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart =
      Hex.ZPoly.ratPolyPrimitivePart
        (Hex.DensePoly.gcd
          (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))
          (Hex.DensePoly.derivative
            (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p)))) := by
  unfold Hex.ZPoly.primitiveSquareFreeDecomposition
  simp [hpp_isZero_false, hderiv]

/--
Specialisation of the abstract `rp_dvd_sf_pow_of_associated` step to the
executable `normalizeForFactor` surface, transported to `Polynomial ℚ`
via `HexPolyZMathlib.toPolynomial` and `Polynomial.map (Int.castRingHom ℚ)`.

This is the rational-side divisibility theorem consumed by the integer
Gauss descent of #4618 (via sibling #4676) and ultimately by the
exponent-extraction step of #4611.
-/
theorem normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∃ N : Nat,
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).repeatedPart).map (Int.castRingHom ℚ) ∣
      ((HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).map (Int.castRingHom ℚ)) ^ N := by
  -- The executable `normalizeForFactor` peels off the `X^k` prefix from the
  -- primitive part of `f` and feeds the result through
  -- `primitiveSquareFreeDecomposition`. We name the resulting primitive
  -- nonzero polynomial `core` and reduce to the `core`-level statement.
  set core : Hex.ZPoly := (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
    with hcore_def
  have hcore_ne : core ≠ 0 := Hex.extractXPower_core_ne_zero_of_ne_zero f hf
  have hcore_prim : Hex.ZPoly.Primitive core :=
    Hex.extractXPower_core_primitive_of_ne_zero f hf
  have hpp : Hex.ZPoly.primitivePart core = core :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive _ hcore_prim
  -- Rewrite the executable goal in the `core`-level form.
  have hsf_eq : (Hex.normalizeForFactor f).squareFreeCore =
      (Hex.ZPoly.primitiveSquareFreeDecomposition core).squareFreeCore := rfl
  have hrp_eq : (Hex.normalizeForFactor f).repeatedPart =
      (Hex.ZPoly.primitiveSquareFreeDecomposition core).repeatedPart := rfl
  rw [hsf_eq, hrp_eq]
  -- Move the goal into the rational view through the integer-to-rational lift.
  rw [← toPolynomial_toRatPoly_eq_map_intCast,
      ← toPolynomial_toRatPoly_eq_map_intCast]
  -- Name the rational images.
  set sf : Hex.ZPoly := (Hex.ZPoly.primitiveSquareFreeDecomposition core).squareFreeCore
    with hsf_def
  set rp : Hex.ZPoly := (Hex.ZPoly.primitiveSquareFreeDecomposition core).repeatedPart
    with hrp_def
  set P : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly core) with hP_def
  set R : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly rp) with hR_def
  set S : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly sf) with hS_def
  -- `toRatPoly core ≠ 0` (inline analogue of the private `toRatPoly_ne_zero_of_ne_zero`).
  have hrat_ne : Hex.ZPoly.toRatPoly core ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply Hex.DensePoly.ext_coeff
    intro n
    have hcoeff : ((core.coeff n : Int) : Rat) = 0 := by
      rw [← Hex.ZPoly.coeff_toRatPoly, hzero, Hex.DensePoly.coeff_zero]
    rw [Hex.DensePoly.coeff_zero]
    exact_mod_cast hcoeff
  -- `P ≠ 0`: route through `Polynomial.map_ne_zero_iff` on the integer-side lift.
  have hP_ne : P ≠ 0 := by
    rw [hP_def, toPolynomial_toRatPoly_eq_map_intCast]
    refine (Polynomial.map_ne_zero_iff Int.cast_injective).mpr ?_
    intro h
    apply hcore_ne
    exact HexPolyZMathlib.equiv.injective (by simpa using h)
  -- Apply the rational reassembly to extract `unit` with
  -- `toRatPoly core = scale unit (toRatPoly sf * toRatPoly rp)`.
  rcases Hex.ZPoly.primitiveSquareFreeDecomposition_reassembly_over_rat core with
    ⟨unit, hunit⟩
  rw [Hex.ZPoly.primitiveSquareFreeDecomposition_primitive, hpp] at hunit
  -- `unit ≠ 0` (else `scale unit _ = 0`).
  have hunit_ne : unit ≠ 0 := by
    intro huzero
    apply hrat_ne
    rw [hunit, huzero]
    apply Hex.DensePoly.ext_coeff
    intro n
    rw [Hex.DensePoly.coeff_scale (R := Rat) 0 _ n (mul_zero 0),
        Hex.DensePoly.coeff_zero, zero_mul]
  -- `P = C unit * (S * R)`.
  have hP_factor : P = Polynomial.C unit * (S * R) := by
    rw [hP_def, hunit, toPolynomial_scale, HexPolyMathlib.toPolynomial_mul]
  have hCunit_unit : IsUnit (Polynomial.C unit) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hunit_ne)
  -- `Associated P (S * R)`.
  have hP_assoc : Associated P (S * R) := by
    rw [hP_factor]
    exact associated_unit_mul_left (S * R) (Polynomial.C unit) hCunit_unit
  -- `(primitivePart core).isZero = false` from `core ≠ 0` and `primitivePart core = core`.
  have hpp_isZero_false : (Hex.ZPoly.primitivePart core).isZero = false :=
    (Hex.DensePoly.isZero_eq_false_iff _).mpr
      (Hex.ZPoly.size_pos_of_ne_zero _ (by rw [hpp]; exact hcore_ne))
  -- Case-split on whether the rational derivative vanishes.
  by_cases hderiv :
      (Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).isZero = true
  · -- Case B: derivative vanishes, so `rp = 1` and `P` is a constant unit.
    have hrp_one : rp = 1 :=
      psd_repeatedPart_eq_one_of_derivative_isZero core hpp_isZero_false hderiv
    -- `R = 1` by transport.
    have hR_one : R = 1 := by
      rw [hR_def, hrp_one, Hex.ZPoly.toRatPoly_one]
      show HexPolyMathlib.toPolynomial (Hex.DensePoly.C (1 : Rat)) = 1
      rw [HexPolyMathlib.toPolynomial_C]
      exact map_one Polynomial.C
    -- `(toRatPoly core).derivative = 0` from the `isZero` flag (using `primitivePart core = core`).
    have hderiv_pp : Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core)) = 0 := by
      have hsize : (Hex.DensePoly.derivative
          (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).size = 0 :=
        (Hex.DensePoly.isZero_eq_true_iff _).mp hderiv
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    have hderiv_core_zero : Hex.DensePoly.derivative (Hex.ZPoly.toRatPoly core) = 0 := by
      rw [← hpp]; exact hderiv_pp
    -- `P.derivative = 0`.
    have hPderiv_zero : Polynomial.derivative P = 0 := by
      rw [hP_def, ← toPolynomial_derivative, hderiv_core_zero, HexPolyMathlib.toPolynomial_zero]
    -- `P` is a unit: derivative zero + char zero + nonzero ⇒ nonzero constant.
    have hP_isUnit : IsUnit P := by
      have hP_eq_C : P = Polynomial.C (P.coeff 0) := eq_C_of_derivative_eq_zero hPderiv_zero
      have hcoeff_ne : P.coeff 0 ≠ 0 := by
        intro h
        apply hP_ne
        rw [hP_eq_C, h, map_zero]
      rw [hP_eq_C]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff_ne)
    -- `R = 1 ~ gcd P 0 = P` (using `gcd_zero_right` and `IsUnit P`).
    have hR_gcd : Associated R (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      rw [hR_one, hPderiv_zero, EuclideanDomain.gcd_zero_right]
      exact (associated_one_iff_isUnit.mpr hP_isUnit).symm
    exact rp_dvd_sf_pow_of_associated hP_ne hR_gcd hP_assoc
  · -- Case C: derivative is nonzero; `rp = ratPolyPrimitivePart (gcd ratPrim ratPrim.derivative)`.
    have hderiv_false : (Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).isZero = false :=
      Bool.eq_false_iff.mpr hderiv
    -- Identify `rp` via the case-C helper. Work with `primitivePart core`-shaped terms.
    have hrp_pp_eq : rp =
        Hex.ZPoly.ratPolyPrimitivePart
          (Hex.DensePoly.gcd
            (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))
            (Hex.DensePoly.derivative
              (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core)))) :=
      psd_repeatedPart_eq_ratPolyPrimitivePart_gcd_of_derivative_not_isZero
        core hpp_isZero_false hderiv_false
    -- Use `hpp` to identify with `toRatPoly core`.
    set ratPrim : Hex.DensePoly Rat := Hex.ZPoly.toRatPoly core with hratPrim_def
    set der : Hex.DensePoly Rat := Hex.DensePoly.derivative ratPrim with hder_def
    set repeatedRat : Hex.DensePoly Rat := Hex.DensePoly.gcd ratPrim der with hrepeatedRat_def
    have hrp_eq_repeatedRat : rp = Hex.ZPoly.ratPolyPrimitivePart repeatedRat := by
      rw [hrp_pp_eq]
      congr 1
      rw [hpp]
    rcases Hex.ZPoly.ratPolyPrimitivePart_rational_associate repeatedRat with ⟨w, hw⟩
    rw [← hrp_eq_repeatedRat] at hw
    -- `repeatedRat ≠ 0` because `repeatedRat ∣ ratPrim` and `ratPrim ≠ 0`.
    have hrepeatedRat_ne : repeatedRat ≠ 0 := by
      intro hzero
      have hdvd : repeatedRat ∣ ratPrim := Hex.DensePoly.gcd_dvd_left ratPrim der
      rw [hzero] at hdvd
      rcases hdvd with ⟨r, hr⟩
      apply hrat_ne
      change ratPrim = 0
      rw [hr]
      exact Hex.DensePoly.zero_mul _
    -- `w ≠ 0`.
    have hw_ne : w ≠ 0 := by
      intro hzero
      apply hrepeatedRat_ne
      rw [hw, hzero]
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Rat) 0 _ n (mul_zero 0),
          Hex.DensePoly.coeff_zero, zero_mul]
    have hCw_unit : IsUnit (Polynomial.C w) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr hw_ne)
    -- `toPolynomial repeatedRat ~ gcd P P.derivative`.
    have hToPoly_ratPrim : HexPolyMathlib.toPolynomial ratPrim = P := by rw [hP_def]
    have hToPoly_der : HexPolyMathlib.toPolynomial der = Polynomial.derivative P := by
      rw [hder_def, toPolynomial_derivative, hToPoly_ratPrim]
    have hgcd_assoc :
        Associated (HexPolyMathlib.toPolynomial repeatedRat)
          (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      have := HexPolyMathlib.toPolynomial_gcd_associated ratPrim der
      rw [hToPoly_ratPrim, hToPoly_der] at this
      exact this
    -- `toPolynomial repeatedRat = C w * R`.
    have hToPoly_repeatedRat : HexPolyMathlib.toPolynomial repeatedRat = Polynomial.C w * R := by
      rw [hw, toPolynomial_scale, ← hR_def]
    -- `R ~ gcd P P.derivative` by cancelling `C w`.
    have hR_gcd : Associated R (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      have hCwR_assoc : Associated (Polynomial.C w * R)
          (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
        rw [← hToPoly_repeatedRat]; exact hgcd_assoc
      exact (associated_unit_mul_left R (Polynomial.C w) hCw_unit).symm.trans hCwR_assoc
    exact rp_dvd_sf_pow_of_associated hP_ne hR_gcd hP_assoc

/--
The repeated part of `normalizeForFactor f` divides a power of the
square-free core over integer polynomials.

This is the integer Gauss-descent form of
`normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow`.
-/
theorem normalizeForFactor_repeatedPart_toPolynomial_dvd_squareFreeCore_pow
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∃ N : Nat,
      HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart ∣
      (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) ^ N := by
  obtain ⟨N, hN⟩ :=
    normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow f hf
  refine ⟨N, ?_⟩
  refine (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart)
    ((HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) ^ N)
    (normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf)
    (isPrimitive_pow
      (normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive f hf) N)).mpr ?_
  simpa using hN

/--
Every normalized irreducible factor of the repeated part is represented,
up to association in `Polynomial ℤ`, by one of the supplied irreducible
core factors.

This is the normalized-factor support step consumed by the successor
exponent-list construction for
`normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover`.
It combines the landed repeated-part power-divisibility theorem with the
`polyProduct_toPolynomial` identification for the supplied `coreFactors`.
-/
theorem normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore) :
    ∀ r ∈ UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart),
      ∃ q ∈ coreFactors.toList,
        Associated r (HexPolyZMathlib.toPolynomial q) := by
  intro r hr
  let R : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart
  let S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore
  have hr_irr : Irreducible r :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
  have hr_prime : Prime r :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hr_irr
  have hr_dvd_R : r ∣ R :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hr
  obtain ⟨N, hR_dvd_pow⟩ :=
    normalizeForFactor_repeatedPart_toPolynomial_dvd_squareFreeCore_pow f hf
  have hr_dvd_pow : r ∣ S ^ N := dvd_trans hr_dvd_R hR_dvd_pow
  have hr_dvd_S : r ∣ S := hr_prime.dvd_of_dvd_pow hr_dvd_pow
  have hS_prod :
      S = (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod := by
    dsimp [S]
    rw [← hprod, polyProduct_toPolynomial]
  have hr_dvd_prod :
      r ∣ (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod := by
    rwa [← hS_prod]
  obtain ⟨qPoly, hqPoly_mem, hr_dvd_qPoly⟩ :=
    (Prime.dvd_prod_iff hr_prime).mp hr_dvd_prod
  rcases List.mem_map.mp hqPoly_mem with ⟨q, hq_mem, hqPoly_eq⟩
  refine ⟨q, hq_mem, ?_⟩
  subst qPoly
  have hq_irr_poly : Irreducible (HexPolyZMathlib.toPolynomial q) :=
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q).mp (hirr q hq_mem)
  exact hr_irr.associated_of_dvd hq_irr_poly hr_dvd_qPoly

/-- Local copy of the integer-polynomial identification for the executable unit. -/
private theorem toPolynomial_one_zpoly :
    HexPolyZMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
  show HexPolyZMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
  rw [HexPolyZMathlib.toPolynomial_C]
  simp

/--
The executable fold of packed powers agrees with the corresponding
`Polynomial ℤ` product after transporting every factor through
`toPolynomial`.

This is the transport half of the #4611 exponent-decomposition theorem:
once the UFD argument supplies the polynomial-level powers in core-factor
order, this lemma converts that certificate back to the exact `ZPoly` fold
shape expected by the Mathlib-free expansion helper.
-/
private theorem toPolynomial_factorPower_foldl_aux
    (entries : List (Hex.ZPoly × Nat)) (init : Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial
        ((entries.map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) init) =
      HexPolyZMathlib.toPolynomial init *
        (entries.map
          (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
  induction entries generalizing init with
  | nil =>
      simp
  | cons qe entries ih =>
      rw [List.map_cons, List.foldl_cons, ih, HexPolyZMathlib.toPolynomial_mul,
        factorPower_toPolynomial]
      simp [List.prod_cons, mul_assoc]

/--
The ordered executable product of public `Hex.Factorization.factorPower`
entries agrees with the ordered `Polynomial ℤ` product of transported powers.

This is the product lemma consumed by repeated-part exponent decompositions
before invoking the Mathlib-free expansion helper.
-/
theorem toPolynomial_factorPower_foldl
    (entries : List (Hex.ZPoly × Nat)) :
    HexPolyZMathlib.toPolynomial
        ((entries.map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1) =
      (entries.map
        (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
  rw [toPolynomial_factorPower_foldl_aux, toPolynomial_one_zpoly, one_mul]

/--
Polynomial-to-executable lemma for the #4611 repeated-part power
decomposition.

The remaining mathematical side condition is the polynomial-level exact
decomposition `hpoly_decomp`.  In downstream use this is the part supplied by
the normalized-factor/UFD exponent extraction: #4745 already gives support of
the repeated part inside the supplied core factors, and the caller must still
show that the chosen exponents multiply to the transported repeated part.
This theorem then converts that certificate into the exact executable
`Factorization.factorPower` fold consumed by
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`.
-/
theorem normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover
    (f : Hex.ZPoly) (_hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (_hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (_hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hpoly_decomp :
      HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod) :
    ∃ exponents : List Nat,
      exponents.length = coreFactors.size ∧
      (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  refine ⟨exponents, hlen, ?_⟩
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply]
  rw [toPolynomial_factorPower_foldl]
  exact hpoly_decomp

/-- Self-zip distributes through `List.map` on the second component. -/
private theorem zip_map_self {α β : Type*} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map (fun x => (x, f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zip_cons_cons, ih]

/--
If a list product in a commutative monoid with zero is squarefree and every
element of the list is irreducible, the list is `Nodup`.
-/
private theorem List.nodup_of_prod_squarefree
    {α : Type*} [CommMonoidWithZero α] [DecidableEq α]
    (l : List α) (hirr : ∀ a ∈ l, Irreducible a)
    (hsq : Squarefree l.prod) :
    l.Nodup := by
  rw [← Multiset.coe_nodup, Multiset.nodup_iff_count_le_one]
  intro p
  by_contra hcontra
  have hcount : 1 < Multiset.count p (l : Multiset α) := Nat.lt_of_not_ge hcontra
  have hp_mem : p ∈ l := by
    rw [← Multiset.mem_coe]
    exact Multiset.count_pos.mp (by omega)
  have hp_irr : Irreducible p := hirr p hp_mem
  -- `p * p ∣ l.prod`: peel two occurrences of `p` from the list.
  have hp_mul_dvd : p * p ∣ l.prod := by
    have hle : Multiset.replicate 2 p ≤ (l : Multiset α) := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x = p
      · subst hx
        rw [Multiset.count_replicate_self]
        omega
      · rw [Multiset.count_replicate, if_neg (Ne.symm hx)]
        exact Nat.zero_le _
    have hdvd_prod := Multiset.prod_dvd_prod_of_le hle
    rw [Multiset.prod_replicate, Multiset.prod_coe] at hdvd_prod
    rw [sq] at hdvd_prod
    exact hdvd_prod
  exact hp_irr.not_isUnit (hsq _ hp_mul_dvd)

/--
**#4611/#4746 capstone — `Factorization.factorPower` decomposition of the
repeated part.**

Every irreducible cover of `(Hex.normalizeForFactor f).squareFreeCore` lifts
to an exponent list whose `Hex.Factorization.factorPower`-fold reconstructs
`(Hex.normalizeForFactor f).repeatedPart` in `Hex.ZPoly`. This is the form
consumed by the public Mathlib-free expansion wrapper
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.

The proof composes three landed base lemmas:

* `normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors`
  (#4749), which guarantees every normalized factor of the repeated part is
  Associated to one of the supplied core factors;
* the normalize identifications
  `normalizeForFactor_repeatedPart_toPolynomial_normalize` and
  `HexBerlekampZassenhausMathlib.normalize_toPolynomial_of_normalizeFactorSign_id`
  (#4758), which align the repeated part and each supplied core factor with
  the `normalize`-fixed UFD canonical form in `Polynomial ℤ`;
* `normalizeForFactor_squareFreeCore_toPolynomial_squarefree`, which (via the
  local `List.nodup_of_prod_squarefree` helper) makes the transported
  core-factor list pairwise distinct so that exponents per position are
  unambiguous, and Mathlib's `Finset.prod_multiset_count_of_subset`
  re-expresses `(normalizedFactors R).prod` as a finset-product over the
  list's `toFinset`.

The constructed exponents are
`exponents[i] = Multiset.count (toPolynomial coreFactors[i]) (normalizedFactors R)`
where `R = toPolynomial (normalizeForFactor f).repeatedPart`.

The `hnorm` hypothesis (`Hex.normalizeFactorSign q = q` for each supplied core
factor) is downstream-friendly: every arm discharger reaches this point after
`multifactorLiftQuadratic`, where the lifted factors are monic, so
`normalizeFactorSign q = q` is immediate from monicity (`leadingCoeff = 1`).
-/
theorem normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q) :
    ∃ exponents : List Nat,
      exponents.length = coreFactors.size ∧
      (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  classical
  -- Abbreviations.
  set R : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart with hR_def
  set S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore with hS_def
  -- Side facts on `R`.
  have hR_norm : normalize R = R :=
    normalizeForFactor_repeatedPart_toPolynomial_normalize f hf
  have hR_prim : R.IsPrimitive :=
    normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
  have hR_ne_zero : R ≠ 0 := hR_prim.ne_zero
  -- Side facts on each `HexPolyZMathlib.toPolynomial q` for `q ∈ coreFactors`.
  have hPq_irr : ∀ q ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial q) := fun q hq =>
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q).mp (hirr q hq)
  have hPq_norm : ∀ q ∈ coreFactors.toList,
      normalize (HexPolyZMathlib.toPolynomial q) = HexPolyZMathlib.toPolynomial q :=
    fun q hq => normalize_toPolynomial_of_normalizeFactorSign_id
      (hirr q hq).not_zero (hnorm q hq)
  -- Translate the executable product `polyProduct` into a `List.prod` in
  -- `Polynomial ℤ`.
  have hS_eq : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod = S := by
    show _ = HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore
    rw [← hprod, polyProduct_toPolynomial]
  have hS_sqfree : Squarefree S :=
    normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf
  have hS_ne_zero : S ≠ 0 := hS_sqfree.ne_zero
  -- The transported core-factor list is `Nodup` (every duplicate would let a
  -- square of an irreducible divide the squarefree `S`).
  have hPq_list_nodup : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).Nodup := by
    apply List.nodup_of_prod_squarefree
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hPq_irr q hq
    · rw [hS_eq]; exact hS_sqfree
  -- Every normalized factor of `R` is one of the transported core factors.
  have hcover := normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors
    f hf coreFactors hirr hprod
  have hsubset : ∀ r ∈ UniqueFactorizationMonoid.normalizedFactors R,
      r ∈ (coreFactors.toList.map HexPolyZMathlib.toPolynomial : List _).toFinset := by
    intro r hr
    obtain ⟨q, hq, hassoc⟩ := hcover r hr
    have hr_norm : normalize r = r :=
      UniqueFactorizationMonoid.normalize_normalized_factor r hr
    have hr_eq : r = HexPolyZMathlib.toPolynomial q := by
      have hassoc_norm : normalize r = normalize (HexPolyZMathlib.toPolynomial q) :=
        normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr hassoc)
      rw [hr_norm, hPq_norm q hq] at hassoc_norm
      exact hassoc_norm
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, hr_eq.symm⟩
  -- Define the exponent list as a count over the multiset of normalized factors.
  set exponents : List Nat :=
    coreFactors.toList.map (fun q =>
      Multiset.count (HexPolyZMathlib.toPolynomial q)
        (UniqueFactorizationMonoid.normalizedFactors R)) with hexponents_def
  have hlen : exponents.length = coreFactors.size := by
    simp [exponents]
  -- Apply the existing `_isPow` wrapper.
  refine normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover
    f hf coreFactors hirr hprod exponents hlen ?_
  -- Fold the unfolded `toPolynomial …` back into `R` so subsequent rewrites match.
  change R = _
  -- The RHS reduces to a `List.map` over `coreFactors.toList.map toPolynomial`
  -- whose entries are `p ^ count p (normalizedFactors R)`. Using `Nodup`, that
  -- list-prod equals a `Finset.prod` over the `toFinset`; `R = (normalizedFactors R).prod`
  -- closes the goal via `prod_multiset_count_of_subset`.
  have hRHS_eq :
      ((coreFactors.toList.zip exponents).map
        (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod
      = ((coreFactors.toList.map HexPolyZMathlib.toPolynomial).map
          (fun p => p ^ Multiset.count p
            (UniqueFactorizationMonoid.normalizedFactors R))).prod := by
    rw [show coreFactors.toList.zip exponents
          = coreFactors.toList.map (fun q => (q,
              Multiset.count (HexPolyZMathlib.toPolynomial q)
                (UniqueFactorizationMonoid.normalizedFactors R)))
        from zip_map_self _ _]
    simp [List.map_map, Function.comp_def]
  rw [hRHS_eq]
  rw [← List.prod_toFinset _ hPq_list_nodup]
  -- Goal: R = ∏ p ∈ (coreFactors.toList.map toPoly).toFinset, p ^ count p (normalizedFactors R)
  have hR_prod_norm :
      (UniqueFactorizationMonoid.normalizedFactors R).prod = R := by
    have := UniqueFactorizationMonoid.prod_normalizedFactors_eq hR_ne_zero
    rw [hR_norm] at this
    exact this
  conv_lhs => rw [← hR_prod_norm]
  -- Goal: (normalizedFactors R).prod = ∏ p ∈ list.toFinset, p ^ count p (normalizedFactors R)
  exact Finset.prod_multiset_count_of_subset
    (UniqueFactorizationMonoid.normalizedFactors R)
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).toFinset
    (by intro r hr; rw [Multiset.mem_toFinset] at hr; exact hsubset r hr)

/-- **HO-1 base task — no-tail-divisibility for an irreducible cover of the
square-free core.**

Given an irreducible cover `coreFactors` of `(Hex.normalizeForFactor f).squareFreeCore`
and any exponent list of matching length, splitting the zipped list
`coreFactors.toList.zip exponents` at any position `(pre, (q, e), suf)` yields a
suffix whose `factorPower`-fold product is not divisible by `q`.

This is the list-shaped generalisation of
`Hex.irreducible_not_dvd_one` (which handles the singleton-suffix case where
the product collapses to `1`) and is the precondition consumed by the
exhaustive arm of
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.

The proof transports both `q` and the suffix product to `Polynomial ℤ` through
`HexPolyZMathlib.equiv`, uses the squarefree square-free core to obtain
`Nodup` of the transported core-factor list, and finishes with a UFD
prime-divides-product argument: `toPolynomial q` is prime in `Polynomial ℤ`,
so any divisor witness would force `q` to coincide with some entry in `suf`
(by `Associated` ⟹ `normalize`-fixed equality, then injectivity), contradicting
`Nodup`. -/
theorem factorPower_cover_not_dvd_tail_of_irreducible_squarefree
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size) :
    ∀ pre q e suf,
      coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
      ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
              Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  classical
  intro pre q e suf hsplit hdvd
  -- Transported square-free core and its squarefreeness.
  set S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore with hS_def
  have hS_sqfree : Squarefree S :=
    normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf
  -- Transported core-factor list product equals `S`.
  have hS_eq : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod = S := by
    show _ = HexPolyZMathlib.toPolynomial _
    rw [← hprod, polyProduct_toPolynomial]
  -- Each transported core factor is irreducible.
  have hPq_irr : ∀ q' ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial q') := fun q' hq' =>
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q').mp (hirr q' hq')
  -- Each transported core factor is `normalize`-fixed.
  have hPq_norm : ∀ q' ∈ coreFactors.toList,
      normalize (HexPolyZMathlib.toPolynomial q') = HexPolyZMathlib.toPolynomial q' :=
    fun q' hq' => normalize_toPolynomial_of_normalizeFactorSign_id
      (hirr q' hq').not_zero (hnorm q' hq')
  -- Transported core-factor list is `Nodup` (squarefree product + irreducible entries).
  have hPq_list_nodup :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).Nodup := by
    apply List.nodup_of_prod_squarefree
    · intro p hp
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hp
      exact hPq_irr q' hq'
    · rw [hS_eq]; exact hS_sqfree
  -- Original core-factor list is `Nodup` (pulls back through injective `toPolynomial`).
  have hcore_nodup : coreFactors.toList.Nodup :=
    List.Nodup.of_map HexPolyZMathlib.toPolynomial hPq_list_nodup
  -- The zip's first-projection equals `coreFactors.toList` (lengths match).
  have hzip_fst :
      (coreFactors.toList.zip exponents).map Prod.fst = coreFactors.toList := by
    apply List.map_fst_zip
    rw [hlen]; simp
  -- Apply that to both sides of `hsplit`.
  have hcore_split :
      coreFactors.toList = pre.map Prod.fst ++ q :: suf.map Prod.fst := by
    have := congrArg (List.map Prod.fst) hsplit
    rw [hzip_fst] at this
    simpa using this
  -- `q` does not occur in `suf.map Prod.fst` (Nodup).
  have hq_not_in_suf : ∀ qe ∈ suf, q ≠ qe.1 := by
    intro qe hqe_mem hq_eq
    have hcore_nodup' : (pre.map Prod.fst ++ q :: suf.map Prod.fst).Nodup :=
      hcore_split ▸ hcore_nodup
    obtain ⟨_, hcons_nodup, _⟩ := (List.nodup_append).mp hcore_nodup'
    have hq_notin : q ∉ suf.map Prod.fst := (List.nodup_cons.mp hcons_nodup).1
    apply hq_notin
    rw [hq_eq]
    exact List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  -- `q` itself sits in `coreFactors.toList`.
  have hq_mem : q ∈ coreFactors.toList := by
    rw [hcore_split]
    exact List.mem_append_right _ List.mem_cons_self
  -- Transport the divisibility hypothesis to `Polynomial ℤ`.
  have htrans_dvd :
      HexPolyZMathlib.toPolynomial q ∣
        (suf.map (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
    rw [← toPolynomial_factorPower_foldl]
    rcases hdvd with ⟨w, hw⟩
    refine ⟨HexPolyZMathlib.toPolynomial w, ?_⟩
    rw [hw, HexPolyZMathlib.toPolynomial_mul]
  -- `toPolynomial q` is irreducible, hence prime in the UFD `Polynomial ℤ`.
  have hPq_irr_q : Irreducible (HexPolyZMathlib.toPolynomial q) := hPq_irr q hq_mem
  have hPq_prime : Prime (HexPolyZMathlib.toPolynomial q) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hPq_irr_q
  -- Prime divides the list product, hence divides some power-entry.
  obtain ⟨entry, hentry_mem, hPq_dvd_entry⟩ :=
    (Prime.dvd_prod_iff hPq_prime).mp htrans_dvd
  rcases List.mem_map.mp hentry_mem with ⟨qe, hqe_mem, hentry_eq⟩
  subst hentry_eq
  -- Prime dividing a power divides the base.
  have hPq_dvd_base :
      HexPolyZMathlib.toPolynomial q ∣ HexPolyZMathlib.toPolynomial qe.1 :=
    hPq_prime.dvd_of_dvd_pow hPq_dvd_entry
  -- `qe.1` is one of the core factors.
  have hqe_in_core : qe.1 ∈ coreFactors.toList := by
    rw [hcore_split]
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩))
  -- Both transported factors are irreducible; the divisibility forces them to be
  -- `Associated`.
  have hPqe_irr : Irreducible (HexPolyZMathlib.toPolynomial qe.1) :=
    hPq_irr qe.1 hqe_in_core
  have hassoc :
      Associated (HexPolyZMathlib.toPolynomial q) (HexPolyZMathlib.toPolynomial qe.1) :=
    hPq_irr_q.associated_of_dvd hPqe_irr hPq_dvd_base
  -- Both are `normalize`-fixed, so `Associated` collapses to equality.
  have hq_norm : normalize (HexPolyZMathlib.toPolynomial q) = HexPolyZMathlib.toPolynomial q :=
    hPq_norm q hq_mem
  have hqe_norm :
      normalize (HexPolyZMathlib.toPolynomial qe.1) = HexPolyZMathlib.toPolynomial qe.1 :=
    hPq_norm qe.1 hqe_in_core
  have hP_eq :
      HexPolyZMathlib.toPolynomial q = HexPolyZMathlib.toPolynomial qe.1 := by
    have hnormeq :
        normalize (HexPolyZMathlib.toPolynomial q) =
          normalize (HexPolyZMathlib.toPolynomial qe.1) :=
      normalize_eq_normalize_iff_associated.mpr hassoc
    rw [hq_norm, hqe_norm] at hnormeq
    exact hnormeq
  -- Injectivity of `toPolynomial` finishes: `q = qe.1`, contradicting `hq_not_in_suf`.
  exact hq_not_in_suf qe hqe_mem (HexPolyZMathlib.equiv.injective hP_eq)

/-- **#4808 base task — expansion-complete from an irreducible square-free
cover.**

Generic assembler for exhaustive-style core factor arrays.  Given an
irreducible factor cover of `(Hex.normalizeForFactor f).squareFreeCore`, the
repeated-part `factorPower` decomposition from
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
and the no-tail-divisibility theorem
`factorPower_cover_not_dvd_tail_of_irreducible_squarefree` supply the two
semantic hypotheses of the executable expansion helper.

The remaining `hmonic`, `hdegree`, and `hfuel` hypotheses are executable
compatibility shims required by
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.
They are intentionally explicit here so branch-specific callers can discharge
or thread them without hiding another analytic obligation. -/
theorem reassemblyExpansionComplete_of_irreducible_squarefree_cover
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (hmonic : ∀ q ∈ coreFactors.toList, Hex.DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  have hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
                Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    exact hfuel exponents hlen hdecomp
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition
    (Hex.normalizeForFactor f).repeatedPart coreFactors hmonic hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel'

/-- Non-monic `_of_pos_lc` sibling of
`reassemblyExpansionComplete_of_irreducible_squarefree_cover`: replaces the
per-factor `Monic q` premise with `0 < leadingCoeff q`, delegating to the
non-monic leaf base task
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(`HexBerlekampZassenhaus/Basic.lean`, landed in #4778). Mid-layer surface for
callers wanting to delegate to the assembler under a primitive + pos-lc
precondition; the existing quadratic-arm caller
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (below)
bypasses the mid-layer by routing through the leaf directly, but the
umbrella-internal rewiring of
`reassemblyExpansionComplete_exhaustive_of_ne_zero` consumes this sibling. -/
theorem reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  have hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
                Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    exact hfuel exponents hlen hdecomp
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart coreFactors hpos_lc hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel'

/-- **#4597 HO-1 base task — small-mod singleton arm `factorPower` shape of
the repeated part.** Singleton specialisation of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
(#4759, the final-assembly successor of the decomposed #4746): when the
normalized square-free core is itself irreducible, the repeated part is
exactly a `Hex.Factorization.factorPower` of the square-free core. The
`hnorm` precondition of the general theorem is discharged by
`Hex.squareFreeCore_normalizeFactorSign_of_ne_zero` (the normalized
square-free core has positive leading coefficient, hence its
sign-normalisation is the identity). Consumed by the public discharger
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597
deliverable 3) to dispatch the singleton expansion specialisation
`Hex.expandRepeatedPartFactorArray_pow_singleton` (#4597 deliverable 2).
Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arms tracked by #4747. -/
theorem normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore) :
    ∃ k : Nat,
      (Hex.normalizeForFactor f).repeatedPart =
        Hex.Factorization.factorPower (Hex.normalizeForFactor f).squareFreeCore k := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hirr_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.ZPoly.Irreducible q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hirr
  have hprod : Array.polyProduct (#[core] : Array Hex.ZPoly) = core :=
    Hex.ZPoly.polyProduct_singleton core
  have hnorm :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    subst hq_eq
    exact Hex.squareFreeCore_normalizeFactorSign_of_ne_zero f hf
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf #[core] hirr_arr hprod hnorm
  -- Singleton `coreFactors` collapses the exponent list to `[k]` for some `k`.
  have hsize : (#[core] : Array Hex.ZPoly).size = 1 := rfl
  rw [hsize] at hlen
  cases exponents with
  | nil => simp at hlen
  | cons k es =>
      cases es with
      | cons _ _ => simp at hlen
      | nil =>
          refine ⟨k, ?_⟩
          simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons,
            List.map_nil, List.foldl_cons, List.foldl_nil,
            Hex.ZPoly.one_mul_zpoly] at hdecomp
          exact hdecomp

/-- **#4597 HO-1 base task — small-mod singleton arm `hcomplete` discharger
(Mathlib-side, deliverable 3).** When the normalized square-free core is
itself irreducible, the singleton-core reassembly is expansion-complete:
the `repeatedPart` of `normalizeForFactor f` is exactly a
`Hex.Factorization.factorPower` of the square-free core (deliverable 1),
and that factorPower is consumed completely by
`Hex.expandRepeatedPartFactorArray` (deliverable 2). Consumed by the
small-mod singleton arm umbrella
`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`
(#4564 / PR #4581) so callers can drop the explicit `hcomplete` premise
once the eventual capstone wiring (#4170) lands.

**Base-task gap (Gap 1):** the explicit `hmonic` premise on the
square-free core mirrors the same gap labelled "Gap 1" in the exhaustive
arm umbrella `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`
(#4561). The underlying executable extraction
(`consumeExactPower_pow_mul_of_not_dvd` and the
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`
wrapper) currently requires monicness of the core factor; dropping the
hypothesis would require a non-monic divMod/exactQuotient generalisation
in `HexPolyZ/Basic.lean`. The premise is documented as an explicit shim
so downstream callers thread it consistently until the base task
lands.

Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arm tracked by #4747. -/
theorem reassemblyExpansionComplete_singleton_of_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore)
    (hmonic : Hex.DensePoly.Monic (Hex.normalizeForFactor f).squareFreeCore)
    (hdeg :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      #[(Hex.normalizeForFactor f).squareFreeCore] := by
  obtain ⟨k, hk⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
      f hf hirr
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  -- Size of `core` is at least 2 from positive degree.
  have hcore_size_ge_two : 2 ≤ core.size := by
    have hdeg_unfold : core.degree?.getD 0 =
        (if core.size = 0 then 0 else core.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : core.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg
    by_cases h : core.size = 0
    · simp [h] at hdeg
    · split at hdeg <;> omega
  -- For monic `core` with `core.size ≥ 2`, the executable `factorPower` of
  -- order `m` has size at least `m + 1`. This gives the fuel bound
  -- `k + 1 ≤ (factorPower core k).size + 1` consumed by deliverable 2.
  have hfactorPower_size_ge :
      ∀ m, m + 1 ≤ (Hex.Factorization.factorPower core m).size := by
    intro m
    induction m with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_pos : 0 < (Hex.Factorization.factorPower core n).size := by
          omega
        have hcore_pos : 0 < core.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower core n * core).size =
              (Hex.Factorization.factorPower core n).size + core.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hcore_pos
        omega
  have hfuel :
      k + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    have := hfactorPower_size_ge k
    rw [hk]
    omega
  -- Apply deliverable 2 to conclude residual = 1.
  unfold Hex.reassemblyExpansionComplete
  have hexpand :=
    Hex.expandRepeatedPartFactorArray_pow_singleton
      core k hmonic hdeg hirr (Hex.normalizeForFactor f).repeatedPart hk hfuel
  rw [hexpand]

/-- **#4956 HO-1 base task — small-mod singleton arm `hcomplete` discharger,
non-monic primitive sibling (Mathlib-side).** Companion to the monic
`reassemblyExpansionComplete_singleton_of_irreducible` above. Drops the
`hmonic` premise on the square-free core in favour of `0 < leadingCoeff core`,
producing the same `Hex.reassemblyExpansionComplete` conclusion. The proof
routes through the non-monic array-level public surface
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(`HexBerlekampZassenhaus/Basic.lean:11777`, #4778), with the
no-tail-divisibility precondition discharged by
`factorPower_cover_not_dvd_tail_of_irreducible_squarefree` (#4807).
The singleton-arm umbrella
`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`
threads `hcomplete` from the caller, so the value of this sibling is in
letting downstream dispatchers discharge `hcomplete` under a non-monic
primitive `squareFreeCore` (e.g. the `2X + 3` residual from
`(X-1)(2X+3) = 2X^2 + X - 3`). Closes the singleton-arm Gap 1 documented
on the monic sibling at the discharger layer. -/
theorem reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore)
    (hpos_lc : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore)
    (hdeg :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      #[(Hex.normalizeForFactor f).squareFreeCore] := by
  obtain ⟨k, hk⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
      f hf hirr
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  -- Size of `core` is at least 2 from positive degree (monicness-agnostic).
  have hcore_size_ge_two : 2 ≤ core.size := by
    have hdeg_unfold : core.degree?.getD 0 =
        (if core.size = 0 then 0 else core.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : core.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg
    by_cases h : core.size = 0
    · simp [h] at hdeg
    · split at hdeg <;> omega
  -- For `core.size ≥ 2`, `factorPower core m` has size at least `m + 1`
  -- (monicness-agnostic; uses `mul_size_eq_top_succ_of_nonzero`).
  have hfactorPower_size_ge :
      ∀ m, m + 1 ≤ (Hex.Factorization.factorPower core m).size := by
    intro m
    induction m with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_pos : 0 < (Hex.Factorization.factorPower core n).size := by
          omega
        have hcore_pos : 0 < core.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower core n * core).size =
              (Hex.Factorization.factorPower core n).size + core.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hcore_pos
        omega
  have hfuel :
      k + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    have := hfactorPower_size_ge k
    rw [hk]
    omega
  -- Singleton-shape preconditions for the array-level public non-monic surface.
  have hirr_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.ZPoly.Irreducible q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hirr
  have hprod : Array.polyProduct (#[core] : Array Hex.ZPoly) = core :=
    Hex.ZPoly.polyProduct_singleton core
  have hnorm :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList,
        Hex.normalizeFactorSign q = q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    subst hq_eq
    exact Hex.squareFreeCore_normalizeFactorSign_of_ne_zero f hf
  have hpos_lc_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList,
        0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hpos_lc
  have hdegree_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, 0 < q.degree?.getD 0 := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hdeg
  have hlen' :
      ([k] : List Nat).length = (#[core] : Array Hex.ZPoly).size := by
    simp
  -- No-tail-divisibility for the singleton split — discharged by the generic
  -- `factorPower_cover_not_dvd_tail_of_irreducible_squarefree` helper (#4807).
  have hnot_dvd_tail :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf #[core] hirr_arr hprod hnorm [k] hlen'
  -- `factorPower` decomposition collapses on the singleton split to `hk`.
  -- `#[core].toList.zip [k]` reduces to `[(core, k)]` by definitional
  -- computation; the foldl then collapses to `1 * factorPower core k`.
  have hdecomp :
      (Hex.normalizeForFactor f).repeatedPart =
        (((#[core] : Array Hex.ZPoly).toList.zip [k]).map
          (fun (qe : Hex.ZPoly × Nat) =>
            Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
    show (Hex.normalizeForFactor f).repeatedPart =
      1 * Hex.Factorization.factorPower core k
    rw [Hex.ZPoly.one_mul_zpoly]
    exact hk
  -- Fuel bound for the singleton zip pair `(core, k)`.
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ (#[core] : Array Hex.ZPoly).toList.zip [k] →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro qe hqe
    -- `hqe : qe ∈ [(core, k)]` reduces to `qe = (core, k)`.
    have hqe_eq : qe = (core, k) := by
      have : qe ∈ ([(core, k)] : List (Hex.ZPoly × Nat)) := hqe
      simpa using this
    rw [hqe_eq]
    exact hfuel
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart #[core] hpos_lc_arr hdegree_arr
    [k] hlen' hnot_dvd_tail hdecomp hfuel'

/-- **#4747 HO-1 base task — quadratic integer-root arm reassembly-expansion
discharger (Mathlib-side).** When the normalized square-free core
`(normalizeForFactor f).squareFreeCore` factors through the executable
`quadraticIntegerRootFactors?` short-circuit (returning `some coreFactors`),
the reassembly of the recorded core factors is expansion-complete: the
`repeatedPart` of `normalizeForFactor f` is exactly the
`Factorization.factorPower` foldl product over the core-factor / exponent
pairs supplied by #4759, and that fold is consumed completely by
`Hex.expandRepeatedPartFactorArray`. Consumed by the slow-path and fast-path
quadratic arm umbrellas
(`factor_quadratic_branch_entry_irreducible_of_quadraticRoots` #4571 and
`factor_slow_quadratic_branch_entry_irreducible_of_choosePrimeData` #4575)
so the eventual capstone wiring (#4170) can drop the explicit `hcomplete`
premise on the quadratic arms.

Composes:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` and the Mathlib-side lemma
  `zpoly_primitive_of_toPolynomial_isPrimitive` ∘
  `normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive` (#4545) —
  the squareFreeCore positive-leading-coefficient and primitivity invariants;
* `Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive` — every
  emitted core factor is irreducible under primitivity;
* `Hex.polyProduct_quadraticIntegerRootFactors?_some` (#4747 plumbing) —
  the polyProduct = squareFreeCore invariant;
* `Hex.quadraticIntegerRootFactors?_normalizeFactorSign` (#4747 plumbing) —
  the per-factor `normalizeFactorSign` identity, discharging the `hnorm`
  precondition of #4759;
* `Hex.quadraticIntegerRootFactors?_factor_size_eq_two` (#4747 plumbing) —
  every core factor has dense size two, supplying the per-factor positive
  leading coefficient and positive degree preconditions of the non-monic
  expansion-complete surface;
* `normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
  (#4759) — the structural `factorPower` decomposition of the repeated part;
* `factorPower_cover_not_dvd_tail_of_irreducible_squarefree` (#4807) — the
  per-position tail-non-divisibility certificate;
* `Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
  (#4778) — the non-monic public expansion-complete surface; the non-monic
  version is required because `quadraticIntegerRootFactors?` may emit a
  primitive non-monic residual (e.g. `2X + 3` from
  `(X-1)(2X+3) = 2X^2 + X - 3`).

Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
small-mod singleton arm `reassemblyExpansionComplete_singleton_of_irreducible`
(#4597); exhaustive arm — tracked by #4848. -/
theorem reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hquad : Hex.quadraticIntegerRootFactors?
              (Hex.normalizeForFactor f).squareFreeCore = some coreFactors) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  -- Discharge prerequisites for the squareFreeCore.
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_primitive := normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  -- Per-factor invariants from the quadratic branch.
  have hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q := fun q hq =>
    Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
      hcore_pos hcore_primitive hquad hq
  have hprod :
      Array.polyProduct coreFactors =
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.polyProduct_quadraticIntegerRootFactors?_some hquad
  have hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q :=
    Hex.quadraticIntegerRootFactors?_normalizeFactorSign hcore_pos hquad
  have hsize_two : ∀ q ∈ coreFactors.toList, q.size = 2 := fun q hq =>
    Hex.quadraticIntegerRootFactors?_factor_size_eq_two
      hcore_pos hcore_primitive hquad hq
  -- factorPower decomposition (#4759).
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  -- No-tail divisibility (#4807).
  have hnot_dvd_tail :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  -- Per-factor pos_lc.  From `normalizeFactorSign q = q`, the leading
  -- coefficient is nonneg (otherwise `scale (-1) q = q` would force `q = 0`),
  -- and combined with irreducibility (hence `q ≠ 0`) it is strictly positive.
  have hpos_lc :
      ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  -- Per-factor degree positivity (from `q.size = 2`).
  have hdegree :
      ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    have hsize := hsize_two q hq
    show 0 < q.degree?.getD 0
    unfold Hex.DensePoly.degree?
    simp [hsize]
  -- Repeated part is nonzero (from primitivity of its toPolynomial image).
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    have hR_prim :=
      normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
    apply hR_prim.ne_zero
    show HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart = 0
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  -- Inline helper: any element of a list divides the foldl-mul product seeded
  -- at 1.  Mirrors the proof shape of `linearFactor_dvd_listFoldl_of_mem`
  -- (`HexBerlekampZassenhaus/Basic.lean:9646`) for arbitrary ZPoly elements.
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  -- For each `q` with `2 ≤ q.size`, `factorPower q e` has size at least `e + 1`.
  -- Mirrors the `hfactorPower_size_ge` inline argument in
  -- `reassemblyExpansionComplete_singleton_of_irreducible` above.
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  -- Fuel bound.  Each `factorPower qe.1 qe.2` divides the decomposition
  -- foldl product (= `repeatedPart`); combined with `size_le_of_dvd_nonzero`
  -- and the size lower bound this gives `qe.2 + 1 ≤ rp.size + 1`.
  have hfuel :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro qe hqe_mem
    have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
    have hq_size := hsize_two qe.1 hq_mem
    have hfp_size_lb :
        qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lb qe.1 qe.2 (by omega)
    have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro hzero
      rw [hzero] at hfp_size_lb
      have h0 : (0 : Hex.ZPoly).size = 0 := rfl
      omega
    have hfp_mem :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          ((coreFactors.toList.zip exponents).map
            (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
      List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact dvd_foldl_one_of_mem _ _ hfp_mem
    have hfp_size_le :
        (Hex.Factorization.factorPower qe.1 qe.2).size ≤
          (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
    omega
  -- Apply the non-monic factorPower expansion-complete helper.
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart coreFactors hpos_lc hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel

end IntReductionMod

/-- **#4549 base task (HO-1), outer-bound specialisation, rewired for #4553.**

Specialisation of `liftedFactorSubsetPartition_of_choosePrimeData`
(`HexBerlekampZassenhausMathlib/Basic.lean`) at the precision count
actually consumed by the slow exhaustive branch of `Hex.factor f`
(i.e. `Hex.factorWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`).
The resulting partition value has the exact `core` / `d` /
`J = Finset.univ` / `target = core` shape expected by the `hpartition`
hypothesis of
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
(PR #4537), so the HO-1 slow-path assembly can apply that wrapper
directly together with the #4543 base value at the same outer-bound
shape.

The explicit `hcore_sqfree` hypothesis previously threaded through this
constructor is now discharged internally from `f ≠ 0` via
`IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree`.
Downstream HO-1 assemblies only need to supply the much weaker non-zero
premise on `f`. -/
theorem liftedFactorSubsetPartition_outerBound_of_choosePrimeData
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdescent :
      HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f) primeData
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData)
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData)) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
  exact liftedFactorSubsetPartition_of_choosePrimeData_success_descent
    (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hchoose
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf)
      hdescent hlifted_of_modP hinitial

/--
Branch-local substrate for the small-mod singleton arm, specialised to the
square-free core produced by `Hex.normalizeForFactor`.

This is the capstone-facing package of side conditions required by
`IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP`:
the primitive Mathlib image of the normalised square-free core, the selected
prime's leading-coefficient nonvanishing after reduction, and the executable
`choosePrimeData?`/singleton-factor-count witnesses in the exact shape used by
the fast singleton branch.
-/
theorem smallModSingletonBranchPreconditions_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1) :
    (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).IsPrimitive ∧
      (Int.castRingHom (ZMod primeData.p))
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore).leadingCoeff ≠ 0 ∧
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData ∧
      primeData.factorsModP.size ≤ 1 := by
  exact ⟨
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive
      f hf_ne,
    IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero
      (Hex.normalizeForFactor f).squareFreeCore primeData hchoose,
    hchoose,
    hsmall⟩

/--
Small-mod singleton irreducibility for the normalised square-free core, with
all primitive, leading-coefficient, selected-prime, and singleton-count
preconditions discharged from the executable branch state.

This is the reusable bridge package consumed by the recorded-entry singleton
umbrella below and by the `factor_irreducible_of_nonUnit` capstone path.
-/
theorem squareFreeCore_irreducible_of_smallModSingletonBranch
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  rcases smallModSingletonBranchPreconditions_of_choosePrimeData
      f hf_ne primeData hchoose hsmall with
    ⟨hprim, hlc_map_ne, hchoose', hsmall'⟩
  exact
    IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP
      (Hex.normalizeForFactor f).squareFreeCore primeData hchoose' hsmall'
      hprim hlc_map_ne

/-- **#4562 HO-1 base task — small-mod singleton arm umbrella.**

Per-branch HO-1 component for the small-mod singleton arm of the capstone
`factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this fast-path branch is `Hex.ZPoly.Irreducible`,
given only `f ≠ 0`, the branch marker hypotheses, and the executable
`choosePrimeData?` success witness `hchoose`. The reassembly
expansion-complete side condition is discharged internally via
`IntReductionMod.reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc`
(#4956 / PR #4961), so the umbrella no longer requires an explicit
`hcomplete` premise.

Composes:
* `Hex.factorWithBound_entry_mem_small_mod_singleton_raw`
  (`HexBerlekampZassenhaus/Basic.lean`) — the Mathlib-free branch-shape
  lemma identifying each recorded entry as the sign-normalisation of a raw
  factor in the singleton-core reassembly;
* `IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP`
  — the singleton-core irreducibility theorem from the chosen prime's
  Berlekamp form;
* the base dischargers from #4545
  (`IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  and `IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero`),
  which produce `hprim` and `hlc_map_ne` from `f ≠ 0` and `hchoose`;
* `IntReductionMod.reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc`
  — the non-monic primitive singleton-arm `hcomplete` discharger from
  #4956 / PR #4961, producing the reassembly expansion-complete side
  condition internally from `hcore_irr`,
  `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero`, and the positive
  squarefree-core degree derived from the umbrella's existing `hdeg`
  premise;
* `Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`
  — the Mathlib-free reassembly lift turning singleton-core irreducibility
  into raw factor irreducibility under the internally-discharged
  expansion-complete side condition;
* `zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible` — the
  sign-normalisation lift from raw factor irreducibility to entry
  irreducibility.

The slow-path exhaustive arm (#4561), the slow-path constant and quadratic
sub-branches, and the fast BHKS arm (gated on #2567) are separate concerns
and are out of scope here. -/
theorem factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat) (hB_pos : 1 ≤ B)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hchoose :
      Hex.choosePrimeData?
        (Hex.normalizeForFactor f).squareFreeCore = some primeData) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Branch-shape lemma: entry is the sign-normalisation of a raw factor in
  -- the singleton-core reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_small_mod_singleton_raw f B entry
      primeData hB_pos hdeg hchoose hsmall hquadratic hentry_mem
  -- Singleton-core irreducibility from the chosen prime's Berlekamp form,
  -- with `hprim` and `hlc_map_ne` discharged by the #4545 base lemmas.
  have hcore_irr :
      Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore :=
    squareFreeCore_irreducible_of_smallModSingletonBranch
      f hf_ne primeData hchoose hsmall
  -- Discharge the reassembly expansion-complete side condition internally
  -- using the non-monic primitive singleton-arm discharger
  -- (#4956 / PR #4961).
  have hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        #[(Hex.normalizeForFactor f).squareFreeCore] :=
    IntReductionMod.reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc
      f hf_ne hcore_irr
      (Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne)
      (Nat.pos_of_ne_zero hdeg)
  -- Lift singleton-core irreducibility through the reassembly to raw factor
  -- irreducibility.
  have h_core_array :
      ∀ factor ∈
        (#[(Hex.normalizeForFactor f).squareFreeCore] : Array Hex.ZPoly).toList,
        Hex.ZPoly.Irreducible factor := by
    intro factor hmem
    have hfactor : factor = (Hex.normalizeForFactor f).squareFreeCore := by
      simpa using hmem
    exact hfactor ▸ hcore_irr
  have hraw_irr : Hex.ZPoly.Irreducible raw :=
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) #[(Hex.normalizeForFactor f).squareFreeCore]
      hcomplete h_core_array hraw_mem
  -- Sign-normalisation lifts raw factor irreducibility to entry
  -- irreducibility.
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hraw_irr

/-- **#4605 HO-1 base task — `hchoose`-free small-mod singleton arm umbrella.**

Capstone-facing variant of
`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`
that takes no separate `hchoose` premise. The witness that `choosePrimeData?`
selected a good prime is packed into the strengthened branch predicate
`hsmall_chosen`, which is the **exact predicate** the post-#4605
`factorFastFactorsWithBound` dispatcher tests when deciding whether to fire
the singleton arm: `(choosePrimeData? sf).isSome ∧ size ≤ 1`. The dispatcher
restriction guarantees that this conjunction is *necessary* (not just
sufficient) for the singleton branch to fire — when `choosePrimeData?` returns
`none` the fast path returns `none` and `factorWithBound` falls through to the
slow exhaustive path, so the singleton branch-shape lemma's conclusion does
not apply in that case.

The reassembly expansion-complete side condition is discharged internally
by the `_of_choosePrimeData` umbrella above (via
`IntReductionMod.reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc`,
#4956 / PR #4961), so this wrapper does not require an explicit
`hcomplete` premise either. -/
theorem factor_small_mod_singleton_branch_entry_irreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat) (hB_pos : 1 ≤ B)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList) :
    Hex.ZPoly.Irreducible entry.1 :=
  factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData
    f hf_ne B hB_pos entry hdeg primeData hsmall hquadratic hentry_mem
    hchoose

/-- **#4565 HO-1 base task — fast-path constant arm umbrella.**

Per-branch HO-1 component for the fast-path **constant square-free core** arm
of the capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded
by `Hex.factorWithBound f B` in the constant branch is
`Hex.ZPoly.Irreducible`, given only `f ≠ 0` and the constant-core marker
`hdeg`. The reassembly expansion-complete side condition is discharged
internally via `Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 /
PR #4598), so the umbrella no longer requires an explicit `hcomplete`
premise.

The constant branch is the earliest dispatch in `factorFastFactorsWithBound`
(triggered when `(normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0`)
and is unconditional on the recombination budget `B`, the small-mod prime
data, and the quadratic-root short-circuit, so the umbrella requires no
`hB_pos` / `hsmall` / `hquadratic` / `hchoose` premises.  The naming suffix
`_of_choosePrimeData` is retained for parity with the singleton arm #4564 (it
is documentary here — the constant branch does not invoke `choosePrimeData`).

Composes:
* `Hex.factorWithBound_entry_mem_constant_branch_raw`
  (`HexBerlekampZassenhaus/Basic.lean`) — the Mathlib-free branch-shape
  lemma identifying each recorded entry as the sign-normalisation of a raw
  factor in the singleton-core reassembly;
* `Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete`
  — the membership classifier for the complete-expansion branch of
  reassembly: under `hcomplete`, each raw factor is either an extracted
  `X`-power factor or one of the supplied core factors (here the singleton
  `#[squareFreeCore]`);
* `Hex.xPowerFactorArray_irreducible` — `X`-power factors are irreducible
  (each is `X`);
* `Hex.squareFreeCore_eq_one_of_constant_of_ne_zero` — in the constant
  branch the primitive square-free core collapses to `1`, so the
  singleton-core entry would be the unit `1`;
* `Hex.factorWithBound_entry_shouldRecord` — recorded entries pass the
  `shouldRecordPolynomialFactor` filter, hence cannot equal `1`; this rules
  out the singleton-core entry, leaving only the `X`-power case;
* `zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible` — the
  sign-normalisation lift from raw factor irreducibility to entry
  irreducibility.

Sibling arms: the small-mod singleton arm #4564
(`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`)
covers the `... ≠ 0` fast-path case with `factorsModP.size ≤ 1`; the slow
exhaustive arm (#4561, in flight) covers the slow-path exhaustive case;
the fast BHKS arm is gated on directive #2567. -/
theorem factor_constant_branch_entry_irreducible_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Discharge the reassembly expansion-complete side condition internally
  -- using the constant-arm discharger (#4585 / PR #4598).
  have hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        #[(Hex.normalizeForFactor f).squareFreeCore] :=
    Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf_ne hdeg
  -- Branch-shape lemma: entry is the sign-normalisation of a raw factor in
  -- the singleton-core reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_constant_branch_raw f B entry hdeg hentry_mem
  -- Reassembly classifier under `hcomplete`: raw is either an extracted
  -- `X`-power factor or the singleton core entry.
  rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
      (Hex.normalizeForFactor f) #[(Hex.normalizeForFactor f).squareFreeCore]
      raw hcomplete hraw_mem with hx | hcore_mem
  · -- `X`-power case: raw is `X`, directly irreducible; sign-normalise.
    rw [hentry_eq]
    exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
      (Hex.xPowerFactorArray_irreducible (Hex.normalizeForFactor f).xPower raw
        hx)
  · -- Singleton-core case: raw = squareFreeCore = 1, so entry.1 = 1, which
    -- contradicts `shouldRecordPolynomialFactor entry.1 = true`.
    exfalso
    have hraw_eq : raw = (Hex.normalizeForFactor f).squareFreeCore := by
      simpa using hcore_mem
    have hcore_one : (Hex.normalizeForFactor f).squareFreeCore = 1 :=
      Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf_ne hdeg
    have hentry_one : entry.1 = 1 := by
      rw [hentry_eq, hraw_eq, hcore_one, Hex.normalizeFactorSign_one]
    have hrecord : Hex.shouldRecordPolynomialFactor entry.1 = true :=
      Hex.factorWithBound_entry_shouldRecord f B entry hentry_mem
    rw [hentry_one, Hex.shouldRecordPolynomialFactor_one] at hrecord
    exact Bool.false_ne_true hrecord

/-- **#4571 HO-1 base task — fast-path quadratic arm umbrella.**

Per-branch HO-1 component for the fast-path quadratic integer-root arm of the
capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this fast-path branch is `Hex.ZPoly.Irreducible`,
given `f ≠ 0`, `1 < B`, and the branch marker hypotheses (`hdeg`, `hquad`).
The reassembly expansion-complete side condition is discharged internally via
`IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(#4747), so the umbrella no longer requires an explicit `hcomplete` premise.

Composes:
* `Hex.factorWithBound_entry_mem_quadratic_branch_raw` — the Mathlib-free
  branch-shape lemma identifying each recorded entry as the
  sign-normalisation of a raw factor in the quadratic-branch reassembly;
* `Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive` — the
  Mathlib-free executable irreducibility of every coreFactor, residual or
  not, under primitivity;
* `IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive` +
  `IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  (from #4545) — the primitivity lemma for the squarefree core;
* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` — the positive-leading-
  coefficient invariant for the squarefree core;
* `Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`
  — the Mathlib-free reassembly lift turning per-core-factor irreducibility
  into raw factor irreducibility under the `hcomplete` side condition;
* `zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible` — the
  sign-normalisation lift from raw factor irreducibility to entry
  irreducibility.

The slow-path exhaustive arm (#4561), the slow-path quadratic arm
(#4575, landed), the fast-path constant arm (#4565 / #4572, landed), the
small-mod singleton arm (#4562 / #4564, landed), and the fast BHKS arm
(gated on #2567) are separate concerns and out of scope here. -/
theorem factor_quadratic_branch_entry_irreducible_of_quadraticRoots
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat) (hB_gt_one : 1 < B)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hquad :
      Hex.quadraticIntegerRootFactors?
        (Hex.normalizeForFactor f).squareFreeCore = some coreFactors)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Discharge the reassembly expansion-complete side condition internally
  -- using the quadratic-arm discharger (#4747).
  have hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors :=
    IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
      f hf_ne hquad
  -- Branch-shape lemma: entry = normalizeFactorSign raw for raw ∈ reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_quadratic_branch_raw f B entry hB_gt_one hdeg
      hquad hentry_mem
  -- Primitivity of squareFreeCore via the Mathlib-side lemma.
  have hcore_primitive :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  -- Every coreFactor is irreducible.
  have hcore_factors_irr :
      ∀ cf ∈ coreFactors.toList, Hex.ZPoly.Irreducible cf := fun cf hcf_mem =>
    Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
      hcore_pos hcore_primitive hquad hcf_mem
  -- Reassembly lift: every raw factor is irreducible when reassembly is
  -- expansion-complete and every core factor is irreducible.
  have hraw_irr : Hex.ZPoly.Irreducible raw :=
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) coreFactors hcomplete hcore_factors_irr hraw_mem
  -- Sign-normalisation lifts to entry irreducibility.
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hraw_irr

/-- **#4575 HO-1 base task — slow-path quadratic integer-root arm umbrella.**

Per-branch HO-1 component for the slow-path **quadratic integer-root** arm of
the capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this arm is `Hex.ZPoly.Irreducible`, given the
branch markers and the `hfast_none` slow-dispatch witness. The reassembly
expansion-complete side condition is discharged internally via
`IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(#4747), so the umbrella no longer requires an explicit `hcomplete` premise.

The slow-quadratic branch is reachable through the public `Hex.factor` entry
exactly when `factorFastFactorsWithBound f B = none` (so the public
`factorWithBound = (fast).getD (slow)` falls through to the slow path) and the
slow path then takes its `match quadraticIntegerRootFactors? = some _` arm.
Per the issue (#4575), this corresponds to one of:

* `B = 0`, or
* `B = 1 ∧ size > 1 ∧ factorFastCoreWithBound = none ∧ quadratic = some _`.

In case (3) of the fast-path `none` enumeration the slow path takes its
exhaustive branch (since the quadratic short-circuit is `none` there), so it
is not reachable here.

Composes:
* `Hex.factorWithBound_entry_mem_slow_quadratic_branch_raw`
  (`HexBerlekampZassenhaus/Basic.lean`) — the Mathlib-free branch-shape
  lemma identifying each recorded entry as the sign-normalisation of a raw
  factor in the quadratic-core reassembly;
* `Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive` — the
  Mathlib-free executable irreducibility of every coreFactor, residual or
  not, under primitivity;
* `IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive` +
  `IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  (from #4545) — the primitivity lemma for the squarefree core;
* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` — the positive-leading-
  coefficient invariant for the squarefree core;
* `Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`
  — the Mathlib-free reassembly lift turning per-core-factor irreducibility
  into raw factor irreducibility under the `hcomplete` side condition;
* `zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible` — the
  sign-normalisation lift from raw factor irreducibility to entry
  irreducibility.

This umbrella shares its shape with the fast-path quadratic arm umbrella
`factor_quadratic_branch_entry_irreducible_of_quadraticRoots` above; only the
branch-shape lemma differs (`_slow_quadratic_branch_raw` keys off
`hfast_none` instead of `1 < B`).

Sibling arms: the fast-path constant arm #4565
(`factor_constant_branch_entry_irreducible_of_choosePrimeData`); the fast-path
small-mod singleton arm #4564
(`factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`);
the fast-path quadratic arm #4571
(`factor_quadratic_branch_entry_irreducible_of_quadraticRoots`, above);
the slow-path exhaustive arm #4561 (in flight); the fast BHKS arm gated on
directive #2567. -/
theorem factor_slow_quadratic_branch_entry_irreducible_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hquad :
      Hex.quadraticIntegerRootFactors?
        (Hex.normalizeForFactor f).squareFreeCore = some coreFactors)
    (hfast_none : Hex.factorFastFactorsWithBound f B = none)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Discharge the reassembly expansion-complete side condition internally
  -- using the quadratic-arm discharger (#4747).
  have hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors :=
    IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
      f hf_ne hquad
  -- Branch-shape lemma: entry = normalizeFactorSign raw for raw ∈ reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_slow_quadratic_branch_raw f B entry hdeg
      hquad hfast_none hentry_mem
  -- Primitivity of squareFreeCore via the Mathlib-side lemma.
  have hcore_primitive :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  -- Every coreFactor is irreducible.
  have hcore_factors_irr :
      ∀ cf ∈ coreFactors.toList, Hex.ZPoly.Irreducible cf := fun cf hcf_mem =>
    Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
      hcore_pos hcore_primitive hquad hcf_mem
  -- Reassembly lift: every raw factor is irreducible when reassembly is
  -- expansion-complete and every core factor is irreducible.
  have hraw_irr : Hex.ZPoly.Irreducible raw :=
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) coreFactors hcomplete hcore_factors_irr hraw_mem
  -- Sign-normalisation lifts to entry irreducibility.
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hraw_irr

set_option maxHeartbeats 8000000

/-- Abstract-bound variant of
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux`: the
concrete inner-form Mignotte precision on the squarefree core
`2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore < d.p ^ d.k`
is replaced by `2 * B' < d.p ^ d.k` against an abstract bound `B'`, paired
with the leading-coefficient bound on the core
(`(Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`) and the universal divisor
coefficient bound (`∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`).

The previous `hcore_monic` premise (Gap 1 shim from #4561/#4940) is replaced
by `hselected : Hex.ZPoly.toMonicPrimeData? squareFreeCore = some
(Hex.choosePrimeData squareFreeCore)`. The lifted-factor monicness /
natDegree-positivity / injectivity facts for the `toMonic` lift are obtained
from the `MonicReductionCorrespondence` transport package via
`monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore`,
which discharges Gap 1 by the monicising-by-scaling route. The original-core
nonzero, primitive, and positive-leading-coefficient facts are derived
internally from `hf_ne` via `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero`
and `IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero`. -/
private theorem factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (entry : Hex.ZPoly × Nat)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (hentry_mem : entry ∈ (Hex.factorWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (hcomplete : Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData))
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ (Hex.normalizeForFactor f).squareFreeCore →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision :
      2 * B' <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Branch-shape positivity of the squareFreeCore degree.
  have hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 :=
    hbranch.2.1
  have hcore_deg_pos : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
    Nat.pos_of_ne_zero hdeg
  -- Original-core facts from `hf_ne` (no monicness assumed).
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_primitive : Hex.ZPoly.Primitive
      (Hex.normalizeForFactor f).squareFreeCore :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  -- Prime + modulus bookkeeping from `hselected`.
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime _ _ hselected
  have hbound_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound f :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf_ne
  have hB_ne_zero : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0 := hbound_pos.ne'
  have hspec :
      2 * Hex.ZPoly.defaultFactorCoeffBound f <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p :=
    Hex.precisionForCoeffBound_spec hp_prime.two_le _
  have hd_modulus :
      2 ≤ primeData.p ^
        Hex.precisionForCoeffBound
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData.p := by
    omega
  -- Lifted-factor facts via the monicized Hensel lift selected by `hselected`.
  have hprecision_lift :
      1 ≤ Hex.precisionForCoeffBound
        (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p := by
    by_contra hlt
    have hzero :
        Hex.precisionForCoeffBound
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p = 0 := by
      omega
    rw [hzero, pow_zero] at hd_modulus
    omega
  have hd_liftedFactor_monic :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData),
        Hex.DensePoly.Monic
          (liftedFactor
            (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f) primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  have hd_liftedFactor_natDegree_pos :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData),
        0 < (HexPolyZMathlib.toPolynomial
          (liftedFactor
            (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f) primeData) i)).natDegree :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  have hd_liftedFactor_inj :
      Function.Injective
        (liftedFactor
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData)) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  -- Discharge `hcore_record` from positive squareFreeCore degree.
  have hcore_record : Hex.shouldRecordPolynomialFactor
      (Hex.normalizeForFactor f).squareFreeCore = true := by
    have hne_one : (Hex.normalizeForFactor f).squareFreeCore ≠ 1 := by
      intro hone
      apply hdeg
      rw [hone]
      exact Hex.DensePoly.degree?_C_getD 1
    have hne_neg_one :
        (Hex.normalizeForFactor f).squareFreeCore ≠ Hex.DensePoly.C (-1 : Int) := by
      intro hneg
      apply hdeg
      rw [hneg]
      exact Hex.DensePoly.degree?_C_getD (-1)
    unfold Hex.shouldRecordPolynomialFactor
    simp [hcore_ne, hne_one, hne_neg_one]
  -- Branch-shape split: each recorded entry is either an X-power image or
  -- an exhaustive-core-factor image (under `hcomplete`).
  obtain ⟨raw, hraw_or, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete
      f (Hex.ZPoly.defaultFactorCoeffBound f) entry primeData hchoose
      hbranch hcomplete hentry_mem
  rcases hraw_or with hx | hcore_mem
  · -- X-power case: raw is an X-power factor, directly irreducible.
    rw [hentry_eq]
    exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
      (Hex.xPowerFactorArray_irreducible (Hex.normalizeForFactor f).xPower raw hx)
  · -- Exhaustive-core case: apply the outer-bound slow-path wrapper's
    -- `_of_bound` sibling (#4947).
    exact factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
      primeData
      hbranch hentry_mem hchoose
        (henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData f
          primeData hchoose hdescent hlifted_of_modP)
        (liftedFactorSubsetPartition_outerBound_of_choosePrimeData f hf_ne
          primeData hchoose hdescent hlifted_of_modP hinitial)
      hcore_ne hcore_primitive hcore_lc_pos hcore_record hB_ne_zero
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hd_liftedFactor_inj B' hcore_lc_le hvalid hprecision
      ⟨raw, hcore_mem, hentry_eq⟩

set_option maxHeartbeats 4000000 in
/-- **#4561 HO-1 base task — slow-path exhaustive arm umbrella.**

Per-branch HO-1 component for the slow-path **exhaustive recombination** arm of
the capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)` in this slow
exhaustive branch is `Hex.ZPoly.Irreducible`, given `f ≠ 0`, the branch marker
`hbranch`, the `Hex.ZPoly.toMonicPrimeData?` selection witness `hselected`,
and the base-shim premises listed below.

Specialises the outer-bound slow-path wrapper #4537
(`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
in `HexBerlekampZassenhausMathlib/Basic.lean`) by:

* discharging the wrapper's `h` premise via the #4543 base-task constructor
  `henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData`;
* discharging the wrapper's `hpartition` via the #4554 base-task constructor
  `liftedFactorSubsetPartition_outerBound_of_choosePrimeData`;
* obtaining the lifted-factor monicness / natDegree-positivity / injectivity
  facts from the `MonicReductionCorrespondence` transport package
  (`monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore`),
  which threads `hselected` through the package fields landed in #5733;
* deriving `hcore_ne`, `hcore_primitive`, and `hcore_lc_pos` from `hf_ne`
  via `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` and
  `IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero`;
  `hcore_record` from the branch marker `hbranch.2.1`; `hB_ne_zero` from
  `defaultFactorCoeffBound_pos_of_ne_zero` (#4637); `hp_prime` and
  `hd_modulus` from `Hex.ZPoly.toMonicPrimeData?_prime` and
  `precisionForCoeffBound_spec`;
* internally case-splitting via
  `factorWithBound_entry_mem_exhaustive_branch_xPower_or_core_of_reassemblyComplete`
  on whether the entry's raw source is an extracted `X`-power factor (closed
  by `xPowerFactorArray_irreducible`) or an exhaustive core factor (closed by
  the wrapper itself).

The remaining base-shim premises are:

* **`hselected`** — replaces the original `hcore_monic` shim (Gap 1). The
  squarefree core is not generally monic, but the lifted-factor facts can
  be obtained from the transport package after aligning the Hensel modular
  data with the monic transform via `Hex.ZPoly.toMonicPrimeData?`. Discharged
  upstream by the caller's `Hex.ZPoly.toMonicPrimeData?` selection witness.
* **`hcomplete`** (Gap 2) — discharged in the public surface
  `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData` via
  `reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core`.
* **`hprecision`** (Gap 3) — exposed by this wrapper; downstream callers
  wanting an outer-shape Mignotte witness route through the `_of_bound`
  sibling.

(The sibling Gap 3a/3b shim premises `hB_ne_zero` / `hd_modulus` were
discharged by #4637 via `defaultFactorCoeffBound_pos_of_ne_zero` and
`precisionForCoeffBound_spec`.)

Downstream callers (notably the HO-1 capstone #4170 / #4819)
currently route through the public umbrella's `_of_bound` sibling
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound`
(which discharges Gap 3 against an abstract bound) and supply
`hselected` directly.

The slow-path constant and quadratic sub-branches are tracked separately
(`squareFreeCore.degree?.getD 0 = 0` and `quadraticIntegerRootFactors? =
some _` respectively); the fast BHKS branch is gated on directive #2567.

**#4848:** the original `hcomplete` premise (Gap 2) is no longer free.
The public surface
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData` derives it
from `reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core`
before invoking this internal residual; the residual is exposed via a private
auxiliary so the heartbeat-sensitive wrapper application here is not
re-elaborated through the discharger.

**#4982:** the original `hprecision` shim (Gap 3) now has an
abstract-bound route. The sibling
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound`
(landed in PR #4982) replaces the core-shape `hprecision` with the
abstract triple `(B', hcore_lc_le, hvalid, hprecision : 2 * B' < d.p ^ d.k)`.
Downstream callers wanting to discharge `hprecision` against an
outer-shape Mignotte witness (notably the HO-1 capstone #4170 / #4819)
should route through the `_of_bound` sibling rather than the wrapper here.

**#5723 (HO-1 Gap 1 caller):** the original `hcore_monic` shim (Gap 1)
is closed by the monicising-by-scaling route. The lifted-factor facts on
the `toMonic`-image Hensel lift come from the
`MonicReductionCorrespondence` transport package (introduced under #5718
and renamed under #5778), which carries a `_of_monicPrimeData` conditional
for each of monicness, natDegree positivity, and injectivity. The
caller-facing surface
`monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore`
(#5733) instantiates the package at the normalized square-free core and
extracts the three facts under the `hselected` selection witness.

Thin wrapper over
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound
(Hex.normalizeForFactor f).squareFreeCore` and discharges the abstract
bound hypotheses via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`. -/
private theorem factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (entry : Hex.ZPoly × Nat)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (hentry_mem : entry ∈ (Hex.factorWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (hcomplete : Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.ZPoly.Irreducible entry.1 := by
  have hcore_lc_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux_of_bound
    f hf_ne entry hbranch hentry_mem primeData hselected hchoose
    hdescent hlifted_of_modP hinitial hcomplete
    (Hex.ZPoly.defaultFactorCoeffBound
      (Hex.normalizeForFactor f).squareFreeCore)
    hcore_lc_le
    (defaultFactorCoeffBound_valid
      (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
    hprecision

set_option maxHeartbeats 8000000

/-- Abstract-bound variant of
`exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData`:
the concrete `2 * defaultFactorCoeffBound squareFreeCore < d.p ^ d.k`
Mignotte precision is replaced by `2 * B' < d.p ^ d.k` against an
abstract bound `B'`, paired with the leading-coefficient bound on the
core and the universal divisor coefficient bound `∀ g ∣ core, ∀ i,
(g.coeff i).natAbs ≤ B'`.

The original premise `Hex.DensePoly.Monic squareFreeCore` (Gap 1 shim from
#4561/#4940) is replaced by `hselected :
Hex.ZPoly.toMonicPrimeData? squareFreeCore = some (Hex.choosePrimeData
squareFreeCore)`: the lifted-factor monicness / natDegree-positivity /
injectivity facts are obtained via the `MonicReductionCorrespondence`
transport package
(`monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore`)
rather than by collapsing `Hex.ZPoly.toMonicLiftData` back to a Hensel
lift on the original (already-monic) core. Primitivity, positive leading
coefficient, and nonzero on the squarefree core are derived from
`hf_ne` via `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` and
`IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero`. -/
theorem exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
        g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision :
      2 * B' <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.shouldRecordPolynomialFactor q = true) ∧
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.normalizeFactorSign q = q) ∧
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.ZPoly.Irreducible q) := by
  -- Branch-shape positivity of the squareFreeCore degree.
  have hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 :=
    hbranch.2.1
  have hcore_deg_pos : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
    Nat.pos_of_ne_zero hdeg
  -- Original-core facts from `hf_ne` (no monicness assumed).
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_primitive : Hex.ZPoly.Primitive
      (Hex.normalizeForFactor f).squareFreeCore :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  -- Prime + modulus bookkeeping from `hselected`.
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime _ _ hselected
  have hbound_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound f :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf_ne
  have hB_ne_zero : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0 := hbound_pos.ne'
  have hspec :
      2 * Hex.ZPoly.defaultFactorCoeffBound f <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p :=
    Hex.precisionForCoeffBound_spec hp_prime.two_le _
  have hd_modulus :
      2 ≤ primeData.p ^
        Hex.precisionForCoeffBound
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData.p := by
    omega
  -- Lifted-factor facts via the monicized Hensel lift selected by `hselected`.
  have hprecision_lift :
      1 ≤ Hex.precisionForCoeffBound
        (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p := by
    by_contra hlt
    have hzero :
        Hex.precisionForCoeffBound
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p = 0 := by
      omega
    rw [hzero, pow_zero] at hd_modulus
    omega
  have hd_liftedFactor_monic :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData),
        Hex.DensePoly.Monic
          (liftedFactor
            (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f) primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  have hd_liftedFactor_natDegree_pos :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData),
        0 < (HexPolyZMathlib.toPolynomial
          (liftedFactor
            (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f) primeData) i)).natDegree :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  have hd_liftedFactor_inj :
      Function.Injective
        (liftedFactor
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData)) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData hcore_lc_pos hcore_deg_pos hselected hprecision_lift
  have hcore_record : Hex.shouldRecordPolynomialFactor
      (Hex.normalizeForFactor f).squareFreeCore = true := by
    have hne_one : (Hex.normalizeForFactor f).squareFreeCore ≠ 1 := by
      intro hone
      apply hdeg
      rw [hone]
      exact Hex.DensePoly.degree?_C_getD 1
    have hne_neg_one :
        (Hex.normalizeForFactor f).squareFreeCore ≠ Hex.DensePoly.C (-1 : Int) := by
      intro hneg
      apply hdeg
      rw [hneg]
      exact Hex.DensePoly.degree?_C_getD (-1)
    unfold Hex.shouldRecordPolynomialFactor
    simp [hcore_ne, hne_one, hne_neg_one]
  refine ⟨?_, ?_, ?_⟩
  · exact Hex.exhaustiveCoreFactorsWithBound_shouldRecord
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
      hcore_record
  · exact Hex.exhaustiveCoreFactorsWithBound_normalizeFactorSign
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
      (Hex.squareFreeCore_normalizeFactorSign_of_ne_zero f hf_ne)
  · exact exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
        (henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData f
          primeData hchoose hdescent hlifted_of_modP)
        (liftedFactorSubsetPartition_outerBound_of_choosePrimeData f hf_ne
          primeData hchoose hdescent hlifted_of_modP hinitial)
      hcore_ne hcore_primitive hcore_lc_pos hcore_record hB_ne_zero
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hd_liftedFactor_inj B' hcore_lc_le hvalid hprecision

/-- **#4806 HO-1 base task — exhaustive-arm expansion-precondition packaging
(precursor to #4627).**

Companion to the slow-path exhaustive-arm umbrella
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData` (#4561):
delivers, for the default `Hex.factorWithBound` precision in the slow
exhaustive arm, the per-element preconditions of
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`
that are currently provable from the existing wrapper stack. #4627 will
consume this packaging together with the #4759 repeated-part `factorPower`
decomposition to discharge `reassemblyExpansionComplete_exhaustive_of_ne_zero`.

The three conjuncts are routed as follows:

* `Hex.shouldRecordPolynomialFactor q = true`
  — via `Hex.exhaustiveCoreFactorsWithBound_shouldRecord` from the branch-
  derived `Hex.shouldRecordPolynomialFactor (Hex.normalizeForFactor f).squareFreeCore = true`;
* `Hex.normalizeFactorSign q = q`
  — via `Hex.exhaustiveCoreFactorsWithBound_normalizeFactorSign` from
  `Hex.squareFreeCore_normalizeFactorSign_of_ne_zero`;
* `Hex.ZPoly.Irreducible q`
  — via `exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
  at the outer-bound shape (the same wrapper consumed by the sibling umbrella).

**Base-task gaps — narrowed scope per #4806.** The expansion wrapper additionally
requires `Hex.DensePoly.Monic q` and `0 < q.degree?.getD 0` on every emitted
factor. Neither is currently exposed for arbitrary `Hex.recombineExhaustive`
output: by inspection of `Hex.recombinationSearchModAux`, every emitted factor
is structurally
`Hex.normalizeFactorSign (Hex.ZPoly.primitivePart (Hex.centeredLiftPoly
  (Array.polyProduct selected.toArray) modulus))` for some `selected` ranging
over `Hex.subsetSplits d.liftedFactors.toList`. Monicness and positive degree
both then follow from `recombinationCandidate_monic` (`HexBerlekampZassenhausMathlib/Basic.lean`)
and `natDegree_toPolynomial_recombinationCandidate_eq_sum`, but only after a
lemma identifying each emitted `selected` with `liftedSubsetSelectedList d S`
for some `LiftedFactorSubset d`. That identification has not yet been built — neither
`recombineExhaustive_monic` nor `recombineExhaustive_natDegree_pos` (nor any
generalisation through `recombinationSearchMod`) exists in
`HexBerlekampZassenhaus/Basic.lean`. Both pieces are deferred to a successor
base-task sub-issue. Until that lands, downstream caller #4627 must thread
the missing monicness and positive-degree facts as additional hypotheses,
mirroring the gap-shim precedent set by the sibling umbrella's `hcomplete`
and `hprecision` premises (Gap 2 and Gap 3 of the #4561 documentation).

The base-shim premises (`hf_ne`, `hbranch`, `hselected`, `hprecision`)
match the sibling umbrella verbatim so the two theorems share their
base-derivation idiom and downstream callers can thread both with the
same evidence bundle. The previous `hcore_monic` shim (Gap 1) is discharged
via the monicising-by-scaling route, threaded through the
`MonicReductionCorrespondence` transport package; the caller-facing
`hselected` premise selects the modular factor data aligned with the
monic transform. Notably absent from this signature: the `hcomplete`
premise (this packaging is precisely the base lemmas #4627 will use to
discharge that premise) and the `hentry_mem` premise (this packaging
yields a universal conclusion over the entire core-factors array).

Thin wrapper over
`exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound
(Hex.normalizeForFactor f).squareFreeCore` and discharges the abstract
bound hypotheses via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.shouldRecordPolynomialFactor q = true) ∧
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.normalizeFactorSign q = q) ∧
    (∀ q ∈ (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData).toList,
      Hex.ZPoly.Irreducible q) := by
  have hcore_lc_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound
    f hf_ne hbranch primeData hselected hchoose
    hdescent hlifted_of_modP hinitial
    (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
    hcore_lc_le
    (defaultFactorCoeffBound_valid (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
    hprecision

/--
Correspondence package between the `toMonic` lift of `core` and the
factorization data of the original primitive positive-leading `core`.

The Hensel lift is built from `(Hex.ZPoly.toMonic core).monic`, while the
factor correspondence, the dilate-model recovery theorem
(`recovery_of_bound`, recovering `liftedRecoveryCandidate core d S`), and the
exhaustive-wrapper membership statement remain phrased over the original
`core`.
-/
structure MonicReductionCorrespondence
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  core_ne : core ≠ 0
  core_primitive : Hex.ZPoly.Primitive core
  core_lc_pos : 0 < Hex.DensePoly.leadingCoeff core
  monic_isMonic :
    Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic
  monic_nonzero :
    (Hex.ZPoly.toMonic core).monic ≠ 0
  monic_degree_eq :
    (Hex.ZPoly.toMonic core).monic.degree?.getD 0 =
      core.degree?.getD 0
  liftedFactor_monic_of_monicPrimeData :
    Hex.ZPoly.toMonicPrimeData? core = some primeData →
      ∀ i : LiftedFactorIndex d,
        Hex.DensePoly.Monic (liftedFactor d i)
  liftedFactor_natDegree_pos_of_monicPrimeData :
    Hex.ZPoly.toMonicPrimeData? core = some primeData →
      ∀ i : LiftedFactorIndex d,
        0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree
  liftedFactor_injective_of_monicPrimeData :
    Hex.ZPoly.toMonicPrimeData? core = some primeData →
      Function.Injective (liftedFactor d)
  correspondence :
    HenselSubsetCorrespondenceHypotheses core B primeData d True True
  partition :
    LiftedFactorSubsetPartition core d Finset.univ core
  recovery_of_bound :
    ∀ {factor : Hex.ZPoly} {S : LiftedFactorSubset d},
      (Hex.ZPoly.toMonic core).monic ≠ 0 →
      Hex.normalizeFactorSign factor = factor →
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k →
      RepresentsIntegerFactorAtLift core d factor S →
      liftedRecoveryCandidate core d S = factor
  exhaustive_mem_of_scaled_search :
    ∀ {factor : Hex.ZPoly} {factors : List Hex.ZPoly},
      B ≠ 0 →
      Hex.scaledRecombinationSearchMod (Hex.DensePoly.leadingCoeff core)
          core (d.p ^ d.k) d.liftedFactors.toList = some factors →
      factor ∈ factors →
      factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList

/--
Specialised monic-reduction correspondence for the normalized square-free
core used by the exhaustive branch of `factorWithBound`.
-/
theorem monicReductionCorrespondence_of_normalizeForFactor_squareFreeCore
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hdegree : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
      (primeData : Hex.PrimeChoiceData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData)) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    MonicReductionCorrespondence core B primeData d := by
  intro core B d
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core := by
    simpa [core] using Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_primitive : Hex.ZPoly.Primitive core := by
    simpa [core] using
      IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hmonic_isMonic :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos
      (by simpa [core] using hdegree)
  have hmonic_degree :
      (Hex.ZPoly.toMonic core).monic.degree?.getD 0 =
        core.degree?.getD 0 := by
    simpa [Hex.ZPoly.toMonic_degree] using
      Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos
        (by simpa [core] using hdegree)
  have hsqfree :
      Squarefree (HexPolyZMathlib.toPolynomial core) := by
    simpa [core] using
      IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf_ne
  have hbound_pos : 0 < B := by
    simpa [B] using Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf_ne
  have hprecision_of_monicPrimeData :
      ∀ hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData,
        1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    intro hselected
    have hp_prime : Hex.Nat.Prime primeData.p :=
      Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
    have hspec :
        2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
      Hex.precisionForCoeffBound_spec hp_prime.two_le B
    have hmodulus : 2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
      omega
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  refine
    { lift_eq := rfl
      core_ne := hcore_ne
      core_primitive := hcore_primitive
      core_lc_pos := hcore_lc_pos
      monic_isMonic := hmonic_isMonic
      monic_nonzero := zpoly_ne_zero_of_monic hmonic_isMonic
      monic_degree_eq := hmonic_degree
      liftedFactor_monic_of_monicPrimeData := ?_
      liftedFactor_natDegree_pos_of_monicPrimeData := ?_
      liftedFactor_injective_of_monicPrimeData := ?_
      correspondence := ?_
      partition := ?_
      recovery_of_bound := ?_
      exhaustive_mem_of_scaled_search := ?_ }
  · intro hselected
    exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos (by simpa [core] using hdegree)
      hselected (hprecision_of_monicPrimeData hselected)
  · intro hselected
    exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos (by simpa [core] using hdegree)
      hselected (hprecision_of_monicPrimeData hselected)
  · intro hselected
    exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos (by simpa [core] using hdegree)
      hselected (hprecision_of_monicPrimeData hselected)
  · simpa [core, B] using
      henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData hchoose hdescent hlifted_of_modP
  · simpa [core, B] using
      liftedFactorSubsetPartition_of_choosePrimeData_success_descent
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData hchoose hsqfree hdescent hlifted_of_modP hinitial
  · intro factor S hmonic_ne hfactor_norm hprecision hrep
    rcases hrep with ⟨hrec⟩
    exact hrec.candidate_eq_of_monic_dvd hmonic_ne hfactor_norm hprecision
  · intro factor factors hB_ne hsearch hmem
    exact exhaustiveCoreFactorsWithBound_mem_of_scaledRecombinationSearchMod_some
      (core := core) (B := B) (primeData := primeData) (d := d)
      hB_ne rfl hsearch hmem

/--
Caller-facing extraction of the `toMonic` lifted-factor facts for the
normalized square-free core.  The hypotheses are the non-monic branch facts:
positive leading coefficient comes from `f ≠ 0`, positive degree is supplied by
the caller, and the Hensel modular data is aligned through
`Hex.ZPoly.toMonicPrimeData?`, not by rewriting the core to be monic.
-/
theorem monicReductionCorrespondence_liftedFactor_facts_of_normalizeForFactor_squareFreeCore
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hdegree : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
      (primeData : Hex.PrimeChoiceData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hselected :
        Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData)) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    (∀ i : LiftedFactorIndex d,
      Hex.DensePoly.Monic (liftedFactor d i)) ∧
    (∀ i : LiftedFactorIndex d,
      0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree) ∧
    Function.Injective (liftedFactor d) := by
  intro core B d
  have pkg :=
    monicReductionCorrespondence_of_normalizeForFactor_squareFreeCore
      f hf_ne hdegree primeData hchoose hdescent hlifted_of_modP hinitial
  exact
    ⟨pkg.liftedFactor_monic_of_monicPrimeData hselected,
      pkg.liftedFactor_natDegree_pos_of_monicPrimeData hselected,
      pkg.liftedFactor_injective_of_monicPrimeData hselected⟩

/-- Divisibility propagation through `List.foldl (· * ·)` on `Hex.ZPoly`: if
`x` divides the accumulator at any point, it divides the final foldl. Used by
`mem_dvd_foldl_mul_zpoly`. -/
private theorem dvd_acc_foldl_mul_zpoly (x : Hex.ZPoly) :
    ∀ (l : List Hex.ZPoly) (acc : Hex.ZPoly),
      x ∣ acc → x ∣ l.foldl (· * ·) acc := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      simpa using hacc
  | cons head tail ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      refine ih (acc * head) ?_
      -- `x ∣ acc * head` from `x ∣ acc` via commutativity + `dvd_mul_left_poly`.
      have hcomm : acc * head = head * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc head
      rw [hcomm]
      exact Hex.DensePoly.dvd_mul_left_poly head hacc

/-- An element of a `List Hex.ZPoly` divides the `List.foldl (· * ·)` of that
list. Used by the exhaustive-arm fuel-bound construction in
`reassemblyExpansionComplete_exhaustive_of_ne_zero`. -/
private theorem mem_dvd_foldl_mul_zpoly
    (l : List Hex.ZPoly) (acc : Hex.ZPoly) (x : Hex.ZPoly) (hx : x ∈ l) :
    x ∣ l.foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons head tail ih =>
      rw [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · -- `x = head`: divides `acc * x = acc * head`, and propagates through tail.
        refine dvd_acc_foldl_mul_zpoly x tail (acc * x) ?_
        have hcomm : acc * x = x * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc x
        rw [hcomm]
        exact ⟨acc, rfl⟩
      · exact ih (acc * head) hx

/-- For a polynomial `q` of positive degree, the size of
`Hex.Factorization.factorPower q m` is at least `m + 1`. Each iteration of
`polyPow` multiplies the running product by `q`, increasing the size by at
least `q.size - 1 ≥ 1`. -/
private theorem factorPower_size_lower_bound
    {q : Hex.ZPoly} (hq_deg : 0 < q.degree?.getD 0) :
    ∀ m : Nat, m + 1 ≤ (Hex.Factorization.factorPower q m).size := by
  intro m
  -- From `0 < q.degree?.getD 0`, derive `2 ≤ q.size`.
  have hq_size_ge_two : 2 ≤ q.size := by
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hq_deg
    by_cases h : q.size = 0
    · simp [h] at hq_deg
    · split at hq_deg <;> omega
  induction m with
  | zero =>
      show 1 ≤ (1 : Hex.ZPoly).size
      rfl
  | succ n ih =>
      rw [Hex.Factorization.factorPower_succ]
      have hprev_pos : 0 < (Hex.Factorization.factorPower q n).size := by
        omega
      have hq_pos : 0 < q.size := by omega
      have hmul_size :
          (Hex.Factorization.factorPower q n * q).size =
            (Hex.Factorization.factorPower q n).size + q.size - 1 :=
        Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hq_pos
      omega

/-- Abstract-bound variant of `reassemblyExpansionComplete_exhaustive_of_ne_zero`
for the case where the squarefree core is monic. Specialises the per-emitted-
factor monicness base lemma `Hex.exhaustiveCoreFactorsWithBound_monic`,
which holds when the input core is monic. -/
theorem reassemblyExpansionComplete_exhaustive_of_ne_zero_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (hcore_monic : Hex.DensePoly.Monic
      (Hex.normalizeForFactor f).squareFreeCore)
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
        g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision :
      2 * B' <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData) := by
  -- Base setup: discharge `hcore_record` and `hcore_ne` from the branch
  -- hypothesis + monicness.
  have hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 := hbranch.2.1
  have hcore_ne := zpoly_ne_zero_of_monic hcore_monic
  have hcore_record : Hex.shouldRecordPolynomialFactor
      (Hex.normalizeForFactor f).squareFreeCore = true := by
    have hne_one : (Hex.normalizeForFactor f).squareFreeCore ≠ 1 := by
      intro hone
      apply hdeg
      rw [hone]
      exact Hex.DensePoly.degree?_C_getD 1
    have hne_neg_one :
        (Hex.normalizeForFactor f).squareFreeCore ≠ Hex.DensePoly.C (-1 : Int) := by
      intro hneg
      apply hdeg
      rw [hneg]
      exact Hex.DensePoly.degree?_C_getD (-1)
    unfold Hex.shouldRecordPolynomialFactor
    simp [hcore_ne, hne_one, hne_neg_one]
  -- #4806 package for `(shouldRecord, normalizeFactorSign, Irreducible)` at the
  -- abstract bound `B'`.
  obtain ⟨_, hnorm, hirr⟩ :=
      exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound
        f hf_ne hbranch
        primeData
        hselected hchoose hdescent hlifted_of_modP hinitial
        B' hcore_lc_le hvalid hprecision
  -- New base lemma: monicness and positive-degree of every emitted factor.
  have hmonic :=
    Hex.exhaustiveCoreFactorsWithBound_monic
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
      hcore_monic hcore_record
  have hdegree :=
    Hex.exhaustiveCoreFactorsWithBound_degree_pos
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
      hcore_monic hcore_record
  -- polyProduct = squareFreeCore.
  have hprod :=
    Hex.exhaustiveCoreFactorsWithBound_product
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
  -- Fuel bound: for any valid exponents, each exponent satisfies
  -- `e + 1 ≤ repeatedPart.size + 1`, via factorPower divisibility + size.
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
    with hcoreFactors_def
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ coreFactors.toList := by
      have := List.of_mem_zip hqe
      exact this.1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]; rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]; exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  -- Apply the generic assembler.
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover
    f hf_ne coreFactors hirr hprod hnorm hmonic hdegree hfuel

/-- **#4848 / #4808 residual — exhaustive-arm `reassemblyExpansionComplete`
discharger.**

Specialised companion to the slow-path exhaustive-arm umbrella
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData` (#4561). The
`hcomplete` premise of that umbrella is exactly
`Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
  (Hex.exhaustiveCoreFactorsWithBound ...)`; this discharger constructs that
witness from the supporting lemmas the umbrella already exposes:

* the generic Mathlib-side assembler
  `IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover`
  (#4840), composing the repeated-part `factorPower` decomposition (#4759)
  and the no-tail divisibility lemma (#4807) into the executable
  expansion contract;
* the exhaustive-arm emit-side properties:
  `Hex.exhaustiveCoreFactorsWithBound_product` for the cover identity,
  `Hex.exhaustiveCoreFactorsWithBound_monic` and
  `Hex.exhaustiveCoreFactorsWithBound_degree_pos` (new) for the monicness
  and positive-degree per-factor preconditions, and the
  `exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData`
  package (#4806) for irreducibility / sign-normalisation;
* a fuel bound, derived by combining the factorPower divisibility chain
  (each emitted factor's `factorPower` divides the foldl product, hence the
  repeated part) with the `factorPower_size_lower_bound` size estimate.

After this lands, callers of the exhaustive umbrella no longer need to thread
a free `hcomplete` premise. -/
theorem reassemblyExpansionComplete_exhaustive_of_ne_zero
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdescent :
      HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f) primeData
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData)
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData))
    (hcore_monic : Hex.DensePoly.Monic
      (Hex.normalizeForFactor f).squareFreeCore)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData) := by
  have hcore_ne := zpoly_ne_zero_of_monic hcore_monic
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact reassemblyExpansionComplete_exhaustive_of_ne_zero_of_bound
    f hf_ne hbranch primeData hselected hchoose
    hdescent hlifted_of_modP hinitial hcore_monic
    (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
    hcore_lc_le
    (defaultFactorCoeffBound_valid (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
    hprecision

/-- Abstract-bound variant of
`reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core`:
the concrete `2 * defaultFactorCoeffBound squareFreeCore < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound `B'`,
paired with the leading-coefficient bound on the core and the universal
divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`.

The previous `hcore_monic` premise (Gap 1 shim) is replaced by `hselected :
Hex.ZPoly.toMonicPrimeData? squareFreeCore = some (Hex.choosePrimeData
squareFreeCore)`; the upstream
`exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound`
call now consumes `hselected` (closing Gap 1 via the
`MonicReductionCorrespondence` transport package). -/
theorem reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (hcore_primitive : Hex.ZPoly.Primitive
      (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore)
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
        g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision :
      2 * B' <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData) := by
  -- Base setup: discharge `hcore_record` and `hcore_ne` from `hbranch` +
  -- `hcore_lc_pos`.
  have hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 := hbranch.2.1
  have hcore_ne := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_record : Hex.shouldRecordPolynomialFactor
      (Hex.normalizeForFactor f).squareFreeCore = true := by
    have hne_one : (Hex.normalizeForFactor f).squareFreeCore ≠ 1 := by
      intro hone
      apply hdeg
      rw [hone]
      exact Hex.DensePoly.degree?_C_getD 1
    have hne_neg_one :
        (Hex.normalizeForFactor f).squareFreeCore ≠ Hex.DensePoly.C (-1 : Int) := by
      intro hneg
      apply hdeg
      rw [hneg]
      exact Hex.DensePoly.degree?_C_getD (-1)
    unfold Hex.shouldRecordPolynomialFactor
    simp [hcore_ne, hne_one, hne_neg_one]
  -- #4806 package for `(shouldRecord, normalizeFactorSign, Irreducible)` at the
  -- abstract bound `B'`.
  obtain ⟨_, hnorm, hirr⟩ :=
      exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound
        f hf_ne hbranch
        primeData
        hselected hchoose hdescent hlifted_of_modP hinitial
        B' hcore_lc_le hvalid hprecision
  -- Weakened-input base lemmas: positive-degree from #4946 deliv 6, primitivity
  -- from #4946 deliv 5.
  have hdegree :=
    Hex.exhaustiveCoreFactorsWithBound_degree_pos_of_primitive_pos_lc_core
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
      hcore_primitive hcore_lc_pos hcore_record
  -- polyProduct = squareFreeCore.
  have hprod :=
    Hex.exhaustiveCoreFactorsWithBound_product
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f)
      primeData
    with hcoreFactors_def
  -- Per-factor pos_lc: combine `q ≠ 0` (from irreducibility) with
  -- `normalizeFactorSign q = q` (forcing `leadingCoeff q ≥ 0`).
  have hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm : Hex.normalizeFactorSign q = q := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  -- Fuel bound: identical to the monic version.
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ coreFactors.toList := by
      have := List.of_mem_zip hqe
      exact this.1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]; rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]; exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  -- Apply the `_of_pos_lc` assembler from #4949.
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf_ne coreFactors hirr hprod hnorm hpos_lc hdegree hfuel

/-- Weakened-conclusion sibling of
`reassemblyExpansionComplete_exhaustive_of_ne_zero`: the per-emitted-factor
monicness requirement on the assembler call is dropped, threading
`Primitive` + `0 < leadingCoeff` on the squareFreeCore instead.

Three substitutions versus the monic original:

* per-factor `Monic q` is replaced by per-factor `0 < leadingCoeff q`,
  derived from `exhaustiveCoreFactorsWithBound_primitive` (#4946 deliv 5)
  together with the `normalizeFactorSign q = q` invariant (existing,
  `exhaustiveCoreFactorsWithBound_normalizeFactorSign`) — same shape as
  the quadratic-arm derivation in
  `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
  above;
* the per-factor positive-degree base lemma is supplied by
  `exhaustiveCoreFactorsWithBound_degree_pos_of_primitive_pos_lc_core`
  (#4946 deliv 6) instead of the monic-input
  `exhaustiveCoreFactorsWithBound_degree_pos`;
* the mid-layer assembler is
  `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`
  (the `_of_pos_lc` sibling landed via #4949) rather than the monic
  parent.

The previous `hcore_monic` premise (Gap 1 shim) is dropped by routing the
upstream
`exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData_of_bound`
call through the `MonicReductionCorrespondence` transport package: the
`hselected` premise selects the modular factor data aligned with the
monic transform, and the lifted-factor facts come from the package rather
than from a `Monic`-input Hensel lift on the original core.

Thin wrapper over
`reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound
(Hex.normalizeForFactor f).squareFreeCore` and discharges the abstract
bound hypotheses via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdescent :
      HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f) primeData
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData)
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData))
    (hcore_primitive : Hex.ZPoly.Primitive
      (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData) := by
  have hcore_ne := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core_of_bound
    f hf_ne hbranch primeData hselected hchoose
    hdescent hlifted_of_modP hinitial hcore_primitive hcore_lc_pos
    (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
    hcore_lc_le
    (defaultFactorCoeffBound_valid (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
    hprecision

/-- Abstract-bound variant of
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`: the
concrete inner-form Mignotte precision on the squarefree core
`2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore < d.p ^ d.k`
is replaced by `2 * B' < d.p ^ d.k` against an abstract bound `B'`, paired
with the leading-coefficient bound on the core
(`(Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`) and the universal divisor
coefficient bound (`∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`).

The previous `hcore_monic` premise (Gap 1) is dropped: the reassembly is
discharged via
`reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core_of_bound`
threaded with `hcore_primitive`, `hcore_lc_pos`, and `hselected`, and the
inner umbrella `_aux_of_bound` consumes the same `hselected` to obtain the
lifted-factor facts via the `MonicReductionCorrespondence` transport
package. -/
theorem factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (entry : Hex.ZPoly × Nat)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (hentry_mem : entry ∈ (Hex.factorWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
      (primeData : Hex.PrimeChoiceData)
      (hselected : Hex.ZPoly.toMonicPrimeData?
        (Hex.normalizeForFactor f).squareFreeCore = some primeData)
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
      (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
        g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision :
      2 * B' <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.ZPoly.Irreducible entry.1 := by
    have hcore_lc_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
    have hcore_primitive :=
      IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
    exact factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux_of_bound
      f hf_ne entry hbranch hentry_mem primeData hselected hchoose
      hdescent hlifted_of_modP hinitial
      (reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core_of_bound
        f hf_ne hbranch primeData hselected hchoose
        hdescent hlifted_of_modP hinitial hcore_primitive hcore_lc_pos
        B' hcore_lc_le hvalid hprecision)
      B' hcore_lc_le hvalid hprecision

/-- **#4561 / #4848 / #5723 HO-1 base task — slow exhaustive-arm umbrella,
with the `hcomplete` premise dropped via the #4848 discharger and the
`hcore_monic` shim closed by the #5723 monicising-by-scaling route.**

Public surface of the exhaustive-arm HO-1 umbrella. Gap 2 (`hcomplete`) is
discharged internally via
`reassemblyExpansionComplete_exhaustive_of_ne_zero_of_primitive_pos_lc_core`
(#4848). Gap 3 (`hprecision`) is exposed in this wrapper's signature
against the core-shape Mignotte threshold; downstream callers wanting
the abstract-bound surface (notably the HO-1 capstone #4170 / #4819)
should route through the `_of_bound` sibling
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound`
(PR #4982). Gap 1 is closed: the new `hselected` premise replaces
`hcore_monic`, and the lifted-factor facts come from the
`MonicReductionCorrespondence` transport package via #5723.

Thin wrapper over
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound
(Hex.normalizeForFactor f).squareFreeCore` and discharges the abstract
bound hypotheses via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem factor_exhaustive_branch_entry_irreducible_of_choosePrimeData
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (entry : Hex.ZPoly × Nat)
    (hbranch : Hex.factorWithBoundUsesExhaustiveBranch f
      (Hex.ZPoly.defaultFactorCoeffBound f))
    (hentry_mem : entry ∈ (Hex.factorWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
    (primeData : Hex.PrimeChoiceData)
    -- Gap 1 closure (#5723): selects the modular factor data aligned with
    -- the `toMonic` transform, feeding the `MonicReductionCorrespondence`
    -- transport package.
    (hselected : Hex.ZPoly.toMonicPrimeData?
      (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    -- HO-5d-2b (#5854) / HO-5d-2c (#5855): the `choosePrimeData?` witness
    -- threaded into the HBZ Mathlib bridges, which now take the
    -- explicit-witness shape.
      (hchoose :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData)
      (hdescent :
        HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f) primeData
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData) True True)
      (hlifted_of_modP :
        ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
          RepresentsIntegerFactorModP primeData factor S →
          RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.toMonicLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)
              primeData) factor
            (liftedSubsetOfModPSubset primeData
              (Hex.ZPoly.toMonicLiftData
                (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)
                primeData)
              hdescent.factor_count_eq S))
      (hinitial :
        InitialLiftedFactorSubsetPartitionEvidence
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData))
    -- Gap 3 (base task): explicit on this wrapper; downstream callers
    -- wanting an outer-shape bound should route through the `_of_bound`
    -- sibling
    -- `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound`
    -- (PR #4982).
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore <
        primeData.p ^
          Hex.precisionForCoeffBound
            (Hex.ZPoly.defaultFactorCoeffBound f)
            primeData.p) :
    Hex.ZPoly.Irreducible entry.1 := by
  have hcore_lc_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_of_bound
    f hf_ne entry hbranch hentry_mem primeData hselected hchoose
    hdescent hlifted_of_modP hinitial
    (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
    hcore_lc_le
      (defaultFactorCoeffBound_valid (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
      hprecision

set_option maxHeartbeats 200000

/-- Mathlib-side abstract-bound wrapper for the slow-trial exhaustive arm.

Specialises the Mathlib-free
`Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible`
(`HexBerlekampZassenhaus/Basic.lean:13443`) to the normalized square-free
core of an `f ≠ 0` input, discharging the four core-shape hypotheses
(`ne_zero`, `Primitive`, `0 < leadingCoeff`, `SquareFreeRat`) from `hf_ne`
via the existing helpers:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` for `0 < leadingCoeff`
  (and `zpoly_ne_zero_of_pos_lc` for `ne_zero`);
* `normalizeForFactor_squareFreeCore_primitive_of_ne_zero` (Mathlib-side)
  for `Primitive`;
* `Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore` for
  `SquareFreeRat`.

The divisor coefficient bound `hbound` stays explicit because two natural
specialisations live downstream: the intrinsic-core form
(`B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`,
discharged below by `defaultFactorCoeffBound_valid` on the core) and the
public-bound form (`B := Hex.ZPoly.defaultFactorCoeffBound f`, required
by the slow-trial arm of the `h_raw` dispatch in
`factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible`), which
needs the `g ∣ (Hex.normalizeForFactor f).squareFreeCore → g ∣ f`
divisibility chain through `primitiveSquareFreeDecomposition_reassembly_signed`
and the primitive-part divisibility relation. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (hbound : ∀ g : Hex.ZPoly,
      g ∣ (Hex.normalizeForFactor f).squareFreeCore →
      ∀ i, (g.coeff i).natAbs ≤ B) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore B).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sq : Hex.ZPoly.SquareFreeRat (Hex.normalizeForFactor f).squareFreeCore := by
    have hsq :=
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
        (by simpa [Hex.normalizeForFactor] using hcore_ne)
    simpa [Hex.normalizeForFactor] using hsq
  exact Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible
    (Hex.normalizeForFactor f).squareFreeCore B
    hcore_ne hcore_prim hcore_pos hcore_sq hbound factor hmem

/-- Intrinsic-core default-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at `B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`.

The divisor coefficient bound is discharged directly by
`defaultFactorCoeffBound_valid` applied to the (nonzero) square-free core.
This is the natural specialisation for callers that have already routed
through the core's intrinsic Mignotte data; the public slow-trial dispatch
in `Hex.factorSlowTrialFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`
uses the outer bound `Hex.ZPoly.defaultFactorCoeffBound f`, which requires
an additional `(Hex.normalizeForFactor f).squareFreeCore ∣ f` divisibility
chain (tracked separately) to discharge against this wrapper's `hbound`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_squareFreeCore_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound
                    (Hex.normalizeForFactor f).squareFreeCore)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  exact
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne
      (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
      (defaultFactorCoeffBound_valid
        (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
      factor hmem

/-- Transitivity of `∣` on `Hex.ZPoly`, Mathlib-side.  Composes the witness
multiplications explicitly. -/
private theorem zpoly_dvd_trans {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨r, hr⟩ := hbc
  exact ⟨q * r, by rw [hr, hq, Hex.DensePoly.mul_assoc_poly (S := Int)]⟩

/-- Public-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at the outer bound `B := Hex.ZPoly.defaultFactorCoeffBound f` consumed by the
slow-trial arm of the `h_raw` dispatch.

The divisor coefficient bound is discharged by lifting
`defaultFactorCoeffBound_valid f` along `Hex.squareFreeCore_dvd_self`: any
divisor of the square-free core also divides `f`, so its coefficients are
bounded by `Hex.ZPoly.defaultFactorCoeffBound f`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound f)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  refine
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne (Hex.ZPoly.defaultFactorCoeffBound f) ?_ factor hmem
  intro g hg i
  exact defaultFactorCoeffBound_valid f hf_ne g
    (zpoly_dvd_trans hg (Hex.squareFreeCore_dvd_self f hf_ne)) i

/-- **Slow-trial exhaustive-arm reassembly discharger (Mathlib-side).**

When the slow trial path takes the exhaustive branch, the reassembly of the
integer-trial core factors of `(normalizeForFactor f).squareFreeCore` at the
public bound `B := Hex.ZPoly.defaultFactorCoeffBound f` is expansion-complete.
The integer-trial analog of
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`: it
composes the public-bound core irreducibility wrapper, the polyProduct /
normalizeFactorSign / degree-positivity companions, and the non-monic
expansion-complete surface `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`.
Per-factor positive leading coefficient follows from the sign-normalisation
identity and irreducibility; the fuel bound from the per-factor
`factorPower` size lower bound and `size_le_of_dvd_nonzero`. -/
theorem reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)) := by
  classical
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  set coreFactors :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) with hcf
  have hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q :=
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default f hf
  have hprod :
      Array.polyProduct coreFactors = (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct _ _
  have hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign _ _ hcore_pos
  have hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0 :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_degree_pos _ _ hcore_prim hcore_pos
  -- Per-factor positive leading coefficient from `normalizeFactorSign q = q`
  -- and irreducibility (hence `q ≠ 0`).
  have hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  refine IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf coreFactors hirr hprod hnorm hpos_lc hdegree ?_
  -- Fuel bound.
  intro exponents hlen hdecomp
  have hsize_ge : ∀ q ∈ coreFactors.toList, 2 ≤ q.size := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_size_pos : 0 < q.size := Hex.ZPoly.size_pos_of_ne_zero q hq_ne
    have hq_deg := hdegree q hq
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold Hex.DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    omega
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    have hR_prim :=
      IntReductionMod.normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
    apply hR_prim.ne_zero
    show HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart = 0
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  intro qe hqe_mem
  have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
  have hq_size := hsize_ge qe.1 hq_mem
  have hfp_size_lb :
      qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
    factorPower_size_lb qe.1 qe.2 hq_size
  have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
    intro hzero
    rw [hzero] at hfp_size_lb
    have h0 : (0 : Hex.ZPoly).size = 0 := rfl
    omega
  have hfp_mem :
      Hex.Factorization.factorPower qe.1 qe.2 ∈
        ((coreFactors.toList.zip exponents).map
          (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
    List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  have hfp_dvd_rp :
      Hex.Factorization.factorPower qe.1 qe.2 ∣
        (Hex.normalizeForFactor f).repeatedPart := by
    rw [hdecomp]
    exact dvd_foldl_one_of_mem _ _ hfp_mem
  have hfp_size_le :
      (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
    Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
  omega

/-- When the fast path declines (`factorFastFactorsWithBound f B = none`), the
square-free core has positive degree.  The fast path short-circuits with
`some _` whenever the core is degree-0, so a `none` result rules out that
branch — and with it the degree-0 arm of the slow trial path, whose raw output
contains the non-irreducible unit `1`. -/
private theorem factorFast_none_squareFreeCore_degree_ne_zero
    {f : Hex.ZPoly} {B : Nat}
    (hfast : Hex.factorFastFactorsWithBound f B = none) :
    (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 := by
  intro hdeg0
  simp [Hex.factorFastFactorsWithBound, hdeg0] at hfast

/-- **Slow-trial raw-factor irreducibility (Mathlib-side), exhaustive and
quadratic arms.**

Under the dispatch hypothesis `factorFastFactorsWithBound f B = none` (which
holds on the slow-trial disjunct of the `h_raw` case-split, where both the fast
and slow-modular paths returned `none`), every raw factor produced by
`factorSlowTrialFactorsWithBound f (defaultFactorCoeffBound f)` is irreducible.

The fast-path `none` result forces the square-free core to have positive
degree, so the degree-0 branch (whose raw output appends the unit `1`) is
unreachable.  The remaining two branches dispatch through
`reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`:

* quadratic short-circuit — completeness from
  `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`, core
  irreducibility from `quadraticIntegerRootFactors?_factor_irreducible_of_primitive`;
* exhaustive trial — completeness from
  `reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero`, core
  irreducibility from
  `exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default`.

This is the slow-trial component of the `h_raw` dispatch consumed by
`factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible` /
`factor_entries_irreducible` for the #6672 capstone. -/
theorem factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hfast : Hex.factorFastFactorsWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f) = none) :
    ∀ raw ∈ (Hex.factorSlowTrialFactorsWithBound f
              (Hex.ZPoly.defaultFactorCoeffBound f)).toList,
      Hex.ZPoly.Irreducible raw := by
  intro raw hmem
  have hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0 :=
    factorFast_none_squareFreeCore_degree_ne_zero hfast
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorSlowTrialFactorsWithBound] at hmem
  rw [if_neg hdeg_ne] at hmem
  cases hquad :
      Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
  | some coreFactors =>
      simp only [hquad] at hmem
      refine
        Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          (Hex.normalizeForFactor f) coreFactors ?_ ?_ hmem
      · exact
          IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
      · intro factor hfmem
        exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
          hcore_pos hcore_prim hquad hfmem
  | none =>
      simp only [hquad] at hmem
      refine
        Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          (Hex.normalizeForFactor f) _ ?_ ?_ hmem
      · exact reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero f hf
      · exact
          exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
            f hf

end HexBerlekampZassenhausMathlib
