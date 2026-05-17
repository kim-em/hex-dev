import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampMathlib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Separable

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
resulting `FpPoly` through the Berlekamp bridge.
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
bridge: it lets a downstream consumer chain the executable good-prime
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
`Hex.ZPoly.Irreducible` via the existing bridge equivalence.
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
    (_hselected : primeData = Hex.choosePrimeData core)
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

/--
Scaling a nonzero modular image to its monic representative preserves the
executable square-free gcd check used by Berlekamp.
-/
private theorem gcd_monicModularImage_derivative_eq_one
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
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
      HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime f hsquareFree
    have hu_ne : HexModArithMathlib.ZMod64.toZMod u ≠ 0 := by
      have hp_hex : Hex.Nat.Prime p := by
        constructor
        · exact (Fact.out : Nat.Prime p).two_le
        · intro m hmdvd
          rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h
      have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ 0 := by
        have hpos : 0 < f.size := by
          simpa [Hex.DensePoly.isZero, Hex.DensePoly.size,
            Array.isEmpty_iff_size_eq_zero, Nat.pos_iff_ne_zero] using hzero
        rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred f hpos]
        exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size f hpos
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

/--
Small-mod singleton irreducibility composed without the explicit
`hirr_fModP` hypothesis.

Given a `choosePrimeData?` success witness and a singleton-bounded
modular-factor count, the executable `factorsModP` array packaged by
`choosePrimeData?_factorsModP_berlekamp_form` is the Berlekamp factor
output for the monic modular image; the `irreducible_of_berlekampFactor_factors_length_le_one`
no-split bridge then turns this into Mathlib irreducibility of the monic
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
  obtain ⟨hzero, hfield, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
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
  -- Apply the no-split bridge to obtain Mathlib irreducibility of the monic image.
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
  -- Push through the Mathlib bridge using toMathlibPolynomial_scale.
  rw [hmonicImg_eq, toMathlibPolynomial_scale] at hirr_monic
  -- The scaling constant is a unit (nonzero in the field).
  have hfsize : 0 < (Hex.ZPoly.modP primeData.p core).size := by
    rcases Nat.eq_zero_or_pos (Hex.ZPoly.modP primeData.p core).size with hsz | hsz
    · exfalso
      have hzero' : (Hex.ZPoly.modP primeData.p core).isZero = true := by
        simpa [Hex.DensePoly.isZero, Hex.DensePoly.size,
          Array.isEmpty_iff_size_eq_zero] using hsz
      rw [hzero'] at hzero
      exact Bool.noConfusion hzero
    · exact hsz
  have hlead_ne :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core) ≠ 0 := by
    rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred _ hfsize]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size _ hfsize
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
  obtain ⟨hzero, _hfield, _hfactors_eq⟩ :=
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
      (p := primeData.p) (Hex.ZPoly.modP primeData.p core) hzero hsquareFree
  exact squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData
    core primeData hselected hsmall hprim hlc_map_ne hsquareFree_monic

/-! ### Substrate discharges for the small-mod singleton branch

The two lemmas below feed `squareFreeCore_irreducible_of_small_mod_singleton`
its `hprim` and `hlc_map_ne` side-conditions from the executable invariants
that `normalizeForFactor` and `choosePrimeData?` already maintain. They
form the substrate for the small-mod singleton arm of the HO-1 capstone
`factor_irreducible_of_nonUnit` (issue #4170, decomposed in #4544).
-/

/--
Bridge from the executable `Hex.ZPoly.Primitive` predicate to Mathlib's
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
  have hcore_ne :
      (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core ≠ 0 :=
    Hex.extractXPower_core_ne_zero_of_ne_zero f hf
  have hprod_prim :
      Hex.ZPoly.Primitive
        ((Hex.normalizeForFactor f).squareFreeCore *
          (Hex.normalizeForFactor f).repeatedPart) := by
    simpa [Hex.normalizeForFactor] using
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive
        _ hcore_ne
  have hprod_isPrim :
      (HexPolyZMathlib.toPolynomial
          ((Hex.normalizeForFactor f).squareFreeCore *
            (Hex.normalizeForFactor f).repeatedPart)).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive hprod_prim
  rw [HexPolyZMathlib.toPolynomial_mul] at hprod_isPrim
  exact isPrimitive_of_dvd hprod_isPrim
    ⟨HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart, rfl⟩

/-! ### Squarefree transport for the square-free core

The lemmas below bridge the executable `Hex.ZPoly.SquareFreeRat` invariant
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
`Polynomial.derivative` under the `HexPolyMathlib.toPolynomial` bridge, for
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
gcd-associatedness bridge `HexPolyMathlib.toPolynomial_gcd_associated`
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
existing primitivity bridge
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
  -- Executable `SquareFreeRat` invariant on the square-free core.
  have hcore_ne :
      (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core ≠ 0 :=
    Hex.extractXPower_core_ne_zero_of_ne_zero f hf
  -- The square-free core of `normalizeForFactor f` is nonzero.  We argue
  -- from primitivity of the product `squareFreeCore * repeatedPart`:
  -- if the core were zero, the product would be zero, contradicting
  -- primitivity (the zero polynomial has zero content).
  have hcore_sq_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 := by
    intro hzero
    have hprod_prim :
        Hex.ZPoly.Primitive
          ((Hex.normalizeForFactor f).squareFreeCore *
            (Hex.normalizeForFactor f).repeatedPart) := by
      simpa [Hex.normalizeForFactor] using
        Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive
          _ hcore_ne
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
Bridge from the executable `isGoodPrime` invariant to the Mathlib
`Int.castRingHom (ZMod p)`-cast leading-coefficient nonvanishing
required by the reduction-mod-`p` machinery.

The good-prime predicate carries `leadingCoeffAdmissible`, i.e. the
executable `leadingCoeffModP` is nonzero; the iff bridge
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
Reverse bridge from Mathlib's `Polynomial.IsPrimitive` on the transported
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

end IntReductionMod

/-- **#4549 substrate (HO-1), outer-bound specialisation, rewired for #4553.**

Specialisation of `liftedFactorSubsetPartition_of_choosePrimeData`
(`HexBerlekampZassenhausMathlib/Basic.lean`) at the precision count
actually consumed by the slow exhaustive branch of `Hex.factor f`
(i.e. `Hex.factorWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`).
The resulting partition value has the exact `core` / `d` /
`J = Finset.univ` / `target = core` shape expected by the `hpartition`
hypothesis of
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
(PR #4537), so the HO-1 slow-path assembly can apply that wrapper
directly together with the #4543 substrate value at the same outer-bound
shape.

The explicit `hcore_sqfree` hypothesis previously threaded through this
constructor is now discharged internally from `f ≠ 0` via
`IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree`.
Downstream HO-1 assemblies only need to supply the much weaker non-zero
premise on `f`. -/
theorem liftedFactorSubsetPartition_outerBound_of_choosePrimeData
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let primeData := Hex.choosePrimeData core
    let B := Hex.precisionForCoeffBound
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p
    let d := Hex.henselLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core :=
  liftedFactorSubsetPartition_of_choosePrimeData _ _
    (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf)

/-- **#4562 HO-1 substrate — small-mod singleton arm umbrella.**

Per-branch HO-1 component for the small-mod singleton arm of the capstone
`factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this fast-path branch is `Hex.ZPoly.Irreducible`,
given only `f ≠ 0`, the branch marker hypotheses, the executable
`choosePrimeData?` success witness `hchoose`, and the reassembly
expansion-complete side condition.

Composes:
* `Hex.factorWithBound_entry_mem_small_mod_singleton_raw`
  (`HexBerlekampZassenhaus/Basic.lean`) — the Mathlib-free branch-shape
  lemma identifying each recorded entry as the sign-normalisation of a raw
  factor in the singleton-core reassembly;
* `IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP`
  — the singleton-core irreducibility theorem from the chosen prime's
  Berlekamp form;
* the substrate dischargers from #4545
  (`IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  and `IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero`),
  which produce `hprim` and `hlc_map_ne` from `f ≠ 0` and `hchoose`;
* `Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`
  — the Mathlib-free reassembly lift turning singleton-core irreducibility
  into raw factor irreducibility under the `hcomplete` side condition;
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
    (hsmall :
      (Hex.choosePrimeData
          (Hex.normalizeForFactor f).squareFreeCore).factorsModP.size ≤ 1)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        #[(Hex.normalizeForFactor f).squareFreeCore])
    (hchoose :
      Hex.choosePrimeData?
        (Hex.normalizeForFactor f).squareFreeCore = some
          (Hex.choosePrimeData
            (Hex.normalizeForFactor f).squareFreeCore)) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Branch-shape lemma: entry is the sign-normalisation of a raw factor in
  -- the singleton-core reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_small_mod_singleton_raw f B entry hB_pos
      hdeg hchoose hsmall hquadratic hentry_mem
  -- Singleton-core irreducibility from the chosen prime's Berlekamp form,
  -- with `hprim` and `hlc_map_ne` discharged by the #4545 substrate.
  have hcore_irr :
      Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore :=
    IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP
      (Hex.normalizeForFactor f).squareFreeCore _ hchoose hsmall
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive
        f hf_ne)
      (IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero
        _ _ hchoose)
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

/-- **#4605 HO-1 substrate — `hchoose`-free small-mod singleton arm umbrella.**

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

The eventual capstone wiring for the small-mod singleton arm composes this
with the `hcomplete` discharger from #4597 to produce a fully
hypothesis-discharged per-branch component. -/
theorem factor_small_mod_singleton_branch_entry_irreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (B : Nat) (hB_pos : 1 ≤ B)
    (entry : Hex.ZPoly × Nat)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hsmall_chosen :
      (Hex.choosePrimeData?
          (Hex.normalizeForFactor f).squareFreeCore).isSome ∧
        (Hex.choosePrimeData
            (Hex.normalizeForFactor f).squareFreeCore).factorsModP.size ≤ 1)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        #[(Hex.normalizeForFactor f).squareFreeCore]) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Derive the explicit `choosePrimeData?` equation from the `isSome` witness
  -- packed into `hsmall_chosen`.
  have hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some (Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore) := by
    cases hc :
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore with
    | none =>
        rw [hc] at hsmall_chosen
        exact absurd hsmall_chosen.1 (by simp)
    | some pd =>
        have hpd :
            Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore = pd := by
          unfold Hex.choosePrimeData; rw [hc]
        rw [hpd]
  exact factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData
    f hf_ne B hB_pos entry hdeg hsmall_chosen.2 hquadratic hentry_mem hcomplete
    hchoose

/-- **#4565 HO-1 substrate — fast-path constant arm umbrella.**

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

/-- **#4571 HO-1 substrate — fast-path quadratic arm umbrella.**

Per-branch HO-1 component for the fast-path quadratic integer-root arm of the
capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this fast-path branch is `Hex.ZPoly.Irreducible`,
given `f ≠ 0`, `1 < B`, the branch marker hypotheses (`hdeg`, `hquad`), and
the reassembly expansion-complete side condition.

Composes:
* `Hex.factorWithBound_entry_mem_quadratic_branch_raw` — the Mathlib-free
  branch-shape lemma identifying each recorded entry as the
  sign-normalisation of a raw factor in the quadratic-branch reassembly;
* `Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive` — the
  Mathlib-free executable irreducibility of every coreFactor, residual or
  not, under primitivity;
* `IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive` +
  `IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  (from #4545) — the primitivity bridge for the squarefree core;
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
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Branch-shape lemma: entry = normalizeFactorSign raw for raw ∈ reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_quadratic_branch_raw f B entry hB_gt_one hdeg
      hquad hentry_mem
  -- Primitivity of squareFreeCore via the Mathlib bridge.
  have hcore_primitive :
      Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore :=
    IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive
        f hf_ne)
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

/-- **#4575 HO-1 substrate — slow-path quadratic integer-root arm umbrella.**

Per-branch HO-1 component for the slow-path **quadratic integer-root** arm of
the capstone `factor_irreducible_of_nonUnit` (#4170): every entry recorded by
`Hex.factorWithBound f B` in this arm is `Hex.ZPoly.Irreducible`, given the
branch markers, the `hfast_none` slow-dispatch witness, and the reassembly
expansion-complete side condition.

The slow-quadratic branch is reachable through the public `Hex.factor` entry
exactly when `factorFastFactorsWithBound f B = none` (so the public
`factorWithBound = (fast).getD (slow)` falls through to `factorSlow`) and the
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
  (from #4545) — the primitivity bridge for the squarefree core;
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
    (hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcomplete :
      Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
        coreFactors) :
    Hex.ZPoly.Irreducible entry.1 := by
  -- Branch-shape lemma: entry = normalizeFactorSign raw for raw ∈ reassembly.
  obtain ⟨raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_slow_quadratic_branch_raw f B entry hdeg
      hquad hfast_none hentry_mem
  -- Primitivity of squareFreeCore via the Mathlib bridge.
  have hcore_primitive :
      Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore :=
    IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive
        f hf_ne)
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

end HexBerlekampZassenhausMathlib
