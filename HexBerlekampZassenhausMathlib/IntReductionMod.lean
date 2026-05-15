import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampMathlib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Irreducible

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

end IntReductionMod

end HexBerlekampZassenhausMathlib
