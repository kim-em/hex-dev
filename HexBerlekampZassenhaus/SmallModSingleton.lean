/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Basic
public import HexBerlekamp.RabinSoundness

public section

/-!
Small-mod singleton Berlekamp irreducibility wrapper.

This module composes the modular Berlekamp soundness chain from
`HexBerlekamp.RabinSoundness` with the executable prime-selection data
maintained by `HexBerlekampZassenhaus.Basic` to expose a Mathlib-free
`Hex.FpPoly.Irreducible` witness for the monic modular image of a
`choosePrimeData?` selection whose Berlekamp factor count is at most one.

The composition rests on three pieces:

* `choosePrimeData?_isGoodPrime` certifies that the selected prime is
  good for the input, in particular giving the modular square-free
  invariant `DensePoly.gcd (modP p core) (derivative (modP p core)) = 1`.
* The relaxed Berlekamp soundness theorem
  `Hex.Berlekamp.berlekampFactor_singleton_irreducible` consumes a
  common-divisor predicate, not the strict executable-gcd identity that
  would fail on the non-monic-normalised `monicModularImage`.
* A small unit-scaling argument shows that any common divisor of
  `monicModularImage (modP p core)` and its derivative is also a common
  divisor of `modP p core` and its derivative, so the square-free
  invariant transports to the relaxed Berlekamp precondition for the
  monic modular image.
-/

namespace Hex

namespace BerlekampZassenhaus

namespace SmallModSingleton

variable {p : Nat} [ZMod64.Bounds p]

private theorem derivative_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.derivative (DensePoly.scale c f) =
      DensePoly.scale c (DensePoly.derivative f) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_d : ((n + 1 : Nat) : ZMod64 p) * (Zero.zero : ZMod64 p) =
      (Zero.zero : ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  have hzero_s : c * (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  rw [DensePoly.coeff_derivative _ _ hzero_d,
      DensePoly.coeff_scale c (DensePoly.derivative f) n hzero_s,
      DensePoly.coeff_derivative _ _ hzero_d,
      DensePoly.coeff_scale c f (n + 1) hzero_s]
  -- Goal: ((n+1) : ZMod64 p) * (c * f.coeff (n+1)) = c * (((n+1) : ZMod64 p) * f.coeff (n+1))
  grind

private theorem dvd_trans_FpPoly {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly a x y

/--
Common divisors of `monicModularImage (modP p core)` and its derivative
are unit polynomials.

This is the relaxed Berlekamp soundness precondition for the small-mod
singleton wrapper.  Strategy: `monicModularImage r = scale c⁻¹ r` for the
unit `c⁻¹ = (leadingCoeff r)⁻¹`, where `leadingCoeff r ≠ 0` follows from
the `isGoodPrime` leading-coefficient admissibility; the derivative of a
unit scaling is a unit scaling of the derivative, and divisibility is
preserved under unit scaling, so a common divisor of the monic image and
its derivative is also a common divisor of `r = modP p core` and its
derivative, where the `isGoodPrime` square-free invariant kicks in.
-/
theorem common_dvd_one_of_isGoodPrime_monicModularImage
    (core : Hex.ZPoly) (hprime : Hex.Nat.Prime p)
    (hgood : isGoodPrime core p = true) :
    ∀ g, g ∣ monicModularImage (Hex.ZPoly.modP p core) →
         g ∣ DensePoly.derivative (monicModularImage (Hex.ZPoly.modP p core)) →
         Hex.Berlekamp.isUnitPolynomial g = true := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hprime
  intro g hg_mmi hg_dmmi
  have hzero : (Hex.ZPoly.modP p core).isZero = false :=
    isGoodPrime_modP_isZero_false core p hgood
  -- Abbreviate the modular image as `r`.
  let r : FpPoly p := Hex.ZPoly.modP p core
  have hr_size_pos : 0 < r.size :=
    (DensePoly.isZero_eq_false_iff r).1 hzero
  have hlead_ne : DensePoly.leadingCoeff r ≠ (0 : ZMod64 p) := by
    rw [FpPoly.leadingCoeff_eq_coeff_pred r hr_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size r hr_size_pos
  have hcinv_ne : (DensePoly.leadingCoeff r)⁻¹ ≠ (0 : ZMod64 p) :=
    ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  -- Rewrite `monicModularImage r` as `scale c⁻¹ r` using the nonzero branch.
  have hmmi_eq :
      monicModularImage r = DensePoly.scale (DensePoly.leadingCoeff r)⁻¹ r := by
    unfold monicModularImage
    rw [show r.isZero = false from hzero]; rfl
  rw [hmmi_eq] at hg_mmi
  rw [hmmi_eq, derivative_scale] at hg_dmmi
  have hscale_dvd_r :
      DensePoly.scale (DensePoly.leadingCoeff r)⁻¹ r ∣ r :=
    FpPoly.dvd_scale_self_of_ne_zero hcinv_ne r
  have hscale_dvd_dr :
      DensePoly.scale (DensePoly.leadingCoeff r)⁻¹ (DensePoly.derivative r) ∣
        DensePoly.derivative r :=
    FpPoly.dvd_scale_self_of_ne_zero hcinv_ne (DensePoly.derivative r)
  have hg_r : g ∣ r := dvd_trans_FpPoly hg_mmi hscale_dvd_r
  have hg_dr : g ∣ DensePoly.derivative r :=
    dvd_trans_FpPoly hg_dmmi hscale_dvd_dr
  have hgcd_unit :
      Hex.Berlekamp.isUnitPolynomial (DensePoly.gcd r (DensePoly.derivative r)) = true := by
    have hsq : squareFreeModP core p := isGoodPrime_squareFreeModP core p hgood
    unfold squareFreeModP at hsq
    change gcdIsUnit (DensePoly.gcd r (DensePoly.derivative r)) = true at hsq
    unfold gcdIsUnit at hsq
    have hsize : (DensePoly.gcd r (DensePoly.derivative r)).size = 1 := by
      simpa using (beq_iff_eq.mp hsq)
    unfold Hex.Berlekamp.isUnitPolynomial
    have hpos : 0 < (DensePoly.gcd r (DensePoly.derivative r)).size := by omega
    rw [DensePoly.degree?_eq_some_of_pos_size _ hpos, hsize]
    rfl
  exact Hex.Berlekamp.isUnitPolynomial_of_dvd_gcd_isUnit hg_r hg_dr hgcd_unit

/--
For a `choosePrimeData?` selection whose Berlekamp factor count is at
most one, the monic modular image of the input at the selected prime is
irreducible as an `FpPoly`.

Composes `choosePrimeData?_berlekampFactor_factors_length_le_one_of_small`
(the shape fact) with the relaxed Berlekamp soundness theorem
`Hex.Berlekamp.berlekampFactor_singleton_irreducible`, using the
`isGoodPrime` invariants maintained by the prime selection to discharge
the relaxed common-divisor precondition through
`common_dvd_one_of_isGoodPrime_monicModularImage`.
-/
theorem monicModularImage_modP_irreducible_of_choosePrimeData?_small
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1) :
    letI := primeData.bounds
    Hex.FpPoly.Irreducible
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) := by
  letI : ZMod64.Bounds primeData.p := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  letI : ZMod64.PrimeModulus primeData.p :=
    ZMod64.primeModulusOfPrime hprime
  have hgood : isGoodPrime core primeData.p = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  obtain ⟨hzero, hlen⟩ :=
    Hex.choosePrimeData?_berlekampFactor_factors_length_le_one_of_small
      core primeData hselected hsmall
  have hmonic :
      DensePoly.Monic
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  have hcommon := common_dvd_one_of_isGoodPrime_monicModularImage
    (p := primeData.p) core hprime hgood
  exact Hex.Berlekamp.berlekampFactor_singleton_irreducible
    (p := primeData.p)
    (f := Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
    hmonic hcommon hlen

/--
A factor of a primitive `ZPoly` product is itself primitive: `content (p * q) = 1`
together with non-negativity of integer content forces `content p = 1`.

Used to discharge the `ZPoly.Primitive core` precondition of
`Irreducible_of_modP_irreducible_of_primitive_of_admissible` from the
`primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive` invariant. -/
private theorem ZPoly_Primitive_left_of_mul (p q : Hex.ZPoly)
    (h : Hex.ZPoly.Primitive (p * q)) : Hex.ZPoly.Primitive p := by
  have hone : Hex.ZPoly.content p * Hex.ZPoly.content q = 1 := by
    rw [← Hex.ZPoly.content_mul]
    exact h
  have hp_nn : 0 ≤ Hex.ZPoly.content p := by
    show 0 ≤ Hex.DensePoly.content p
    rw [Hex.DensePoly.content]
    exact Int.natCast_nonneg _
  have hdvd : Hex.ZPoly.content p ∣ (1 : Int) := ⟨Hex.ZPoly.content q, hone.symm⟩
  have habs : (Hex.ZPoly.content p).natAbs ∣ (1 : Nat) := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have habs_le : (Hex.ZPoly.content p).natAbs ≤ 1 := Nat.le_of_dvd (by omega) habs
  have hp_ne : Hex.ZPoly.content p ≠ 0 := by
    intro hzero
    rw [hzero, Int.zero_mul] at hone
    omega
  have habs_pos : 1 ≤ (Hex.ZPoly.content p).natAbs := by
    rcases Nat.eq_zero_or_pos (Hex.ZPoly.content p).natAbs with hz | hp
    · exact absurd (Int.natAbs_eq_zero.mp hz) hp_ne
    · exact hp
  have habs_eq : (Hex.ZPoly.content p).natAbs = 1 := by omega
  show Hex.ZPoly.content p = 1
  rcases Int.natAbs_eq (Hex.ZPoly.content p) with heq | heq
  · rw [heq, habs_eq]; rfl
  · rw [heq, habs_eq] at hp_nn
    omega

/--
Generic core-level small-mod singleton irreducibility lemma: given a primitive
`ZPoly` whose `degree` is positive, a `choosePrimeData?` success witness, and a
singleton-bounded Berlekamp factor count, the core is `ZPoly.Irreducible`.

Composes
`monicModularImage_modP_irreducible_of_choosePrimeData?_small`
(`FpPoly`-irreducibility of the monic modular image at the selected good prime)
with the Gauss reduction-mod-`p` transfer
`Hex.ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible`
via `FpPoly.irreducible_of_scale_of_ne_zero` applied to the unit-scaling
equation `monicModularImage r = scale (leadingCoeff r)⁻¹ r`. -/
private theorem zpoly_irreducible_of_choosePrimeData?_small_of_primitive
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hprim : Hex.ZPoly.Primitive core)
    (hsize_gt_one : 1 < core.size) :
    Hex.ZPoly.Irreducible core := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  -- Standard prime/admissibility chain.
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hchoose
  have hgood : Hex.isGoodPrime core primeData.p = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hchoose
  have hadm : Hex.leadingCoeffAdmissible core primeData.p :=
    Hex.isGoodPrime_leadingCoeffAdmissible core primeData.p hgood
  -- `FpPoly.Irreducible (monicModularImage (modP p core))` from the singleton lemma.
  have hirr_monic :
      Hex.FpPoly.Irreducible
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    monicModularImage_modP_irreducible_of_choosePrimeData?_small
      core primeData hchoose hsmall
  -- Transfer to `FpPoly.Irreducible (modP p core)` via the unit-scale equation.
  have hisZero : (Hex.ZPoly.modP primeData.p core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hr_size_pos : 0 < (Hex.ZPoly.modP primeData.p core).size := by
    rcases Nat.eq_zero_or_pos (Hex.ZPoly.modP primeData.p core).size with hsz | hsz
    · exfalso
      have hisz : (Hex.ZPoly.modP primeData.p core).isZero = true := by
        simpa [Hex.DensePoly.isZero, Hex.DensePoly.size,
          Array.isEmpty_iff_size_eq_zero] using hsz
      rw [hisz] at hisZero
      contradiction
    · exact hsz
  have hlead_ne :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core) ≠
        (0 : Hex.ZMod64 primeData.p) := by
    rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred _ hr_size_pos]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size _ hr_size_pos
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹ ≠
        (0 : Hex.ZMod64 primeData.p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  have hmmi_eq :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) =
        Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹
          (Hex.ZPoly.modP primeData.p core) := by
    unfold Hex.monicModularImage
    rw [show (Hex.ZPoly.modP primeData.p core).isZero = false from hisZero]
    rfl
  rw [hmmi_eq] at hirr_monic
  have hirr_modP : Hex.FpPoly.Irreducible (Hex.ZPoly.modP primeData.p core) :=
    Hex.FpPoly.irreducible_of_scale_of_ne_zero hinv_ne hirr_monic
  -- Apply the Gauss reduction-mod-`p` transfer.
  exact Hex.ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible
    core primeData.p hprime hprim hadm hsize_gt_one hirr_modP

/--
Small-mod singleton branch irreducibility for the square-free core of
`Hex.normalizeForFactor f`, packaged Mathlib-free.

Composes
`monicModularImage_modP_irreducible_of_choosePrimeData?_small`
(`FpPoly`-irreducibility of the monic modular image at the selected good prime)
with the Gauss reduction-mod-`p` transfer
`Hex.ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible`
to lift `Hex.ZPoly.Irreducible` from the modular image back to the
square-free core.

Side conditions discharged internally:

* `Hex.ZPoly.Primitive core` from the
  `primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`
  invariant on `(extractXPower (primitivePart f)).core`.
* `leadingCoeffAdmissible core primeData.p` from
  `choosePrimeData?_isGoodPrime` and `isGoodPrime_leadingCoeffAdmissible`.
* `1 < core.size` from `hdeg` (non-constancy marker also used by the capstone
  caller to dispatch into this branch).

This is the Mathlib-free analog of
`IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP`
in `HexBerlekampZassenhausMathlib/IntReductionMod.lean`. -/
theorem squareFreeCore_irreducible_of_small_mod_singleton
    (f : Hex.ZPoly) (hf_ne : f ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1)
    (hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  -- `1 < core.size` from `hdeg`.
  have hcore_size_gt_one : 1 < (Hex.normalizeForFactor f).squareFreeCore.size := by
    rcases Nat.lt_or_ge 1 (Hex.normalizeForFactor f).squareFreeCore.size with h | hle
    · exact h
    · exfalso
      apply hdeg
      show (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
      unfold Hex.DensePoly.degree?
      by_cases hz : (Hex.normalizeForFactor f).squareFreeCore.size = 0
      · simp [hz]
      · simp [hz]
        omega
  -- `ZPoly.Primitive ((normalizeForFactor f).squareFreeCore)` from
  -- `primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`.
  have hprim_core : Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore := by
    have hxcore_ne :
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core ≠ 0 :=
      Hex.extractXPower_core_ne_zero_of_ne_zero f hf_ne
    have hprod :=
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core hxcore_ne
    -- `(normalizeForFactor f).squareFreeCore =
    --   (primitiveSquareFreeDecomposition xCore).squareFreeCore` by definition.
    have hcore_eq :
        (Hex.normalizeForFactor f).squareFreeCore =
          (Hex.ZPoly.primitiveSquareFreeDecomposition
              (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core).squareFreeCore :=
      rfl
    rw [hcore_eq]
    exact ZPoly_Primitive_left_of_mul _ _ hprod
  exact zpoly_irreducible_of_choosePrimeData?_small_of_primitive _ primeData hchoose hsmall
    hprim_core hcore_size_gt_one

end SmallModSingleton

end BerlekampZassenhaus

end Hex
