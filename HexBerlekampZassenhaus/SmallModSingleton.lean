import HexBerlekampZassenhaus.Basic
import HexBerlekamp.RabinSoundness

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
  have hsf : DensePoly.gcd r (DensePoly.derivative r) = 1 :=
    isGoodPrime_squareFreeModP core p hgood
  exact Hex.Berlekamp.squareFree_common_of_gcd_eq_one hsf g hg_r hg_dr

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

end SmallModSingleton

end BerlekampZassenhaus

end Hex
