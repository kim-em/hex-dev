/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Irreducibility
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.HenselLemmas
public import HexPolyZMathlib.PolynomialEquivalence
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor

public section
set_option backward.proofsInPublic true

/-!
This module collects M1 recovery, the Hensel-lift invariant, and `LiftedFactorSubsetPartition`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-! # M1 (`monicTarget`-coordinate) recovery math

Additive congruence machinery for handling the fast recovery recovery through the van
Hoeij `M1` target `monicTarget core p k = core · ℓf⁻¹ (mod p^k)`
(`Hex.ZPoly.monicTarget`) instead of the `toMonic` `x ↦ x/ℓf` dilation.  Over
`(ℤ/p^k)` the `monicTarget` keeps `core`'s own coordinate, so scaling the lifted
monic product by `ℓf = leadingCoeff core` lands back on `core` directly; no
`dilate`.  These lemmas are the "new math" the original-coordinate swap consumes; they
are stated additively so they land green ahead of that atomic remodel. -/

/-- Constant scaling preserves coefficientwise congruence modulo `m`:
`f ≡ g (mod m) → c·f ≡ c·g (mod m)`. -/
theorem scale_congr_of_congr (c : Int) (f g : Hex.ZPoly) (m : Nat)
    (h : Hex.ZPoly.congr f g m) :
    Hex.ZPoly.congr (Hex.DensePoly.scale c f) (Hex.DensePoly.scale c g) m := by
  intro i
  rw [Hex.DensePoly.coeff_scale c f i (mul_zero c),
      Hex.DensePoly.coeff_scale c g i (mul_zero c)]
  have hdvd : (m : Int) ∣ (f.coeff i - g.coeff i) := Int.dvd_of_emod_eq_zero (h i)
  have hrw : c * f.coeff i - c * g.coeff i = c * (f.coeff i - g.coeff i) := by ring
  rw [hrw]
  exact Int.emod_eq_zero_of_dvd (hdvd.mul_left c)

/-- Scalar multiplications multiply through a polynomial product. -/
theorem scale_mul_scale (a b : Int) (p q : Hex.ZPoly) :
    Hex.DensePoly.scale a p * Hex.DensePoly.scale b q =
      Hex.DensePoly.scale (a * b) (p * q) := by
  rw [← Hex.ZPoly.C_mul_eq_scale, ← Hex.ZPoly.C_mul_eq_scale,
    ← Hex.ZPoly.C_mul_eq_scale]
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
    HexPolyZMathlib.toPolynomial_C, Polynomial.C_mul]
  ring

/-- Scalar multiplications compose. -/
theorem scale_scale (a b : Int) (p : Hex.ZPoly) :
    Hex.DensePoly.scale a (Hex.DensePoly.scale b p) =
      Hex.DensePoly.scale (a * b) p := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_scale (R := Int) a _ n (Int.mul_zero a),
    Hex.DensePoly.coeff_scale (R := Int) b p n (Int.mul_zero b),
    Hex.DensePoly.coeff_scale (R := Int) (a * b) p n
      (Int.mul_zero (a * b)), ← Int.mul_assoc]

/-- Congruent integer scalars produce coefficientwise-congruent scalings. -/
theorem scale_congr_of_modEq
    {a b : Int} {m : Nat} (h : a ≡ b [ZMOD (m : Int)]) (f : Hex.ZPoly) :
    Hex.ZPoly.congr (Hex.DensePoly.scale a f) (Hex.DensePoly.scale b f) m := by
  intro i
  rw [Hex.DensePoly.coeff_scale a f i (Int.mul_zero a),
    Hex.DensePoly.coeff_scale b f i (Int.mul_zero b)]
  rw [show a * f.coeff i - b * f.coeff i = (a - b) * f.coeff i by ring]
  exact Int.emod_eq_zero_of_dvd
    ((Int.modEq_iff_dvd.mp h.symm).mul_right (f.coeff i))

/-- The BHKS `monicTarget` is, coefficientwise modulo `p^k`, the rescaling of
`core` by the modular inverse of its leading coefficient:
`monicTarget core p k ≡ core · ℓf⁻¹ (mod p^k)`.  Immediate from
`monicTarget = reduceModPow (scale ℓf⁻¹ core) p k`. -/
theorem monicTarget_congr_scaleInv (core : Hex.ZPoly) (p k : Nat) (hpk : 0 < p ^ k) :
    Hex.ZPoly.congr (Hex.ZPoly.monicTarget core p k)
      (Hex.DensePoly.scale (Hex.ZPoly.leadingCoeffInverse core p k) core) (p ^ k) :=
  Hex.ZPoly.congr_reduceModPow
    (Hex.DensePoly.scale (Hex.ZPoly.leadingCoeffInverse core p k) core) p k hpk

/--
Multiplication of direct-coordinate monic targets follows multiplication of
their integer polynomials modulo the Hensel modulus.
-/
theorem monicTarget_mul_congr
    {core factor cofactor : Hex.ZPoly} {p k : Nat}
    (hpk : 1 < p ^ k)
    (hproduct : factor * cofactor = core)
    (hlc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor * Hex.DensePoly.leadingCoeff cofactor)
    (hgcd_core :
      Int.gcd (Hex.DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1)
    (hgcd_factor :
      Int.gcd (Hex.DensePoly.leadingCoeff factor) (Int.ofNat (p ^ k)) = 1)
    (hgcd_cofactor :
      Int.gcd (Hex.DensePoly.leadingCoeff cofactor) (Int.ofNat (p ^ k)) = 1) :
    Hex.ZPoly.congr
      (Hex.ZPoly.monicTarget factor p k * Hex.ZPoly.monicTarget cofactor p k)
      (Hex.ZPoly.monicTarget core p k)
      (p ^ k) := by
  let sf := Hex.ZPoly.leadingCoeffInverse factor p k
  let sc := Hex.ZPoly.leadingCoeffInverse cofactor p k
  let s := Hex.ZPoly.leadingCoeffInverse core p k
  let lf := Hex.DensePoly.leadingCoeff factor
  let lc := Hex.DensePoly.leadingCoeff cofactor
  let m : Int := Int.ofNat (p ^ k)
  have hinv (g : Hex.ZPoly)
      (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff g) m = 1) :
      Hex.ZPoly.leadingCoeffInverse g p k * Hex.DensePoly.leadingCoeff g
          ≡ 1 [ZMOD m] := by
    show _ % m = _ % m
    rw [Hex.ZPoly.leadingCoeffInverse_mul_emod g p k hpk hgcd]
    exact (Int.emod_eq_of_lt (by decide) (by
      simpa [m] using Int.ofNat_lt.mpr hpk)).symm
  have hf_inv : sf * lf ≡ 1 [ZMOD m] := hinv factor (by simpa [m] using hgcd_factor)
  have hc_inv : sc * lc ≡ 1 [ZMOD m] := hinv cofactor (by simpa [m] using hgcd_cofactor)
  have hcore_inv : s * (lf * lc) ≡ 1 [ZMOD m] := by
    have := hinv core (by simpa [m] using hgcd_core)
    simpa [s, lf, lc, hlc] using this
  have hpair_inv : (sf * sc) * (lf * lc) ≡ 1 [ZMOD m] := by
    calc
      (sf * sc) * (lf * lc) = (sf * lf) * (sc * lc) := by ring
      _ ≡ 1 * 1 [ZMOD m] := hf_inv.mul hc_inv
      _ = 1 := by ring
  have hscalar : sf * sc ≡ s [ZMOD m] := by
    calc
      sf * sc = (sf * sc) * 1 := by ring
      _ ≡ (sf * sc) * ((lf * lc) * s) [ZMOD m] := by
        have hs : (lf * lc) * s ≡ 1 [ZMOD m] := by
          simpa [mul_comm] using hcore_inv
        exact hs.symm.mul_left (sf * sc)
      _ = ((sf * sc) * (lf * lc)) * s := by ring
      _ ≡ 1 * s [ZMOD m] := hpair_inv.mul_right s
      _ = s := by ring
  have hfactor :=
    monicTarget_congr_scaleInv factor p k (Nat.zero_lt_of_lt hpk)
  have hcofactor :=
    monicTarget_congr_scaleInv cofactor p k (Nat.zero_lt_of_lt hpk)
  have hmul := Hex.ZPoly.congr_mul _ _ _ _ _ hfactor hcofactor
  have hscaled :
      Hex.ZPoly.congr
        (Hex.DensePoly.scale (sf * sc) core)
        (Hex.DensePoly.scale s core) (p ^ k) := by
    exact scale_congr_of_modEq (by simpa [m] using hscalar) core
  exact Hex.ZPoly.congr_trans _ _ _ _
    (by simpa [sf, sc, hproduct, scale_mul_scale] using hmul)
    (Hex.ZPoly.congr_trans _ _ _ _ hscaled
      (Hex.ZPoly.congr_symm _ _ _
        (monicTarget_congr_scaleInv core p k (Nat.zero_lt_of_lt hpk))))

/-- The BHKS mod-correspondence: rescaling the `monicTarget` by `ℓf = leadingCoeff core`
recovers `core` modulo `p^k`, i.e. `ℓf · monicTarget core p k ≡ core (mod p^k)`,
provided `core`'s leading coefficient is coprime to `p^k` (the good-prime
condition).  This is what lets the lifted monic factors of `monicTarget` recover
integer factors of `core` directly in `core`'s own coordinate. -/
theorem leadingCoeff_scale_monicTarget_congr_core (core : Hex.ZPoly) (p k : Nat)
    (hpk : 1 < p ^ k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
        (Hex.ZPoly.monicTarget core p k))
      core (p ^ k) := by
  have hpk_pos : 0 < p ^ k := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hpk)
  -- `ℓ · s ≡ 1 (mod p^k)` from the unit-residue certificate.
  have hsl : (Hex.ZPoly.leadingCoeffInverse core p k
      * Hex.DensePoly.leadingCoeff core) ≡ 1 [ZMOD (↑(p ^ k) : Int)] := by
    have hemod := Hex.ZPoly.leadingCoeffInverse_mul_emod core p k hpk hgcd
    rw [Int.ofNat_eq_natCast] at hemod
    have h1 : (1 : Int) % (↑(p ^ k) : Int) = 1 :=
      Int.emod_eq_of_lt (by decide) (by exact_mod_cast hpk)
    show _ % _ = _ % _
    rw [hemod, h1]
  intro i
  set s := Hex.ZPoly.leadingCoeffInverse core p k with hs
  set ℓ := Hex.DensePoly.leadingCoeff core with hℓ
  set a := core.coeff i with ha
  set m := (↑(p ^ k) : Int) with hm
  -- Compute the `monicTarget` coefficient as a centered residue of `s · a`.
  have hcoeff : (Hex.DensePoly.scale ℓ (Hex.ZPoly.monicTarget core p k)).coeff i
      = ℓ * ((s * a) % m) := by
    rw [Hex.DensePoly.coeff_scale ℓ _ i (mul_zero ℓ)]
    unfold Hex.ZPoly.monicTarget
    rw [Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ p k i hpk_pos,
      Hex.DensePoly.coeff_scale s core i (mul_zero s)]
    rw [Int.ofNat_eq_natCast]
  rw [hcoeff]
  -- `ℓ · ((s·a) % m) ≡ a (mod m)`, hence the congruence subtraction vanishes.
  have hmod : ℓ * ((s * a) % m) ≡ a [ZMOD m] := by
    have hself : ((s * a) % m) ≡ (s * a) [ZMOD m] :=
      Int.emod_emod_of_dvd _ (dvd_refl _)
    calc ℓ * ((s * a) % m)
        ≡ ℓ * (s * a) [ZMOD m] := hself.mul_left ℓ
      _ = (s * ℓ) * a := by ring
      _ ≡ 1 * a [ZMOD m] := hsl.mul_right a
      _ = a := by ring
  have hdvd : m ∣ (ℓ * ((s * a) % m) - a) :=
    (Int.modEq_iff_dvd.mp hmod.symm)
  exact Int.emod_eq_zero_of_dvd hdvd

/-- The original-coordinate scaled-product congruence: given the `M1` lift congruence
`∏ liftedFactors ≡ monicTarget core p k (mod p^k)` for a selected subset `S`,
the `ℓf`-scaled lifted product is congruent to `core` itself modulo `p^k`:
`scaledLiftedFactorProduct core d S ≡ core (mod p^k)`.  This is the precise
hypothesis the existing Mignotte recovery
(`centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision`) consumes,
delivered in `core`'s own coordinate. -/
theorem scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget
    {core : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hpk : 1 < d.p ^ d.k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core) (Int.ofNat (d.p ^ d.k)) = 1)
    (hprod :
      Hex.ZPoly.congr (liftedFactorProduct d S)
        (Hex.ZPoly.monicTarget core d.p d.k) (d.p ^ d.k)) :
    Hex.ZPoly.congr (scaledLiftedFactorProduct core d S) core (d.p ^ d.k) := by
  unfold scaledLiftedFactorProduct
  exact Hex.ZPoly.congr_trans _ _ _ _
    (scale_congr_of_congr (Hex.DensePoly.leadingCoeff core) _ _ _ hprod)
    (leadingCoeff_scale_monicTarget_congr_core core d.p d.k hpk hgcd)

/-- A subset product congruent to a factor's direct monic target recovers that
factor after scaling by its leading coefficient. -/
theorem factorCongr_of_product_congr_monicTarget
    {factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hprod :
      Hex.ZPoly.congr
        (liftedFactorProduct d S)
        (Hex.ZPoly.monicTarget factor d.p d.k)
        (d.p ^ d.k))
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (d.p ^ d.k)) = 1)
    (hpk : 1 < d.p ^ d.k) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff factor)
        (liftedFactorProduct d S))
      factor
      (d.p ^ d.k) := by
  simpa [scaledLiftedFactorProduct] using
    (scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget
      (core := factor) (d := d) (S := S) hpk hgcd hprod)

/-- Scale a factor-coordinate congruence through the leading-coefficient
factorization of the original polynomial. -/
theorem honestCongr_of_correspondence
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (cofactorLc : Int)
    (hlc : Hex.DensePoly.leadingCoeff core =
      Hex.DensePoly.leadingCoeff factor * cofactorLc)
    (hcorr :
      Hex.ZPoly.congr
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff factor)
          (liftedFactorProduct d S))
        factor (d.p ^ d.k)) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
        (liftedFactorProduct d S))
      (Hex.DensePoly.scale cofactorLc factor)
      (d.p ^ d.k) := by
  have hscaled := scale_congr_of_congr cofactorLc _ _ _ hcorr
  rw [scale_scale] at hscaled
  rwa [show cofactorLc * Hex.DensePoly.leadingCoeff factor =
      Hex.DensePoly.leadingCoeff core by rw [hlc]; ring] at hscaled

/-- Compose direct-target recovery with the original polynomial's
leading-coefficient factorization. -/
theorem honestCongr_of_product_congr_monicTarget
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (cofactorLc : Int)
    (hlc : Hex.DensePoly.leadingCoeff core =
      Hex.DensePoly.leadingCoeff factor * cofactorLc)
    (hprod :
      Hex.ZPoly.congr
        (liftedFactorProduct d S)
        (Hex.ZPoly.monicTarget factor d.p d.k)
        (d.p ^ d.k))
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (d.p ^ d.k)) = 1)
    (hpk : 1 < d.p ^ d.k) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
        (liftedFactorProduct d S))
      (Hex.DensePoly.scale cofactorLc factor)
      (d.p ^ d.k) :=
  honestCongr_of_correspondence cofactorLc hlc
    (factorCongr_of_product_congr_monicTarget hprod hgcd hpk)


/--
M1 (`monicTarget`-coordinate) recovery witness, the van Hoeij analogue of
`RecoveredAtLift`.

The selected lifted product represents a monic-coordinate factor `monicFactor`
modulo `p^k`; the integer factor is recovered by scaling that monic factor by
`ℓf = leadingCoeff core` and taking the primitive part of its centred lift; no
`dilate`, because the `monicTarget` coordinate already *is* `core`'s coordinate
(`monicTarget ≡ core·ℓf⁻¹`).  Accordingly `monic_dvd` pins `monicFactor` to a
divisor of `monicTarget core p k` rather than `(toMonic core).monic`.

Stated standalone (a fresh carrier with its own recovery lemma `candidate_eq`)
so it lands green without rerouting any existing `RecoveredAtLift` (M2) consumer.
-/
structure RecoveredAtLiftM1
    (core : Hex.ZPoly) (d : Hex.LiftData) (factor : Hex.ZPoly)
    (S : LiftedFactorSubset d) where
  /-- The direct-coordinate factor represented by the selected lifted factors. -/
  monicFactor : Hex.ZPoly
  /-- The selected lifted product agrees with that factor modulo the lift modulus. -/
  congr :
    Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
      Hex.ZPoly.reduceModPow monicFactor d.p d.k
  /-- Scaling and centred lifting recover the original integer factor. -/
  recovered_eq :
    Hex.ZPoly.primitivePart
        (Hex.centeredLiftPoly
          (Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) monicFactor)
            d.p d.k)
          (d.p ^ d.k)) =
      factor
  /-- The direct-coordinate factor divides the polynomial lifted by Hensel's method. -/
  monic_dvd : monicFactor ∣ Hex.ZPoly.monicTarget core d.p d.k

/-- Recovery formula in `core`'s own coordinate: an `M1` recovery witness recovers
its integer factor as the primitive part of the centred lift of the `ℓf`-scaled
selected lifted product, `primitivePart (centeredLiftPoly ((ℓf · ∏ S) % p^k)) =
factor`.  This is the original-coordinate analogue of
`RecoveredAtLift.candidate_eq_of_monic_dvd`, but with no `dilate`; the proof just
transports the witness `congr` through the `ℓf`-scaling (`scale_congr_of_congr`).
-/
theorem RecoveredAtLiftM1.candidate_eq
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hrec : RecoveredAtLiftM1 core d factor S) (hpk : 0 < d.p ^ d.k) :
    Hex.ZPoly.primitivePart
        (Hex.centeredLiftPoly
          (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
          (d.p ^ d.k)) =
      factor := by
  have hcongr :
      Hex.ZPoly.congr (liftedFactorProduct d S) hrec.monicFactor (d.p ^ d.k) := by
    have hf := Hex.ZPoly.congr_reduceModPow (liftedFactorProduct d S) d.p d.k hpk
    have hg := Hex.ZPoly.congr_reduceModPow hrec.monicFactor d.p d.k hpk
    rw [hrec.congr] at hf
    exact Hex.ZPoly.congr_trans _ _ _ _ (Hex.ZPoly.congr_symm _ _ _ hf) hg
  have hscale_eq :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k
        = Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) hrec.monicFactor)
            d.p d.k := by
    unfold scaledLiftedFactorProduct
    exact Hex.ZPoly.reduceModPow_eq_of_congr _ _ d.p d.k
      (scale_congr_of_congr (Hex.DensePoly.leadingCoeff core) _ _ _ hcongr)
  rw [hscale_eq]
  exact hrec.recovered_eq

/-- A centred lift is coefficientwise congruent to its argument modulo `m`: each
coefficient is the centred representative `centeredModNat`, which differs from the
original by a multiple of `m`. -/
theorem centeredLiftPoly_congr_self (g : Hex.ZPoly) (m : Nat) :
    Hex.ZPoly.congr (Hex.centeredLiftPoly g m) g m := by
  intro i
  rw [Hex.coeff_centeredLiftPoly]
  apply Int.emod_eq_zero_of_dvd
  simpa [neg_sub] using (dvd_neg (α := Int)).mpr (Hex.self_sub_centeredModNat_dvd (g.coeff i) m)


/-! # M1 Hensel lift invariant: `monicTarget` mod-`p` structure transfers from `core`

The fast recovery lift `directLiftData` lifts `core`'s Berlekamp factors against the
`monicTarget`, but the prime is selected against `core`.  Over `ℤ/p` the
`monicTarget` is the unit rescaling `ℓf⁻¹·core`, so it shares its monic modular
image with `core`; the boundary facts the Hensel lift invariant consumes
(`factorsModP` product congruence, monicity, good prime) transfer verbatim. -/

private theorem zmod64_toZMod_injective {p : Nat} [Hex.ZMod64.Bounds p] :
    Function.Injective (HexModArithMathlib.ZMod64.toZMod (p := p)) := by
  intro x y h
  rw [← HexModArithMathlib.ZMod64.ofZMod_toZMod x,
    ← HexModArithMathlib.ZMod64.ofZMod_toZMod y, h]

/-- Coprimality with `p ^ k` makes the integer leading coefficient nonzero
in the prime field at `p`. -/
theorem leadingCoeffAdmissible_of_gcd_pow
    (core : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p)
    (hpk : 1 < p ^ k) (hk : 0 < k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (p ^ k)) = 1) :
    Hex.leadingCoeffAdmissible core p := by
  letI : Fact (_root_.Nat.Prime p) := ⟨natPrime_of_hexNatPrime hprime⟩
  have hs_inv :
      (Hex.ZPoly.leadingCoeffInverse core p k *
          Hex.DensePoly.leadingCoeff core) %
        Int.ofNat (p ^ k) = 1 :=
    Hex.ZPoly.leadingCoeffInverse_mul_emod core p k hpk hgcd
  have hmod_pk :
      (Hex.ZPoly.leadingCoeffInverse core p k *
          Hex.DensePoly.leadingCoeff core) ≡ 1
        [ZMOD Int.ofNat (p ^ k)] := by
    show _ % _ = _ % _
    rw [hs_inv]
    exact (Int.emod_eq_of_lt (by decide) (Int.ofNat_lt.mpr hpk)).symm
  have hp_dvd : (p : Int) ∣ Int.ofNat (p ^ k) := by
    rw [Int.ofNat_eq_natCast]
    exact_mod_cast dvd_pow_self p hk.ne'
  have hmod_p := hmod_pk.of_dvd hp_dvd
  have hunit :
      ((Hex.ZPoly.leadingCoeffInverse core p k : Int) : ZMod p) *
          ((Hex.DensePoly.leadingCoeff core : Int) : ZMod p) = 1 := by
    rw [← Int.cast_mul]
    simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod_p
  have hlc_ne :
      ((Hex.DensePoly.leadingCoeff core : Int) : ZMod p) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hunit
    exact zero_ne_one hunit
  unfold Hex.leadingCoeffAdmissible Hex.ZPoly.leadingCoeffModP
  intro hzero
  apply hlc_ne
  have hz := congrArg
    (HexModArithMathlib.ZMod64.toZMod (p := p)) hzero
  rw [HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast,
    HexModArithMathlib.ZMod64.toZMod_zero] at hz
  exact hz

/-- Reduction modulo `p` of an integer rescaling: the integer scalar reduces to
its `ZMod64 p` image, `modP p (scale c f) = scale (↑c) (modP p f)`. -/
theorem modP_scale_intCast {p : Nat} [Hex.ZMod64.Bounds p] (c : Int) (f : Hex.ZPoly) :
    Hex.ZPoly.modP p (Hex.DensePoly.scale c f) =
      Hex.DensePoly.scale ((c : Hex.ZMod64 p)) (Hex.ZPoly.modP p f) := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [Hex.ZPoly.coeff_modP,
    Hex.DensePoly.coeff_scale c f i (Int.mul_zero c),
    Hex.DensePoly.coeff_scale ((c : Hex.ZMod64 p)) (Hex.ZPoly.modP p f) i
      (Lean.Grind.Semiring.mul_zero _),
    Hex.ZPoly.coeff_modP]
  apply zmod64_toZMod_injective
  rw [HexModArithMathlib.ZMod64.toZMod_mul,
    HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast,
    HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast,
    HexModArithMathlib.ZMod64.toZMod_intCast]
  push_cast
  ring

/-- The BHKS `monicTarget` reduces mod `p` to the monic modular image of `core`.
Both are the monic mod-`p` factor pattern of `core`; the `monicTarget` realises it
as an honest reduction (`ℓf⁻¹·core ≡ monicModularImage (modP p core)`), provided
the prime is good for `core` and `ℓf` is coprime to `p^k`. -/
theorem monicModularImage_modP_eq_modP_monicTarget
    (core : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p)
    (hpk : 1 < p ^ k) (hk : 0 < k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core) (Int.ofNat (p ^ k)) = 1) :
    Hex.monicModularImage (Hex.ZPoly.modP p core) =
      Hex.ZPoly.modP p (Hex.ZPoly.monicTarget core p k) := by
  haveI : Fact (_root_.Nat.Prime p) := ⟨natPrime_of_hexNatPrime hprime⟩
  have hadm : Hex.leadingCoeffAdmissible core p :=
    leadingCoeffAdmissible_of_gcd_pow core p k hprime hpk hk hgcd
  have hsize : 0 < (Hex.ZPoly.modP p core).size := by
    rw [Hex.size_modP_eq_of_leadingCoeffAdmissible core p hadm]
    exact Hex.leadingCoeffAdmissible_size_pos core p hadm
  have hzero : (Hex.ZPoly.modP p core).isZero = false :=
    (Hex.DensePoly.isZero_eq_false_iff _).mpr hsize
  set s := Hex.ZPoly.leadingCoeffInverse core p k with hs
  set ℓf := Hex.DensePoly.leadingCoeff core with hℓf
  set a := Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP p core) with ha
  -- RHS as a scaling of `modP p core`.
  have hrhs : Hex.ZPoly.modP p (Hex.ZPoly.monicTarget core p k) =
      Hex.DensePoly.scale ((s : Hex.ZMod64 p)) (Hex.ZPoly.modP p core) := by
    unfold Hex.ZPoly.monicTarget
    rw [Hex.ZPoly.modP_reduceModPow_of_pos p k _ hk, modP_scale_intCast]
  -- LHS as a scaling of `modP p core`.
  have hlhs : Hex.monicModularImage (Hex.ZPoly.modP p core) =
      Hex.DensePoly.scale (a⁻¹) (Hex.ZPoly.modP p core) :=
    monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hzero
  rw [hlhs, hrhs]
  -- It remains to identify the scalars in `ZMod64 p`.
  have ha_ne : a ≠ 0 := by
    rw [ha, Hex.leadingCoeff_modP_eq_leadingCoeffModP_of_admissible core p hadm]
    exact hadm
  -- `a = ↑ℓf` in `ZMod64 p`.
  have ha_eq : a = ((ℓf : Int) : Hex.ZMod64 p) := by
    apply zmod64_toZMod_injective
    rw [ha, Hex.leadingCoeff_modP_eq_leadingCoeffModP_of_admissible core p hadm,
      Hex.ZPoly.leadingCoeffModP,
      HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast,
      HexModArithMathlib.ZMod64.toZMod_intCast]
  -- `ℓf · s ≡ 1 (mod p)` in the field `ZMod p`.
  have hsl_zmod : ((ℓf : Int) : ZMod p) * ((s : Int) : ZMod p) = 1 := by
    have hbez : (s * ℓf) % (Int.ofNat (p ^ k)) = 1 :=
      Hex.ZPoly.leadingCoeffInverse_mul_emod core p k hpk hgcd
    have hmod : (s * ℓf) ≡ 1 [ZMOD (Int.ofNat (p ^ k))] := by
      unfold Int.ModEq
      rw [hbez, Int.emod_eq_of_lt (by decide) (by simpa using Int.ofNat_lt.mpr hpk)]
    have hdvd_pk : ((p : Int)) ∣ (Int.ofNat (p ^ k)) := by
      rw [Int.ofNat_eq_natCast]
      exact_mod_cast dvd_pow_self p hk.ne'
    have hmod_p : (s * ℓf) ≡ 1 [ZMOD (p : Int)] := hmod.of_dvd hdvd_pk
    have hcast : ((s * ℓf : Int) : ZMod p) = 1 := by
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod_p, Int.cast_one]
    rw [mul_comm, ← Int.cast_mul]
    exact hcast
  -- Hence `a⁻¹ = ↑s` in `ZMod64 p`, via the field `ZMod p`.
  have hscalar : a⁻¹ = ((s : Int) : Hex.ZMod64 p) := by
    apply zmod64_toZMod_injective
    have hinv_z : HexModArithMathlib.ZMod64.toZMod (a⁻¹) =
        (HexModArithMathlib.ZMod64.toZMod a)⁻¹ := by
      have hmul1 : HexModArithMathlib.ZMod64.toZMod a *
          HexModArithMathlib.ZMod64.toZMod (a⁻¹) = 1 := by
        rw [← HexModArithMathlib.ZMod64.toZMod_mul]
        have hia : a * a⁻¹ = 1 := Hex.ZMod64.mul_inv_eq_one_of_prime hprime ha_ne
        rw [hia, HexModArithMathlib.ZMod64.toZMod_one]
      exact eq_inv_of_mul_eq_one_right hmul1
    rw [hinv_z, HexModArithMathlib.ZMod64.toZMod_intCast]
    -- `(toZMod a)⁻¹ = ↑s`, since `↑ℓf · ↑s = 1` and `toZMod a = ↑ℓf`.
    have ha_zmod : HexModArithMathlib.ZMod64.toZMod a = ((ℓf : Int) : ZMod p) := by
      rw [ha_eq, HexModArithMathlib.ZMod64.toZMod_intCast]
    rw [ha_zmod]
    exact (eq_inv_of_mul_eq_one_right hsl_zmod).symm
  rw [hscalar]

/--
Abstract-bound variant of
`existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the input-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors
the original but invokes the `_of_bound` recovery theorem instead of
the input-shape one.
-/
theorem existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (B' : Nat)
    (hvalid :
      ∀ {S : LiftedFactorSubset d} (hrec : RecoveredAtLift core d factor S),
        ∀ i, (hrec.monicFactor.coeff i).natAbs ≤ B')
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∃! S : LiftedFactorSubset d,
      ∃ _hrec : RecoveredAtLift core d factor S,
        liftedRecoveryCandidate core d S = factor := by
  rcases h.exists_subset hfactor_norm hirr hdvd with ⟨S, hS⟩
  rcases hS with ⟨hrecS⟩
  refine ⟨S, ⟨hrecS, ?_⟩, ?_⟩
  · exact
      RecoveredAtLift.candidate_eq_of_bound
        hrecS B' (hvalid hrecS) hfactor_norm hprecision
  · intro T hT
    rcases hT with ⟨hrecT, _hT_recovered⟩
    exact
      (h.unique_subset (factor := factor) (S := S) (T := T)
        hirr hdvd (RepresentsIntegerFactorAtLift.ofRecovered hrecS)
        (RepresentsIntegerFactorAtLift.ofRecovered hrecT)).symm

/--
Group A2 packaged for downstream exhaustive-search proofs: under the Hensel
subset-correspondence hypotheses, each irreducible integer factor has a unique
lifted-factor subset whose recovered-coordinate candidate equals the factor
exactly at Mignotte precision.

This is a thin wrapper over
`existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core`.  The coefficient bound
is explicitly about the hidden monic-coordinate witness exposed by the
`RecoveredAtLift` carrier.
-/
theorem existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hvalid :
      ∀ {S : LiftedFactorSubset d} (hrec : RecoveredAtLift core d factor S),
        ∀ i,
          (hrec.monicFactor.coeff i).natAbs ≤
            Hex.ZPoly.defaultFactorCoeffBound core)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∃! S : LiftedFactorSubset d,
      ∃ _hrec : RecoveredAtLift core d factor S,
        liftedRecoveryCandidate core d S = factor :=
  existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound
    h (Hex.ZPoly.defaultFactorCoeffBound core)
    hvalid hfactor_norm hirr hdvd hprecision


/--
Induced subset-correspondence predicate for the recursive state of the
exhaustive recombination search.

After the search consumes a prefix of subsets, it recurses on a `target`
polynomial (a quotient of `core` by the factors emitted so far) with a reduced
index set `J ⊆ Finset.univ` of lifted-factor indices not yet selected.  This
predicate packages the correspondence between irreducible integer divisors of
`target` and their representing lifted-factor subsets, constrained to live in
`J`.

When `target = core` and `J = Finset.univ`, this reduces to the existence and
uniqueness fields of `HenselSubsetCorrespondenceHypotheses`.  Downstream
coverage proofs use the predicate to track the recursive state across one
emission step at a time.
-/
structure HenselSubsetCorrespondenceRest
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (J : LiftedFactorSubset d) (target : Hex.ZPoly) : Prop where
  /-- Every normalized irreducible divisor has a representing subset inside `J`. -/
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Hex.normalizeFactorSign factor = factor →
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ S : LiftedFactorSubset d,
        S ⊆ J ∧ RepresentsIntegerFactorAtLift core d factor S
  /-- An irreducible divisor has at most one representing subset inside `J`. -/
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      S ⊆ J →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d factor S →
      RepresentsIntegerFactorAtLift core d factor T →
      S = T

/--
Initial-state lemma: a Hensel subset correspondence implies the induced
predicate at the full universe of lifted-factor indices with `target = core`.
This is the entry point for downstream recursive-search coverage proofs.
-/
theorem henselSubsetCorrespondenceRest_initial
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift) :
    HenselSubsetCorrespondenceRest core d Finset.univ core where
  exists_subset := by
    intro factor hsign hirr hdvd
    rcases h.exists_subset hsign hirr hdvd with ⟨S, hS⟩
    exact ⟨S, Finset.subset_univ S, hS⟩
  unique_subset := by
    intro factor S T hirr hdvd _hS_in _hT_in hS hT
    exact h.unique_subset hirr hdvd hS hT


/-- Transitivity of `Hex.ZPoly`-level divisibility. Discharges the
`core = g * (q * v)` step explicitly via `Hex.DensePoly.mul_assoc_poly`
because `Hex.ZPoly` does not synthesise a Mathlib `Semigroup` instance
at this layer. -/
private theorem zpoly_dvd_trans
    {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨q * v, ?_⟩
  rw [hv, hq]
  exact Hex.DensePoly.mul_assoc_poly (S := Int) _ _ _

/-- A polynomial factor with nonnegative leading coefficient is a fixed point of
`Hex.normalizeFactorSign`. -/
theorem normalizeFactorSign_eq_self_of_leadingCoeff_nonneg (g : Hex.ZPoly)
    (h : 0 ≤ Hex.DensePoly.leadingCoeff g) :
    Hex.normalizeFactorSign g = g := by
  unfold Hex.normalizeFactorSign
  rw [ite_eq_right (by omega : ¬ Hex.DensePoly.leadingCoeff g < 0)]


/--
Transport an induced Hensel subset correspondence through one emitted
recombination factor.

The emitted subset `S` is removed from the remaining index set.  The only
non-structural obligation is the expected disjointness fact: every irreducible
divisor of the quotient must be represented by a subset disjoint from the
emitted subset.  Later coverage proofs discharge that from square-free
factorisation/associatedness; this lemma packages the pure rest-state transport
and reuses the parent state's uniqueness field.
-/
theorem henselSubsetCorrespondenceRest_transport_of_disjoint
    {core target quotient emitted : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (h : HenselSubsetCorrespondenceRest core d J target)
    (hquot : quotient * emitted = target)
    (hdisjoint :
      ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ quotient →
        T ⊆ J →
        RepresentsIntegerFactorAtLift core d factor T →
        Disjoint T S) :
    HenselSubsetCorrespondenceRest core d (J \ S) quotient where
  exists_subset := by
    intro factor hsign hirr hdvd_quot
    have hdvd_target : factor ∣ target :=
      zpoly_dvd_trans hdvd_quot ⟨emitted, hquot.symm⟩
    rcases h.exists_subset hsign hirr hdvd_target with ⟨T, hTJ, hTrep⟩
    have hTS : Disjoint T S := hdisjoint hirr hdvd_quot hTJ hTrep
    refine ⟨T, ?_, hTrep⟩
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hTJ hi, fun hiS => (Finset.disjoint_left.mp hTS) hi hiS⟩
  unique_subset := by
    intro factor T U hirr hdvd_quot hTJU hUJU hTrep hUrep
    have hdvd_target : factor ∣ target :=
      zpoly_dvd_trans hdvd_quot ⟨emitted, hquot.symm⟩
    apply h.unique_subset hirr hdvd_target
    · intro i hi
      exact (Finset.mem_sdiff.mp (hTJU hi)).1
    · intro i hi
      exact (Finset.mem_sdiff.mp (hUJU hi)).1
    · exact hTrep
    · exact hUrep

/--
Strengthened rest predicate that augments `HenselSubsetCorrespondenceRest`
with the structural facts needed by the recursive-coverage proof:
square-freeness of `target` in `Polynomial ℤ`, a cover field saying every
remaining index lies in *some* representing subset, a pairwise-disjoint
field for non-associated irreducible divisors, and a uniqueness-up-to-
association field saying associated irreducible divisors of `target` share
their representing subset.

The doc-comment on `henselSubsetCorrespondenceRest_transport_of_disjoint`
flags the disjointness obligation as "discharged from square-free
factorisation by later coverage proofs"; this predicate packages exactly
that information.

The predicate is designed to transport through one emitted recombination
factor.
-/
structure LiftedFactorSubsetPartition
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (J : LiftedFactorSubset d) (target : Hex.ZPoly) : Prop
    extends HenselSubsetCorrespondenceRest core d J target where
  /-- The current target has no repeated irreducible factors. -/
  target_squarefree : Squarefree (HexPolyZMathlib.toPolynomial target)
  /-- Every remaining lifted factor belongs to an irreducible divisor of the target. -/
  cover :
    ∀ {i : LiftedFactorIndex d}, i ∈ J →
      ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
        Irreducible (HexPolyZMathlib.toPolynomial f) ∧
        f ∣ target ∧
        S ⊆ J ∧ i ∈ S ∧
        RepresentsIntegerFactorAtLift core d f S
  /-- Nonassociated irreducible factors have disjoint lifted supports. -/
  pairwise_disjoint :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d g T →
      ¬ Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      Disjoint S T
  /-- Associated irreducible factors have the same lifted support. -/
  unique_up_to_associated :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d g T →
      Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      S = T
  /-- Divisibility of a direct recombination candidate implies support inclusion. -/
  support_subset_of_dvd_recombinationCandidate :
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      T ⊆ J →
      Hex.DensePoly.leadingCoeff core = 1 →
      f ∣ liftedFactorProductCandidate d T →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      S ⊆ T
  /-- Divisibility of a recovered candidate implies support inclusion. -/
  support_subset_of_dvd_liftedRecoveryCandidate :
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      T ⊆ J →
      f ∣ liftedRecoveryCandidate core d T →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      S ⊆ T
  /-- Recovery from a genuine support returns its represented factor. -/
  liftedRecoveryCandidate_eq :
    ∀ {f : Hex.ZPoly} {S : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      liftedRecoveryCandidate core d S = f

/--
The lifted-index supports corresponding to irreducible integer divisors of
`core`, represented at the Hensel lift by `RepresentsIntegerFactorAtLift`.

This is the concrete `trueSupports` family used by the BHKS support-partition
counting step: the executable representation is a `Finset`, while the lattice
side consumes supports as sets of lifted-factor indices.

The accompanying partition lemmas specialize to the full lifted-index universe
`J = Finset.univ`; proper recursive rest partitions keep their remaining-index
guard outside this support family.
-/
@[expose]
def liftedTrueSupports (core : Hex.ZPoly) (d : Hex.LiftData) :
    Set (Set (LiftedFactorIndex d)) :=
  fun U =>
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
        f ∣ core ∧
          RepresentsIntegerFactorAtLift core d f S ∧
            (↑S : Set (LiftedFactorIndex d)) = U

namespace liftedTrueSupports


end liftedTrueSupports


end

end HexBerlekampZassenhausMathlib
