/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.PublicSurface

public section
set_option backward.proofsInPublic true

/-!
This module collects `modPFactor`/`monicModPImage` and `ModPSubsetPartitionHypotheses`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Index type for the modular factors stored in executable prime-choice data. -/
abbrev ModPFactorIndex (primeData : Hex.PrimeChoiceData) : Type :=
  Fin primeData.factorsModP.size

/-- A finite subset of the modular factors stored in executable prime-choice data. -/
abbrev ModPFactorSubset (primeData : Hex.PrimeChoiceData) : Type :=
  Finset (ModPFactorIndex primeData)

/-- The selected modular factor at an executable `PrimeChoiceData` index. -/
def modPFactor (primeData : Hex.PrimeChoiceData)
    (i : ModPFactorIndex primeData) : @Hex.FpPoly primeData.p primeData.bounds :=
  primeData.factorsModP[i]

/-- Product of the selected modular factors. -/
def modPFactorProduct
    (primeData : Hex.PrimeChoiceData) (S : ModPFactorSubset primeData) :
    @Hex.FpPoly primeData.p primeData.bounds :=
  letI := primeData.bounds
  S.toList.foldl (fun acc i => acc * modPFactor primeData i) 1

/--
Identify the executable modular subset product with a Mathlib `Finset.prod`.

The executable surface stores subset products as a left fold over
`Finset.toList`; after transporting each `FpPoly` to Mathlib, commutativity
identifies that fold with the canonical finite-set product.
-/
theorem toMathlibPolynomial_modPFactorProduct
    (primeData : Hex.PrimeChoiceData) (S : ModPFactorSubset primeData) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial (modPFactorProduct primeData S) =
      ∏ i ∈ S,
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) := by
  letI := primeData.bounds
  unfold modPFactorProduct
  rw [show
      (S.toList.foldl (fun acc i => acc * modPFactor primeData i)
          (1 : @Hex.FpPoly primeData.p primeData.bounds)) =
        (S.toList.map (modPFactor primeData)).foldl (· * ·) 1 from by
    rw [List.foldl_map]]
  rw [toMathlibPolynomial_listFoldlMul_one, List.map_map]
  exact Finset.prod_map_toList S
    (fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i))

/--
The monic modular image used for subset partition statements. This mirrors the
executable prime-choice normalization: zero stays zero, and nonzero inputs are
scaled by the inverse of their leading coefficient.
-/
@[expose]
def monicModPImage {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p) : Hex.FpPoly p :=
  if f.isZero then
    0
  else
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f

theorem monicModPImage_eq_monicModularImage
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p) :
    monicModPImage f = Hex.monicModularImage f := by
  rfl

/-- For a nonzero `Hex.FpPoly p`, `Hex.monicModularImage` is exactly the
leading-coefficient inverse scaling of the input. This records the direct
`if f.isZero then 0 else scale (lc f)⁻¹ f` branch of the definition, avoiding
repeated local `unfold Hex.monicModularImage; simp [hf]` derivations at the
call sites that need this equation. -/
private theorem monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] {f : Hex.FpPoly p}
    (hf : f.isZero = false) :
    Hex.monicModularImage f =
        Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f := by
  unfold Hex.monicModularImage
  simp [hf]

theorem monicModPImage_zero {p : Nat} [Hex.ZMod64.Bounds p] :
    @monicModPImage p _ 0 = 0 := by
  rfl

theorem monicModPImage_ne_zero_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Hex.Nat.Prime p)]
    {f : Hex.FpPoly p} (hf : f.isZero = false) :
    monicModPImage f ≠ 0 := by
  rw [monicModPImage_eq_monicModularImage]
  have hf_ne : f ≠ 0 := by
    intro hzero
    subst hzero
    contradiction
  exact Hex.monicModularImage_ne_zero_of_ne_zero (Fact.out : Hex.Nat.Prime p) hf_ne

theorem monicModPImage_monic_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p} (hf : f.isZero = false) :
    Hex.DensePoly.Monic (monicModPImage f) := by
  rw [monicModPImage_eq_monicModularImage]
  exact Hex.monicModularImage_monic hprime f hf

/-- Nonvanishing of the leading coefficient for a positive-size
`Hex.FpPoly p`. Composes `Hex.FpPoly.leadingCoeff_eq_coeff_pred`, which
rewrites the leading coefficient to `f.coeff (f.size - 1)`, with
`Hex.DensePoly.coeff_last_ne_zero_of_pos_size`, the invariant that the
size-pred coefficient of a positive-size `Hex.DensePoly` is nonzero. -/
theorem fpPoly_leadingCoeff_ne_zero_of_size_pos
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p)
    (hf_size_pos : 0 < f.size) :
    Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) := by
  rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred f hf_size_pos]
  exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size f hf_size_pos

/-- For a nonzero `Hex.FpPoly p`, the monic modular image divides the input.
This packages the nonzero branch of `Hex.monicModularImage`: the branch scales
by the inverse of a nonzero leading coefficient, and unit-scaling preserves
divisibility back to the original polynomial. -/
private theorem monicModularImage_dvd_self_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] (hprime : Hex.Nat.Prime p)
    {f : Hex.FpPoly p} (hf : f.isZero = false) :
    Hex.monicModularImage f ∣ f := by
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hprime
  have hsize_pos : 0 < f.size :=
    (Hex.DensePoly.isZero_eq_false_iff _).mp hf
  have hlead_ne :
      Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos f hsize_pos
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff f)⁻¹ ≠ (0 : Hex.ZMod64 p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  rw [monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hf]
  exact Hex.FpPoly.dvd_scale_self_of_ne_zero hinv_ne f

theorem monicModPImage_dvd_self_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p} (hf : f.isZero = false) :
    monicModPImage f ∣ f := by
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hprime
  unfold monicModPImage
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  have hf_ne : f ≠ 0 := by
    intro hzero
    subst hzero
    contradiction
  have hf_size_pos : 0 < f.size := Hex.FpPoly.size_pos_of_ne_zero hf_ne
  have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos f hf_size_pos
  have hinv_ne : (Hex.DensePoly.leadingCoeff f)⁻¹ ≠ (0 : Hex.ZMod64 p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  exact Hex.FpPoly.dvd_scale_self_of_ne_zero hinv_ne f

theorem dvd_monicModPImage_of_dvd
    {p : Nat} [Hex.ZMod64.Bounds p]
    (_hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p}
    (hf : f.isZero = false) :
    f ∣ monicModPImage f := by
  unfold monicModPImage
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹, ?_⟩
  calc
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f
        = Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ * f := by
          rw [Hex.FpPoly.C_mul_eq_scale]
    _ = f * Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ :=
          Hex.DensePoly.mul_comm_poly _ _

theorem modP_mul
    (p : Nat) [Hex.ZMod64.Bounds p] (f g : Hex.ZPoly) :
    Hex.ZPoly.modP p (f * g) = Hex.ZPoly.modP p f * Hex.ZPoly.modP p g := by
  have hprod :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
        (f * g) p := by
    exact Hex.ZPoly.congr_trans
      (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
      (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f) * Hex.FpPoly.liftToZ (Hex.ZPoly.modP p g))
      (f * g) p
      (Hex.ZPoly.liftToZ_mul_congr p (Hex.ZPoly.modP p f) (Hex.ZPoly.modP p g))
      (Hex.ZPoly.congr_mul
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f))
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p g))
        f g p
        (Hex.FpPoly.congr_liftToZ_modP (p := p) f)
        (Hex.FpPoly.congr_liftToZ_modP (p := p) g))
  have hmod := Hex.ZPoly.modP_eq_of_congr p
    (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
    (f * g) hprod
  simp only [Hex.FpPoly.modP_liftToZ] at hmod
  exact hmod.symm

theorem modP_dvd_modP_of_dvd
    (p : Nat) [Hex.ZMod64.Bounds p] {factor core : Hex.ZPoly}
    (hdvd : factor ∣ core) :
    Hex.ZPoly.modP p factor ∣ Hex.ZPoly.modP p core := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨Hex.ZPoly.modP p q, ?_⟩
  rw [hq, modP_mul]

/-- Divisibility at the `Hex.FpPoly p` layer preserves `isZero = false`:
if `a ∣ b` and `b.isZero = false` then `a.isZero = false`. The bespoke
`Dvd` instance for `Hex.FpPoly p` is `instDvdOfAddOfMul`, not Mathlib's
`semigroupDvd`, so Mathlib's `dvd`-based zero-propagation lemmas do not
apply at this layer and the boolean-`isZero` contrapositive is rebuilt
directly here. -/
private theorem fpPoly_isZero_false_of_dvd_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] {a b : Hex.FpPoly p}
    (hab : a ∣ b) (hb : b.isZero = false) : a.isZero = false := by
  cases ha : a.isZero with
  | false => rfl
  | true =>
      exfalso
      have ha_zero : a = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro n
        have hsize : a.size = 0 := by
          change a.coeffs.isEmpty = true at ha
          simpa [Hex.DensePoly.size, Array.isEmpty_iff_size_eq_zero] using ha
        rw [Hex.DensePoly.coeff_eq_zero_of_size_le a (by omega)]
        exact Hex.DensePoly.coeff_zero n
      rcases hab with ⟨q, hq⟩
      rw [ha_zero, Hex.FpPoly.zero_mul] at hq
      rw [hq] at hb
      exact Bool.noConfusion hb

/-- Transitivity of `Hex.FpPoly p`-level divisibility. Discharges the
`c = a * (q * v)` step explicitly via `Hex.FpPoly.mul_assoc` because the
`Dvd` instance on `Hex.FpPoly p` is the bespoke `instDvdOfAddOfMul`
(witness shape `b = a * r`), and `dvd_trans` does not see through that. -/
private theorem fpPoly_dvd_trans
    {p : Nat} [Hex.ZMod64.Bounds p]
    {a b c : Hex.FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨q * v, ?_⟩
  rw [hv, hq]
  exact Hex.FpPoly.mul_assoc _ _ _

/-- Products of divisors divide products at the executable `Hex.FpPoly p`
level. The `Dvd` instance on `Hex.FpPoly p` is the bespoke
`instDvdOfAddOfMul` (witness shape `b = a * r`), so Mathlib's
`mul_dvd_mul` does not see through it. -/
private theorem fpPoly_mul_dvd_mul
    {p : Nat} [Hex.ZMod64.Bounds p]
    {a b c d : Hex.FpPoly p} (hab : a ∣ b) (hcd : c ∣ d) :
    a * c ∣ b * d := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hcd
  refine ⟨q * v, ?_⟩
  rw [hq, hv, Hex.FpPoly.mul_assoc a q (c * v), ← Hex.FpPoly.mul_assoc q c v,
    Hex.FpPoly.mul_comm q c, Hex.FpPoly.mul_assoc c q v, ← Hex.FpPoly.mul_assoc a c (q * v)]

theorem monicModPImage_dvd_monicModularImage_of_dvd_of_choosePrimeData?_some
    {core factor : Hex.ZPoly}
    (hdvd : factor ∣ core)
    (_hcore_ne : core ≠ 0)
    {primeData : Hex.PrimeChoiceData}
    (hsome : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    @monicModPImage primeData.p primeData.bounds
        (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
      Hex.monicModularImage
        (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hsome
  have hcore_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  have hcore_mod_ne : @Hex.ZPoly.modP primeData.p primeData.bounds core ≠ 0 := by
    intro hzero
    rw [hzero] at hcore_iszero
    contradiction
  have hfactor_dvd_core :
      @Hex.ZPoly.modP primeData.p primeData.bounds factor ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds core :=
    modP_dvd_modP_of_dvd primeData.p hdvd
  have hfactor_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds factor).isZero = false :=
    fpPoly_isZero_false_of_dvd_of_isZero_false hfactor_dvd_core hcore_iszero
  have hmonic_factor_dvd_factor :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds factor :=
    monicModPImage_dvd_self_of_ne_zero hprime hfactor_iszero
  have hmonic_factor_dvd_core :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds core :=
    fpPoly_dvd_trans hmonic_factor_dvd_factor hfactor_dvd_core
  have hcore_dvd_monic :
      @Hex.ZPoly.modP primeData.p primeData.bounds core ∣
        Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
    unfold Hex.monicModularImage
    simp only [hcore_iszero, Bool.false_eq_true, ↓reduceIte]
    refine ⟨Hex.DensePoly.C
        (Hex.DensePoly.leadingCoeff
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹, ?_⟩
    calc
      Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹
          (@Hex.ZPoly.modP primeData.p primeData.bounds core)
          = Hex.DensePoly.C
              (Hex.DensePoly.leadingCoeff
                (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹ *
            (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
            rw [Hex.FpPoly.C_mul_eq_scale]
      _ = (@Hex.ZPoly.modP primeData.p primeData.bounds core) *
            Hex.DensePoly.C
              (Hex.DensePoly.leadingCoeff
                (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹ :=
            Hex.DensePoly.mul_comm_poly _ _
  exact fpPoly_dvd_trans hmonic_factor_dvd_core hcore_dvd_monic

/--
An integer factor is represented modulo the selected prime by a subset of the
recorded modular factors when the subset product is the monic modular image of
that integer factor.
-/
def RepresentsIntegerFactorModP
    (primeData : Hex.PrimeChoiceData) (factor : Hex.ZPoly)
    (S : ModPFactorSubset primeData) : Prop :=
  modPFactorProduct primeData S =
    @monicModPImage primeData.p primeData.bounds
      (@Hex.ZPoly.modP primeData.p primeData.bounds factor)

/--
Proof-facing package for the mod-`p` irreducible-factor subset partition over
the executable `PrimeChoiceData` surface.

The proposition parameters are hooks for the eventual admissible-prime and
square-free-reduction hypotheses. Downstream callers should depend on the
existence and uniqueness projections below rather than on a particular analytic
proof of this package.
-/
structure ModPSubsetPartitionHypotheses
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (admissiblePrime squareFreeReduction : Prop) : Prop where
  fModP_eq : primeData.fModP = @Hex.ZPoly.modP primeData.p primeData.bounds core
  admissible_prime : admissiblePrime
  square_free_reduction : squareFreeReduction
  factors_irreducible :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i))
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃ S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : ModPFactorSubset primeData},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorModP primeData factor S →
      RepresentsIntegerFactorModP primeData factor T →
      S = T

/--
Caller-facing mod-`p` subset partition: an irreducible integer factor of the
core has a unique representing subset of the selected modular factors.
-/
theorem existsUnique_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S := by
  rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro T hT
  exact (h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT).symm

/-- Existence projection from the mod-`p` subset-partition package. -/
theorem exists_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃ S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S :=
  h.exists_subset hirr hdvd

/-- Uniqueness projection from the mod-`p` subset-partition package. -/
theorem unique_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly} {S T : ModPFactorSubset primeData}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hS : RepresentsIntegerFactorModP primeData factor S)
    (hT : RepresentsIntegerFactorModP primeData factor T) :
    S = T :=
  h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT

/-- Irreducibility projection for a selected modular factor. -/
theorem modPFactor_irreducible_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (i : ModPFactorIndex primeData) :
    Irreducible
      (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (modPFactor primeData i)) :=
  h.factors_irreducible i

/--
If a selected modular factor divides the Mathlib image of a represented
integer-factor product, then its index belongs to the representing subset.
-/
theorem mem_modPSubset_of_dvd
    {core factor : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (hprime : _root_.Nat.Prime primeData.p)
    (hpart :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hf_inj : Function.Injective (fun i : ModPFactorIndex primeData =>
      @HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (modPFactor primeData i)))
    (hmonic : ∀ i : ModPFactorIndex primeData,
      (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (modPFactor primeData i)).Monic)
    {S : ModPFactorSubset primeData} {i : ModPFactorIndex primeData}
    (hS : RepresentsIntegerFactorModP primeData factor S)
    (hdvd :
      @HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i) ∣
        @HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor))) :
    i ∈ S := by
  classical
  letI := primeData.bounds
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  let F : ModPFactorIndex primeData → Polynomial (ZMod primeData.p) :=
    fun j => @HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
      (modPFactor primeData j)
  have hrepresented :
      (∏ j ∈ S, F j) =
        @HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (@monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds factor)) := by
    rw [← toMathlibPolynomial_modPFactorProduct]
    exact congrArg HexBerlekampMathlib.toMathlibPolynomial hS
  have hdvd_prod : F i ∣ ∏ j ∈ S, F j := by
    rw [hrepresented]
    simpa [F] using hdvd
  have hi_prime : Prime (F i) := by
    simpa [F] using (hpart.factors_irreducible i).prime
  rcases (Prime.dvd_finsetProd_iff hi_prime F).mp hdvd_prod with ⟨j, hjS, hdvd_ij⟩
  have hij_poly : F i = F j := by
    have hassoc : Associated (F i) (F j) := by
      exact (hpart.factors_irreducible i).associated_of_dvd
        (hpart.factors_irreducible j) (by simpa [F] using hdvd_ij)
    exact Polynomial.eq_of_monic_of_associated
      (by simpa [F] using hmonic i)
      (by simpa [F] using hmonic j)
      hassoc
  have hij : i = j := hf_inj (by simpa [F] using hij_poly)
  simpa [hij] using hjS

/-- The project-local primality predicate implies Mathlib's `Nat.Prime`. -/
theorem natPrime_of_hexNatPrime {p : Nat} (hp : Hex.Nat.Prime p) :
    _root_.Nat.Prime p := by
  refine _root_.Nat.prime_def_lt.mpr ⟨hp.two_le, ?_⟩
  intro m hmlt hmdvd
  rcases hp.2 m hmdvd with h | h
  · exact h
  · exact absurd h (Nat.ne_of_lt hmlt)

/-- Multiplicative inverse cancellation modulo a prime: `(c * a)⁻¹ * c = a⁻¹`
for nonzero residues, the field identity that lets `monicModPImage` absorb a
unit scalar. -/
private theorem zmod64_inv_mul_left_cancel {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {a c : Hex.ZMod64 p} (ha : a ≠ 0) (hc : c ≠ 0) :
    (c * a)⁻¹ * c = a⁻¹ := by
  have hca : c * a ≠ 0 := by
    intro h
    rcases Hex.ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hprime h with h1 | h2
    · exact hc h1
    · exact ha h2
  have h1 : (c * a)⁻¹ * (c * a) = 1 :=
    Hex.ZMod64.inv_mul_eq_one_of_prime hprime hca
  have h2 : a * a⁻¹ = 1 := Hex.ZMod64.mul_inv_eq_one_of_prime hprime ha
  have hxa : ((c * a)⁻¹ * c) * a = 1 := by
    have e : ((c * a)⁻¹ * c) * a = (c * a)⁻¹ * (c * a) := by grind
    rw [e]; exact h1
  calc (c * a)⁻¹ * c
      = ((c * a)⁻¹ * c) * (a * a⁻¹) := by rw [h2]; grind
    _ = (((c * a)⁻¹ * c) * a) * a⁻¹ := by grind
    _ = 1 * a⁻¹ := by rw [hxa]
    _ = a⁻¹ := by grind

/-- **Unit-invariance of `monicModPImage`.** Scaling a modular polynomial by a
nonzero residue (a unit modulo a prime) leaves its monic image unchanged: the
leading-coefficient normalisation divides the unit scalar back out. -/
theorem monicModPImage_scale {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {c : Hex.ZMod64 p} (hc : c ≠ 0) (f : Hex.FpPoly p) :
    monicModPImage (Hex.DensePoly.scale c f) = monicModPImage f := by
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hprime
  cases hf : f.isZero with
  | true =>
    have hf_size : f.size = 0 := by
      by_contra h
      have hfalse : f.isZero = false :=
        (Hex.DensePoly.isZero_eq_false_iff f).mpr (Nat.pos_of_ne_zero h)
      rw [hfalse] at hf
      exact Bool.noConfusion hf
    have hsf_size : (Hex.DensePoly.scale c f).size = 0 := by
      have := Hex.FpPoly.scale_size_le c f; omega
    have hsf : (Hex.DensePoly.scale c f).isZero = true := by
      by_contra h
      rw [Bool.not_eq_true] at h
      have := (Hex.DensePoly.isZero_eq_false_iff _).mp h; omega
    unfold monicModPImage
    simp [hf, hsf]
  | false =>
    have hf_pos : 0 < f.size := (Hex.DensePoly.isZero_eq_false_iff f).mp hf
    have hf_size : f.size ≠ 0 := by omega
    have hsf_size : (Hex.DensePoly.scale c f).size = f.size :=
      Hex.FpPoly.scale_size_eq_of_ne_zero hc f
    have hsf : (Hex.DensePoly.scale c f).isZero = false :=
      (Hex.DensePoly.isZero_eq_false_iff _).mpr (by omega)
    unfold monicModPImage
    simp only [hf, hsf, Bool.false_eq_true, ↓reduceIte]
    rw [Hex.FpPoly.leadingCoeff_scale_of_ne_zero_of_nonzero hc f hf_size,
      Hex.FpPoly.scale_scale,
      zmod64_inv_mul_left_cancel hprime
        (fpPoly_leadingCoeff_ne_zero_of_size_pos f hf_pos) hc]

/-- Transport of a `-1` integer scaling to `Polynomial ℤ` negation. -/
private theorem toPolynomial_scale_neg_one (f : Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial (Hex.DensePoly.scale (-1 : Int) f) =
      -HexPolyZMathlib.toPolynomial f := by
  ext n
  have hzero_mul : (-1 : Int) * (0 : Int) = 0 := by simp
  rw [HexPolyZMathlib.coeff_toPolynomial,
    Hex.DensePoly.coeff_scale (-1 : Int) f n hzero_mul,
    Polynomial.coeff_neg, HexPolyZMathlib.coeff_toPolynomial]
  ring

/-- The `ZMod p` image of the residue `-1` is `-1`. Computed through the
ring-hom bridge `toZMod`, keeping `ZMod64` arithmetic on the `grind` side. -/
private theorem toZMod_neg_one {p : Nat} [Hex.ZMod64.Bounds p] :
    HexModArithMathlib.ZMod64.toZMod (-1 : Hex.ZMod64 p) = (-1 : ZMod p) := by
  have hzm : (-1 : Hex.ZMod64 p) + 1 = 0 := by grind
  have h0 : HexModArithMathlib.ZMod64.toZMod ((-1 : Hex.ZMod64 p) + 1) = 0 := by
    rw [hzm, HexModArithMathlib.ZMod64.toZMod_zero]
  rw [HexModArithMathlib.ZMod64.toZMod_add, HexModArithMathlib.ZMod64.toZMod_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- Reduction modulo `p` commutes with `-1` scaling: it lands on scaling by the
residue `-1`. Proved through the `Polynomial (ZMod p)` bridge. -/
private theorem modP_scale_neg_one {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    Hex.ZPoly.modP p (Hex.DensePoly.scale (-1 : Int) f) =
      Hex.DensePoly.scale (-1 : Hex.ZMod64 p) (Hex.ZPoly.modP p f) := by
  apply HexBerlekampMathlib.fpPolyEquiv.injective
  change
    HexBerlekampMathlib.toMathlibPolynomial
        (Hex.ZPoly.modP p (Hex.DensePoly.scale (-1 : Int) f)) =
      HexBerlekampMathlib.toMathlibPolynomial
        (Hex.DensePoly.scale (-1 : Hex.ZMod64 p) (Hex.ZPoly.modP p f))
  rw [toMathlibPolynomial_modP_eq_map_intCast_zmod, toPolynomial_scale_neg_one,
    Polynomial.map_neg, toMathlibPolynomial_scale,
    toMathlibPolynomial_modP_eq_map_intCast_zmod, toZMod_neg_one,
    Polynomial.C_neg, Polynomial.C_1]
  ring

/-- `-1` is a nonzero residue modulo a prime. -/
private theorem neg_one_ne_zero_zmod {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) : (-1 : Hex.ZMod64 p) ≠ 0 := by
  haveI : Fact (_root_.Nat.Prime p) := ⟨natPrime_of_hexNatPrime hprime⟩
  intro h
  have hz : HexModArithMathlib.ZMod64.toZMod (-1 : Hex.ZMod64 p) =
      HexModArithMathlib.ZMod64.toZMod (0 : Hex.ZMod64 p) := by rw [h]
  rw [HexModArithMathlib.ZMod64.toZMod_zero, toZMod_neg_one] at hz
  exact (neg_ne_zero.mpr one_ne_zero) hz

/-- An `Associated` pair in `Polynomial ℤ` differs by the unit `±1`, so the
executable integer polynomials agree up to the canonical `-1` scaling. -/
private theorem zpoly_eq_or_eq_scale_neg_one_of_associated {f g : Hex.ZPoly}
    (hassoc :
      Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)) :
    g = f ∨ g = Hex.DensePoly.scale (-1 : Int) f := by
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨c, hc_unit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rcases Int.isUnit_iff.mp hc_unit with hc1 | hcneg1
  · left
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial f
    rw [← hu, ← hcu, hc1, Polynomial.C_1, mul_one]
  · right
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial g =
      HexPolyZMathlib.toPolynomial (Hex.DensePoly.scale (-1 : Int) f)
    rw [toPolynomial_scale_neg_one, ← hu, ← hcu, hcneg1, Polynomial.C_neg, Polynomial.C_1]
    ring

/-- **Associated factors share a monic modular image.** If two integer factors
are associated in `Polynomial ℤ`, their reductions modulo `p` have the same
monic image, because `monicModPImage` absorbs the unit `±1`. -/
theorem monicModPImage_modP_eq_of_associated {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {f g : Hex.ZPoly}
    (hassoc :
      Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)) :
    monicModPImage (Hex.ZPoly.modP p f) = monicModPImage (Hex.ZPoly.modP p g) := by
  rcases zpoly_eq_or_eq_scale_neg_one_of_associated hassoc with hg | hg
  · rw [hg]
  · rw [hg, modP_scale_neg_one]
    exact (monicModPImage_scale hprime (neg_one_ne_zero_zmod hprime)
      (Hex.ZPoly.modP p f)).symm

/-- `RepresentsIntegerFactorModP` depends only on the `Associated` class of the
integer factor in `Polynomial ℤ`: a representing subset for `f` also represents
any associate `g`. -/
theorem representsIntegerFactorModP_of_associated
    {primeData : Hex.PrimeChoiceData} (hprime : Hex.Nat.Prime primeData.p)
    {f g : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hassoc :
      Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g))
    (hf : RepresentsIntegerFactorModP primeData f S) :
    RepresentsIntegerFactorModP primeData g S := by
  letI := primeData.bounds
  unfold RepresentsIntegerFactorModP at hf ⊢
  rw [hf]
  exact monicModPImage_modP_eq_of_associated hprime hassoc

/-- **modP uniqueness up to association.** Associated irreducible integer
divisors of `core` have the *same* representing subset of modular factors, not
merely equal ones. Combines unit-invariance of `monicModPImage` with the
package's `unique_subset` projection. -/
theorem unique_modPFactorSubset_up_to_associated
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (hprime : Hex.Nat.Prime primeData.p)
    (h :
      ModPSubsetPartitionHypotheses core primeData admissiblePrime squareFreeReduction)
    {f g : Hex.ZPoly} {S T : ModPFactorSubset primeData}
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g))
    (hg_dvd : g ∣ core)
    (hS : RepresentsIntegerFactorModP primeData f S)
    (hT : RepresentsIntegerFactorModP primeData g T)
    (hassoc :
      Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)) :
    S = T :=
  h.unique_subset hg_irr hg_dvd
    (representsIntegerFactorModP_of_associated hprime hassoc hS) hT

/-- Transport executable `FpPoly` divisibility (`∃ r, b = a * r`) to Mathlib
divisibility across `toMathlibPolynomial`. -/
private theorem toMathlibPolynomial_dvd {p : Nat} [Hex.ZMod64.Bounds p]
    {a b : Hex.FpPoly p} (h : a ∣ b) :
    HexBerlekampMathlib.toMathlibPolynomial a ∣
      HexBerlekampMathlib.toMathlibPolynomial b := by
  obtain ⟨r, hr⟩ := h
  exact ⟨HexBerlekampMathlib.toMathlibPolynomial r, by rw [hr, toMathlibPolynomial_mul]⟩

/-- A nonzero modular polynomial divides its own monic image. -/
private theorem self_dvd_monicModPImage {p : Nat} [Hex.ZMod64.Bounds p]
    {h : Hex.FpPoly p} (hh : h.isZero = false) :
    h ∣ monicModPImage h := by
  unfold monicModPImage
  simp only [hh, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hex.DensePoly.C (Hex.DensePoly.leadingCoeff h)⁻¹, ?_⟩
  calc Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff h)⁻¹ h
      = Hex.DensePoly.C (Hex.DensePoly.leadingCoeff h)⁻¹ * h := by
        rw [Hex.FpPoly.C_mul_eq_scale]
    _ = h * Hex.DensePoly.C (Hex.DensePoly.leadingCoeff h)⁻¹ :=
        Hex.DensePoly.mul_comm_poly _ _

/-- **modP pairwise-disjointness.** Non-associated irreducible integer divisors of
`core` are represented by disjoint subsets of the modular factors. The genuine
square-freeness of the modular reduction is threaded as the explicit hypothesis
`hsqfree`; if two representing subsets shared an index, that modular factor would
square-divide the (square-free) modular core, an impossibility. -/
theorem modPFactorSubset_disjoint_of_not_associated
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (hprime : Hex.Nat.Prime primeData.p)
    (hpart :
      ModPSubsetPartitionHypotheses core primeData admissiblePrime squareFreeReduction)
    (hcore_modP_nz :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false)
    (hsqfree :
      Squarefree
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (@monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))))
    {f g : Hex.ZPoly} {S T : ModPFactorSubset primeData}
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f)) (hf_dvd : f ∣ core)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g)) (hg_dvd : g ∣ core)
    (hS : RepresentsIntegerFactorModP primeData f S)
    (hT : RepresentsIntegerFactorModP primeData g T)
    (hnotassoc :
      ¬ Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)) :
    Disjoint S T := by
  classical
  letI := primeData.bounds
  set p := primeData.p with hp_def
  -- `modP f`, `modP g` are nonzero because they divide the nonzero `modP core`.
  have hf_modP_nz : (Hex.ZPoly.modP p f).isZero = false :=
    fpPoly_isZero_false_of_dvd_of_isZero_false (modP_dvd_modP_of_dvd p hf_dvd) hcore_modP_nz
  have hg_modP_nz : (Hex.ZPoly.modP p g).isZero = false :=
    fpPoly_isZero_false_of_dvd_of_isZero_false (modP_dvd_modP_of_dvd p hg_dvd) hcore_modP_nz
  -- The representing products transport to the monic modular images.
  have hSeq : modPFactorProduct primeData S =
      @monicModPImage p primeData.bounds (Hex.ZPoly.modP p f) := hS
  have hTeq : modPFactorProduct primeData T =
      @monicModPImage p primeData.bounds (Hex.ZPoly.modP p g) := hT
  have hAf :
      (∏ j ∈ S, HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j)) =
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p f)) := by
    rw [← toMathlibPolynomial_modPFactorProduct, hSeq]
  have hAg :
      (∏ j ∈ T, HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j)) =
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p g)) := by
    rw [← toMathlibPolynomial_modPFactorProduct, hTeq]
  -- `toPoly f * toPoly g ∣ toPoly core` (distinct primes both divide the core).
  have hfg_zdvd :
      HexPolyZMathlib.toPolynomial f * HexPolyZMathlib.toPolynomial g ∣
        HexPolyZMathlib.toPolynomial core := by
    have hf_zdvd : HexPolyZMathlib.toPolynomial f ∣ HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hf_dvd
    have hg_zdvd : HexPolyZMathlib.toPolynomial g ∣ HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hg_dvd
    obtain ⟨k, hk⟩ := hg_zdvd
    have hf_dvd_gk :
        HexPolyZMathlib.toPolynomial f ∣ HexPolyZMathlib.toPolynomial g * k := by
      rw [← hk]; exact hf_zdvd
    have hf_ndvd_g :
        ¬ HexPolyZMathlib.toPolynomial f ∣ HexPolyZMathlib.toPolynomial g := by
      intro hd
      exact hnotassoc (hf_irr.associated_of_dvd hg_irr hd)
    rcases hf_irr.prime.dvd_or_dvd hf_dvd_gk with hg' | hk'
    · exact absurd hg' hf_ndvd_g
    · obtain ⟨m, hm⟩ := hk'
      exact ⟨m, by rw [hk, hm]; ring⟩
  -- Push the divisibility through `Polynomial.map (Int.castRingHom (ZMod p))`.
  have hfg_modP :
      HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p f) *
          HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p g) ∣
        HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p core) := by
    have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod p)) hfg_zdvd
    rw [Polynomial.map_mul, ← toMathlibPolynomial_modP_eq_map_intCast_zmod,
      ← toMathlibPolynomial_modP_eq_map_intCast_zmod,
      ← toMathlibPolynomial_modP_eq_map_intCast_zmod] at hmap
    exact hmap
  -- Assemble: the product of the two monic images divides the square-free core.
  have hMf_dvd :
      HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p f)) ∣
        HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p f) :=
    toMathlibPolynomial_dvd (monicModPImage_dvd_self_of_ne_zero hprime hf_modP_nz)
  have hMg_dvd :
      HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p g)) ∣
        HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p g) :=
    toMathlibPolynomial_dvd (monicModPImage_dvd_self_of_ne_zero hprime hg_modP_nz)
  have hcore_dvd_M :
      HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p core) ∣
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p core)) :=
    toMathlibPolynomial_dvd (self_dvd_monicModPImage hcore_modP_nz)
  have hMfMg_dvd_M :
      HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p f)) *
          HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p g)) ∣
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p core)) :=
    ((mul_dvd_mul hMf_dvd hMg_dvd).trans hfg_modP).trans hcore_dvd_M
  -- A shared index would force a square factor of the square-free core.
  rw [Finset.disjoint_left]
  intro i hiS hiT
  have h1 :
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ∣
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p f)) := by
    rw [← hAf]; exact Finset.dvd_prod_of_mem _ hiS
  have h2 :
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ∣
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p g)) := by
    rw [← hAg]; exact Finset.dvd_prod_of_mem _ hiT
  have hsqM :
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) *
          HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ∣
        HexBerlekampMathlib.toMathlibPolynomial (monicModPImage (Hex.ZPoly.modP p core)) :=
    (mul_dvd_mul h1 h2).trans hMfMg_dvd_M
  exact (hpart.factors_irreducible i).not_isUnit (hsqfree _ hsqM)

end

end HexBerlekampZassenhausMathlib
