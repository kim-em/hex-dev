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

public import HexBerlekampZassenhausMathlib.RecombinationMonic
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.RecombinationMonic

public section
set_option backward.proofsInPublic true

/-!
This module collects primitivity, leading coefficient, and `normalizeFactorSign`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- `Hex.normalizeFactorSign` preserves the content of a `Hex.ZPoly`: it either
returns the input or scales by `-1`, both of which leave the content (the gcd
of absolute values of the coefficients) unchanged. -/
private theorem content_normalizeFactorSign_eq (f : Hex.ZPoly) :
    Hex.ZPoly.content (Hex.normalizeFactorSign f) = Hex.ZPoly.content f := by
  unfold Hex.normalizeFactorSign
  by_cases h : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos h]
    show Hex.DensePoly.content (Hex.DensePoly.scale (-1 : Int) f) =
      Hex.DensePoly.content f
    exact Hex.DensePoly.content_scale_neg_one f
  · rw [if_neg h]

/-- The output of `Hex.normalizeFactorSign` has nonnegative leading coefficient:
the `if_neg` branch keeps the input (whose leading coefficient is already
`≥ 0`), and the `if_pos` branch negates a strictly negative leading coefficient
to a nonnegative one. -/
theorem leadingCoeff_normalizeFactorSign_nonneg (f : Hex.ZPoly) :
    0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign f) := by
  unfold Hex.normalizeFactorSign
  by_cases h : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos h]
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero (-1 : Int) f (by decide)]
    omega
  · rw [if_neg h]
    omega

/-- The scaled recombination candidate is a fixed point of
`Hex.normalizeFactorSign`: its construction applies `Hex.normalizeFactorSign`
as the outermost operation, so the candidate already has nonnegative leading
coefficient. -/
private theorem normalizeFactorSign_scaledRecombinationCandidate_eq
    {core : Hex.ZPoly} {d : Hex.LiftData} (T : LiftedFactorSubset d) :
    Hex.normalizeFactorSign (scaledRecombinationCandidate core d T) =
      scaledRecombinationCandidate core d T := by
  have hnonneg :
      0 ≤ Hex.DensePoly.leadingCoeff (scaledRecombinationCandidate core d T) := by
    show 0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign _)
    exact leadingCoeff_normalizeFactorSign_nonneg _
  unfold Hex.normalizeFactorSign
  have hnot :
      ¬ Hex.DensePoly.leadingCoeff (scaledRecombinationCandidate core d T) < 0 := by
    omega
  rw [if_neg hnot]

/-- The corrected recovered candidate is primitive whenever `lc(core)` is
positive and the selected lifted factors are monic. -/
theorem zpoly_primitive_liftedRecoveryCandidate
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (liftedRecoveryCandidate core d T) := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  set cl := Hex.centeredLiftPoly lp (d.p ^ d.k) with hcl_def
  have hcl_monic : Hex.DensePoly.Monic cl := by
    rw [hcl_def]
    exact monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hcl_size_pos : 0 < cl.size := zpoly_size_pos_of_monic hcl_monic
  have hdil_size :
      (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl).size =
        cl.size :=
    size_dilate_eq_of_monic_of_ne_zero hcore_lc_ne hcl_monic
  have hdil_ne :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl ≠ 0 := by
    intro h
    have h0 :
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl).size = 0 := by
      rw [h]; rfl
    omega
  have hdil_content_ne :
      Hex.ZPoly.content
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl) ≠
        (0 : Int) :=
    HexPolyZMathlib.content_ne_zero _ hdil_ne
  show Hex.ZPoly.content (liftedRecoveryCandidate core d T) = 1
  unfold liftedRecoveryCandidate
  rw [← hlp_def, ← hcl_def, content_normalizeFactorSign_eq]
  exact Hex.ZPoly.primitivePart_primitive _ hdil_content_ne

/-- The corrected recovered candidate on the empty subset is the constant `1`.
The empty lifted-factor product is `1`, whose centred lift (for `2 ≤ d.p^d.k`)
and `lc(core)`-dilation are again `1`, leaving `primitivePart 1 = 1` and the
sign-normalised constant `1`. -/
private theorem liftedRecoveryCandidate_empty_eq_one
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k) :
    liftedRecoveryCandidate core d (∅ : LiftedFactorSubset d) = (1 : Hex.ZPoly) := by
  have hempty_lp :
      liftedFactorProduct d (∅ : LiftedFactorSubset d) = (1 : Hex.ZPoly) := by
    unfold liftedFactorProduct
    simp
  have hclpone :
      Hex.centeredLiftPoly (1 : Hex.ZPoly) (d.p ^ d.k) = (1 : Hex.ZPoly) := by
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.coeff_centeredLiftPoly]
    show Hex.centeredModNat
        ((Hex.DensePoly.C (1 : Int)).coeff i) (d.p ^ d.k) =
      (Hex.DensePoly.C (1 : Int)).coeff i
    rw [Hex.DensePoly.coeff_C]
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact centeredModNat_one_of_two_le hd_modulus
    · rw [if_neg hi]
      exact Hex.centeredModNat_zero (d.p ^ d.k)
  have hdilone :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) (1 : Hex.ZPoly) =
        (1 : Hex.ZPoly) := by
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.ZPoly.coeff_dilate]
    show Hex.DensePoly.leadingCoeff core ^ i * (Hex.DensePoly.C (1 : Int)).coeff i =
      (Hex.DensePoly.C (1 : Int)).coeff i
    rw [Hex.DensePoly.coeff_C]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg hi]; exact mul_zero _
  have hone_primitive : Hex.ZPoly.Primitive (1 : Hex.ZPoly) := by
    show Hex.ZPoly.content (1 : Hex.ZPoly) = 1
    show Hex.DensePoly.content (Hex.DensePoly.C (1 : Int)) = 1
    rw [Hex.DensePoly.content_C]; rfl
  have hppone : Hex.ZPoly.primitivePart (1 : Hex.ZPoly) = (1 : Hex.ZPoly) :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive (1 : Hex.ZPoly) hone_primitive
  unfold liftedRecoveryCandidate
  rw [hempty_lp, hclpone, hdilone, hppone, Hex.normalizeFactorSign_one]

/-- Abstract-bound wrapper for
`zpoly_primitive_liftedRecoveryCandidate`. -/
private theorem zpoly_primitive_liftedRecoveryCandidate_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (liftedRecoveryCandidate core d T) := by
  have hB_pos : 0 < B' := by
    have hlc_nat_pos :
        0 < (Hex.DensePoly.leadingCoeff core).natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt hcore_lc_pos)
    omega
  have hd_modulus : 2 ≤ d.p ^ d.k := by
    have htwo_le : 2 ≤ 2 * B' := by omega
    omega
  exact zpoly_primitive_liftedRecoveryCandidate
    hcore_lc_pos hd_modulus hd_liftedFactor_monic T

/-- The corrected recovered candidate has strictly positive leading coefficient
whenever `lc(core)` is positive and the selected lifted factors are monic.

`liftedRecoveryCandidate` is headed by `Hex.normalizeFactorSign`, so its leading
coefficient is nonnegative; primitivity makes it nonzero, hence the leading
coefficient is nonzero, so strictly positive. -/
theorem leadingCoeff_liftedRecoveryCandidate_pos
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    0 < Hex.DensePoly.leadingCoeff (liftedRecoveryCandidate core d T) := by
  have hprim : Hex.ZPoly.Primitive (liftedRecoveryCandidate core d T) :=
    zpoly_primitive_liftedRecoveryCandidate hcore_lc_pos hd_modulus
      hd_liftedFactor_monic T
  have hne : liftedRecoveryCandidate core d T ≠ 0 :=
    Hex.ZPoly.ne_zero_of_primitive _ hprim
  have hlc_ne : Hex.DensePoly.leadingCoeff (liftedRecoveryCandidate core d T) ≠ 0 :=
    Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero _ hne
  have hlc_nonneg :
      0 ≤ Hex.DensePoly.leadingCoeff (liftedRecoveryCandidate core d T) := by
    show 0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign _)
    exact leadingCoeff_normalizeFactorSign_nonneg _
  omega

/-- The leading coefficient of a leading-coefficient dilation of a monic
polynomial is the dilation scalar raised to the polynomial's degree.  Dilation
preserves the size of a monic polynomial (`size_dilate_eq_of_monic_of_ne_zero`),
so the top coefficient is `c ^ (size - 1)` times the monic top coefficient `1`. -/
private theorem leadingCoeff_dilate_of_monic
    {c : Int} (hc : c ≠ 0) {m : Hex.ZPoly} (hm : Hex.DensePoly.Monic m) :
    Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate c m) = c ^ (m.size - 1) := by
  have hm_size_pos : 0 < m.size := zpoly_size_pos_of_monic hm
  have hsize : (Hex.ZPoly.dilate c m).size = m.size :=
    size_dilate_eq_of_monic_of_ne_zero hc hm
  have hdil_size_pos : 0 < (Hex.ZPoly.dilate c m).size := by
    rw [hsize]; exact hm_size_pos
  have hm_lead : m.coeff (m.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last m hm_size_pos]
    exact Hex.DensePoly.leadingCoeff_eq_one_of_monic hm
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last _ hdil_size_pos, hsize,
    Hex.ZPoly.coeff_dilate, hm_lead, Int.mul_one]

/-- A nonzero integer polynomial with positive leading coefficient has a
primitive part with positive leading coefficient: dividing out the nonnegative
content scales the leading coefficient by a positive factor. -/
private theorem leadingCoeff_primitivePart_pos
    {q : Hex.ZPoly} (hq : q ≠ 0)
    (hlc : 0 < Hex.DensePoly.leadingCoeff q) :
    0 < Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart q) := by
  have hcontent_ne : Hex.ZPoly.content q ≠ 0 := HexPolyZMathlib.content_ne_zero q hq
  have hcontent_nonneg : 0 ≤ Hex.ZPoly.content q := by
    unfold Hex.ZPoly.content Hex.DensePoly.content
    exact Int.natCast_nonneg _
  have hrec :
      Hex.ZPoly.content q *
          Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart q) =
        Hex.DensePoly.leadingCoeff q := by
    have h := Hex.ZPoly.content_mul_primitivePart q
    calc
      Hex.ZPoly.content q *
            Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart q)
          = Hex.DensePoly.leadingCoeff
              (Hex.DensePoly.scale (Hex.ZPoly.content q)
                (Hex.ZPoly.primitivePart q)) := by
            rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
              (Hex.ZPoly.content q) (Hex.ZPoly.primitivePart q) hcontent_ne]
      _ = Hex.DensePoly.leadingCoeff q := by rw [h]
  by_contra hle
  push Not at hle
  have hnonpos :
      Hex.ZPoly.content q *
          Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart q) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨hcontent_nonneg, hle⟩)
  rw [hrec] at hnonpos
  exact absurd hlc (not_lt.mpr hnonpos)

/-- **Recovery sign-normalisation bridge.**

A recovered integer factor at a Hensel lift over a positive-leading-coefficient
core, with monic lifted local factors and Mignotte-sufficient precision, is
already sign-normalised: `Hex.normalizeFactorSign factor = factor`.

The `dilate_eq` field pins `factor = primitivePart (dilate (lc core) monicFactor)`.
Under the precision bound the monic coordinate `monicFactor` is the centred lift
of the monic selected product (`hcl`), hence monic, so the dilation by
`lc core > 0` has leading coefficient `(lc core) ^ deg > 0`, and primitivisation
preserves that positive sign.

The `0 < lc core`, monic-lifted-factor and precision hypotheses are genuinely
required: the carrier alone fixes `factor` as `primitivePart (dilate (lc core)
monicFactor)`, whose leading-coefficient sign is `sign (lc core ^ deg ·
lc monicFactor)`, and `lc core < 0` (or a non-monic coordinate) admits a
negative-leading-coefficient `factor` for which `normalizeFactorSign factor ≠
factor`.  The bare `Irreducible`/`∣ core` hypotheses suggested by the directive
do not constrain that sign. -/
theorem RecoveredAtLift.normalizeFactorSign_eq
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hrep : RecoveredAtLift core d factor S)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k) :
    Hex.normalizeFactorSign factor = factor := by
  set B' := Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic
    with hB'
  have hvalid : ∀ i, (hrep.monicFactor.coeff i).natAbs ≤ B' :=
    defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hmonic_ne
      hrep.monicFactor hrep.monic_dvd
  have hB'_pos : 0 < B' :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hmonic_ne
  have hmod : 2 ≤ d.p ^ d.k := by omega
  have hlp_monic : Hex.DensePoly.Monic (liftedFactorProduct d S) :=
    liftedFactorProduct_monic d S (fun i _ => hd_liftedFactor_monic i)
  have hcl :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) =
        hrep.monicFactor := by
    rw [← centeredLiftPoly_reduceModPow_eq (liftedFactorProduct d S) d.p d.k
      d.p_pos, hrep.congr]
    exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
      hrep.monicFactor d.p d.k B' hvalid hprecision
  have hmf_monic : Hex.DensePoly.Monic hrep.monicFactor := by
    rw [← hcl]; exact monic_centeredLiftPoly_of_monic hlp_monic hmod
  have hc_ne : Hex.DensePoly.leadingCoeff core ≠ 0 := ne_of_gt hcore_lc_pos
  have hdil_lc_pos :
      0 < Hex.DensePoly.leadingCoeff
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) hrep.monicFactor) := by
    rw [leadingCoeff_dilate_of_monic hc_ne hmf_monic]
    exact pow_pos hcore_lc_pos _
  have hdil_ne :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) hrep.monicFactor ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hdil_lc_pos
    exact lt_irrefl 0 hdil_lc_pos
  have hfactor_lc_pos : 0 < Hex.DensePoly.leadingCoeff factor := by
    rw [← hrep.dilate_eq]
    exact leadingCoeff_primitivePart_pos hdil_ne hdil_lc_pos
  unfold Hex.normalizeFactorSign
  rw [if_neg (by omega : ¬ Hex.DensePoly.leadingCoeff factor < 0)]

/-- `RepresentsIntegerFactorAtLift` form of the recovery sign-normalisation
bridge `RecoveredAtLift.normalizeFactorSign_eq`: a represented integer factor
over a positive-leading-coefficient core with monic lifted factors and
Mignotte-sufficient precision is sign-normalised. -/
theorem normalizeFactorSign_eq_of_representsAtLift
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k) :
    Hex.normalizeFactorSign factor = factor := by
  rcases hrep with ⟨hrec⟩
  exact hrec.normalizeFactorSign_eq hcore_lc_pos hmonic_ne hd_liftedFactor_monic
    hprecision

/-- One-step `shouldRecord` discharge for the corrected recovered candidate:
when `liftedRecoveryCandidate core d S` equals an irreducible integer factor,
the executable record check passes. -/
private theorem shouldRecord_liftedRecoveryCandidate_of_eq_factor
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : liftedRecoveryCandidate core d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    Hex.shouldRecordPolynomialFactor (liftedRecoveryCandidate core d S) = true := by
  rw [heq]
  exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr

/-- One-step `exactQuotient?` discharge for the corrected recovered candidate:
when `liftedRecoveryCandidate core d S` equals an integer divisor of `target`
with positive leading coefficient and positive degree, the executable
exact-division check on `target` returns `some` of the proof-side cofactor. -/
private theorem exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (heq : liftedRecoveryCandidate core d S = factor)
    (hpos_lc : 0 < Hex.DensePoly.leadingCoeff factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target) :
    ∃ quotient,
      Hex.exactQuotient? target (liftedRecoveryCandidate core d S) =
        some quotient ∧
        quotient * liftedRecoveryCandidate core d S = target := by
  obtain ⟨q, hq⟩ := hdvd
  have hmul : q * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq hpos_lc hpos hmul
  · rw [heq]; exact hmul

/--
Abstract-bound variant of `representsIntegerFactorAtLift_primitive`: takes
`B' : Nat`, `hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

Primitivity of `factor` follows soundly from `factor ∣ core` and
`Primitive core`. The positive leading coefficient routes through the
partition's sound recovery equality
`LiftedFactorSubsetPartition.liftedRecoveryCandidate_eq`, which pins
`factor` to `liftedRecoveryCandidate core d S`; that candidate has positive
leading coefficient by `leadingCoeff_liftedRecoveryCandidate_pos`.
-/
theorem representsIntegerFactorAtLift_primitive_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.ZPoly.Primitive factor ∧ 0 < Hex.DensePoly.leadingCoeff factor := by
  have hfactor_dvd_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
  have hfactor_poly_primitive :
      (HexPolyZMathlib.toPolynomial factor).IsPrimitive := by
    have hcore_poly_primitive :
        (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
      toPolynomial_isPrimitive_of_zpoly_primitive_basic hcore_primitive
    exact isPrimitive_of_dvd hcore_poly_primitive
      (HexPolyMathlib.toPolynomial_dvd hfactor_dvd_core)
  have hfactor_primitive : Hex.ZPoly.Primitive factor :=
    zpoly_primitive_of_toPolynomial_isPrimitive_basic hfactor_poly_primitive
  have hB_pos : 0 < B' := by
    have hlc_nat_pos :
        0 < (Hex.DensePoly.leadingCoeff core).natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt hcore_lc_pos)
    omega
  have hd_modulus : 2 ≤ d.p ^ d.k := by
    have htwo_le : 2 ≤ 2 * B' := by omega
    omega
  have hrec_eq : liftedRecoveryCandidate core d S = factor :=
    hpartition.liftedRecoveryCandidate_eq hfactor_irr hfactor_dvd_target hSJ hrep
  have hfactor_lc_pos : 0 < Hex.DensePoly.leadingCoeff factor := by
    rw [← hrec_eq]
    exact leadingCoeff_liftedRecoveryCandidate_pos hcore_lc_pos hd_modulus
      hd_liftedFactor_monic S
  exact ⟨hfactor_primitive, hfactor_lc_pos⟩

/--
Primitive/positive-leading capstone for represented factors under a primitive
non-monic core.

Given an integer factor `factor` of `target ∣ core` represented at the Hensel
lift, primitive `core`, positive leading coefficient for `core`, monic lifted
local factors, the partition, and Mignotte precision, the represented factor is
primitive and has positive leading coefficient.

This is a thin wrapper over
`representsIntegerFactorAtLift_primitive_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges the leading-coefficient
bound via `defaultFactorCoeffBound_valid`.
-/
theorem representsIntegerFactorAtLift_primitive
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    Hex.ZPoly.Primitive factor ∧ 0 < Hex.DensePoly.leadingCoeff factor := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact representsIntegerFactorAtLift_primitive_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hpartition hfactor_irr hfactor_dvd_target htarget_dvd_core hSJ hrep hprecision

/-- Abstract-bound variant of `zpoly_primitive_scaledRecombinationCandidate`:
takes `B' : Nat`,
`hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors the
original but invokes `size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound`
with the abstract `B'` rather than `defaultFactorCoeffBound core`.  The
original core-shape theorem is a wrapper around this variant. -/
private theorem zpoly_primitive_scaledRecombinationCandidate_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (scaledRecombinationCandidate core d T) := by
  -- Inline the size machinery from
  -- `natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum` to obtain
  -- nonzeroness of the inner centred lift, then chase content through the
  -- two outer normalisation operations.
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hslp_size :
      (scaledLiftedFactorProduct core d T).size = lp.size := by
    unfold scaledLiftedFactorProduct
    exact size_scale_eq_of_monic_of_ne_zero hcore_lc_ne hlp_monic
  have hslp_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) lp hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff lp = (1 : Int) from hlp_monic]
    ring
  have hslp_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) := by
    rw [hslp_lc]; exact hcore_lc_pos
  have hslp_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T)).natAbs ≤
        B' := by
    rw [hslp_lc]; exact hcore_lc_le
  have hcl_size :
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size =
        (scaledLiftedFactorProduct core d T).size :=
    size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
      hslp_lc_pos hslp_lc_bound hprecision
  have hcl_size_pos :
      0 < (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size := by
    rw [hcl_size, hslp_size]; exact hlp_size_pos
  have hcl_ne :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k) ≠
        0 := by
    intro h
    have h0 :
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size = 0 := by
      rw [h]; rfl
    omega
  have hcl_content_ne :
      Hex.ZPoly.content
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)) ≠ (0 : Int) := by
    intro hcontent
    apply hcl_ne
    have hpart_zero :
        Hex.ZPoly.primitivePart
            (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
              (d.p ^ d.k)) = 0 := by
      simpa [Hex.ZPoly.primitivePart] using
        Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k))
          (by simpa [Hex.ZPoly.content] using hcontent)
    have hreconstruct := Hex.ZPoly.content_mul_primitivePart
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k))
    rw [hcontent, hpart_zero] at hreconstruct
    have hzero_scale :
        Hex.DensePoly.scale (0 : Int) (0 : Hex.ZPoly) = (0 : Hex.ZPoly) := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Int) (0 : Int) (0 : Hex.ZPoly) n
        (Int.zero_mul 0), Hex.DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [hzero_scale] at hreconstruct
    exact hreconstruct.symm
  show Hex.ZPoly.content (scaledRecombinationCandidate core d T) = 1
  unfold scaledRecombinationCandidate
  rw [content_normalizeFactorSign_eq]
  exact Hex.ZPoly.primitivePart_primitive _ hcl_content_ne

/-- The scaled recombination candidate is primitive whenever `core` is nonzero
and has positive leading coefficient (so the centred-lift size machinery
applies). The construction `normalizeFactorSign ∘ primitivePart` gives content
`1` whenever the inner centred lift is nonzero, and `normalizeFactorSign`
preserves content.

Thin wrapper over `zpoly_primitive_scaledRecombinationCandidate_of_bound` that
instantiates `B' := defaultFactorCoeffBound core` and discharges
`hcore_lc_le` via `defaultFactorCoeffBound_valid core hcore_ne core
(dvd_refl core) (core.size - 1)`. -/
private theorem zpoly_primitive_scaledRecombinationCandidate
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (scaledRecombinationCandidate core d T) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact zpoly_primitive_scaledRecombinationCandidate_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core) hcore_lc_le
    hcore_ne hcore_lc_pos hd_liftedFactor_monic hprecision T

/-- Abstract-bound variant of `not_represents_empty_of_irreducible_dvd_core`.

Routes through the partition's sound recovery equality
`LiftedFactorSubsetPartition.liftedRecoveryCandidate_eq`: on the empty subset
the recovered candidate is the constant `1`
(`liftedRecoveryCandidate_empty_eq_one`), so an empty representation forces
`factor = 1`, contradicting irreducibility. The `hcore_monic` hypothesis is no
longer load-bearing for the recovery itself but is retained for API
uniformity with the consuming monic recursion. -/
private theorem not_represents_empty_of_irreducible_dvd_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (B' : Nat)
    (_hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (_hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_dvd_target : factor ∣ target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (_hprecision : 2 * B' < d.p ^ d.k) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  intro hrep
  have hrec : liftedRecoveryCandidate core d (∅ : LiftedFactorSubset d) = factor :=
    hpartition.liftedRecoveryCandidate_eq hfactor_irr hfactor_dvd_target
      (Finset.empty_subset J) hrep
  rw [liftedRecoveryCandidate_empty_eq_one hd_modulus] at hrec
  have hpolyfactor_eq : HexPolyZMathlib.toPolynomial factor = 1 := by
    rw [← hrec]; exact toPolynomial_one_zpoly
  exact not_irreducible_one (hpolyfactor_eq ▸ hfactor_irr)

/--
An irreducible integer factor of the core is never represented by the empty
subset.  The recovery equation
`centeredLiftPoly (scaledLiftedFactorProduct core d ∅) (d.p^d.k) = factor`
collapses (under a monic core) to `centeredLiftPoly 1 (d.p^d.k) = factor`,
which forces `factor = 1` whenever `d.p^d.k ≥ 2`; the residual `d.p^d.k = 1`
case forces `factor = 0`.  Both outcomes contradict irreducibility of
`HexPolyZMathlib.toPolynomial factor`.

Used by `representedFactor_dvd_recombinationCandidate_of_subset` (#4457) to
close the `S = ∅` subcase of the squarefreeness contradiction.

This is a thin wrapper over
`not_represents_empty_of_irreducible_dvd_core_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges `hvalid` via
`defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd`.
-/
private theorem not_represents_empty_of_irreducible_dvd_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd : factor ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_dvd_target : factor ∣ target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hd_modulus : 2 ≤ d.p ^ d.k := by
    rw [hlead] at hcore_lc_le
    simp only [Int.natAbs_one] at hcore_lc_le
    omega
  exact not_represents_empty_of_irreducible_dvd_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd)
    hcore_ne hcore_monic hd_modulus hpartition hfactor_dvd_target hfactor_irr
    hprecision

/-- Abstract-bound variant of
`not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core`.

Routes through the partition's sound recovery equality
`LiftedFactorSubsetPartition.liftedRecoveryCandidate_eq`: on the empty subset
the recovered candidate is the constant `1`
(`liftedRecoveryCandidate_empty_eq_one`), so an empty representation forces
`factor = 1`, contradicting irreducibility. The primitive/positive-leading
core hypotheses are no longer load-bearing for the recovery itself but are
retained for API uniformity with the consuming primitive recursion. -/
private theorem not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (B' : Nat)
    (_hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_dvd_target : factor ∣ target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (_hprecision : 2 * B' < d.p ^ d.k) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  intro hrep
  have hrec : liftedRecoveryCandidate core d (∅ : LiftedFactorSubset d) = factor :=
    hpartition.liftedRecoveryCandidate_eq hfactor_irr hfactor_dvd_target
      (Finset.empty_subset J) hrep
  rw [liftedRecoveryCandidate_empty_eq_one hd_modulus] at hrec
  have hpolyfactor_eq : HexPolyZMathlib.toPolynomial factor = 1 := by
    rw [← hrec]; exact toPolynomial_one_zpoly
  exact not_irreducible_one (hpolyfactor_eq ▸ hfactor_irr)

/--
Primitive + positive-leading-core variant of
`not_represents_empty_of_irreducible_dvd_core` (#4646).

For primitive non-monic `core`, the empty-prefix collapse becomes
`scaledLiftedFactorProduct core d ∅ = C (lc core)`, and the centred-lift
recovery forces `factor = C (lc core)`. Together with
`Primitive core` and `factor ∣ core`, the primitivity definition of
`Polynomial ℤ` forces `lc core` to be a unit. With `0 < lc core` this gives
`lc core = 1`, so `factor = 1`, contradicting irreducibility. The
`d.p^d.k = 1` degenerate case is excluded as in the monic proof.

This is a thin wrapper over
`not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := defaultFactorCoeffBound core`, discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd`,
and discharges the leading-coefficient bound via the same lemma applied to
`core ∣ core`.
-/
private theorem not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd : factor ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hfactor_dvd_target : factor ∣ target)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  -- Bound the leading coefficient of `core` against the Mignotte half-window.
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hlc_natAbs_pos : 0 < (Hex.DensePoly.leadingCoeff core).natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt hcore_lc_pos)
  have hd_modulus : 2 ≤ d.p ^ d.k := by omega
  exact not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd)
    hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hd_modulus hpartition
    hfactor_dvd_target hfactor_irr hprecision

end

end HexBerlekampZassenhausMathlib
