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

public import HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the lifted-factor infrastructure, candidate definitions, and Hensel-subset correspondence.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Index type for the local factors stored in executable Hensel lift data. -/
abbrev LiftedFactorIndex (d : Hex.LiftData) : Type :=
  Fin d.liftedFactors.size

/-- A finite subset of the local factors stored in executable Hensel lift data. -/
abbrev LiftedFactorSubset (d : Hex.LiftData) : Type :=
  Finset (LiftedFactorIndex d)

/-- The lifted local factor at an executable `LiftData` index. -/
@[expose]
def liftedFactor (d : Hex.LiftData) (i : LiftedFactorIndex d) : Hex.ZPoly :=
  d.liftedFactors[i]

/-- Product of the lifted local factors selected by a finite subset. -/
def liftedFactorProduct (d : Hex.LiftData) (S : LiftedFactorSubset d) : Hex.ZPoly :=
  S.toList.foldl (fun acc i => acc * liftedFactor d i) 1

/-- Transport a modular-factor index to the corresponding lifted-factor index. -/
@[expose]
def liftedIndexOfModPIndex
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (i : ModPFactorIndex primeData) : LiftedFactorIndex d :=
  ⟨i.val, by
    rw [hsize]
    exact i.isLt⟩

/-- Embedding version of `liftedIndexOfModPIndex` for finite-set transport. -/
def modPIndexToLiftedEmbedding
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    ModPFactorIndex primeData ↪ LiftedFactorIndex d where
  toFun := liftedIndexOfModPIndex primeData d hsize
  inj' := by
    intro i j hij
    apply Fin.ext
    change i.val = j.val
    have hval :=
      congrArg (fun x : LiftedFactorIndex d => x.val) hij
    simpa [liftedIndexOfModPIndex] using hval

/--
Transport a selected subset of modular factors to the corresponding selected
subset of lifted factors, once the lift stage is known to preserve factor count.
-/
def liftedSubsetOfModPSubset
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S : ModPFactorSubset primeData) : LiftedFactorSubset d :=
  S.map (modPIndexToLiftedEmbedding primeData d hsize)

/-- Membership in a lifted canonical subset, tested at the lifted image of a
mod-`p` factor index, is exactly membership in the original mod-`p` subset. -/
theorem liftedIndex_mem_liftedSubset_iff
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S : ModPFactorSubset primeData) (i : ModPFactorIndex primeData) :
    liftedIndexOfModPIndex primeData d hsize i ∈
        liftedSubsetOfModPSubset primeData d hsize S ↔
      i ∈ S := by
  unfold liftedSubsetOfModPSubset
  simp [modPIndexToLiftedEmbedding]

/-- The canonical lift from mod-`p` factor subsets to lifted-factor subsets is
injective. -/
theorem liftedSubsetOfModPSubset_injective
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    Function.Injective (liftedSubsetOfModPSubset primeData d hsize) := by
  intro S T hST
  ext i
  rw [← liftedIndex_mem_liftedSubset_iff primeData d hsize S i,
    hST, liftedIndex_mem_liftedSubset_iff primeData d hsize T i]

/-- Canonical lifting reflects and preserves subset containment. -/
theorem liftedSubsetOfModPSubset_subset_iff
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S T : ModPFactorSubset primeData) :
    liftedSubsetOfModPSubset primeData d hsize S ⊆
        liftedSubsetOfModPSubset primeData d hsize T ↔
      S ⊆ T := by
  constructor
  · intro hST i hi
    rw [← liftedIndex_mem_liftedSubset_iff primeData d hsize T i]
    exact hST ((liftedIndex_mem_liftedSubset_iff primeData d hsize S i).mpr hi)
  · intro hST
    unfold liftedSubsetOfModPSubset
    exact (Finset.map_subset_map).mpr hST

/-- Canonical lifting reflects and preserves disjointness. -/
theorem liftedSubsetOfModPSubset_disjoint_iff
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S T : ModPFactorSubset primeData) :
    Disjoint (liftedSubsetOfModPSubset primeData d hsize S)
        (liftedSubsetOfModPSubset primeData d hsize T) ↔
      Disjoint S T := by
  constructor
  · intro hST
    rw [Finset.disjoint_left] at hST ⊢
    intro i hiS hiT
    exact hST
      ((liftedIndex_mem_liftedSubset_iff primeData d hsize S i).mpr hiS)
      ((liftedIndex_mem_liftedSubset_iff primeData d hsize T i).mpr hiT)
  · intro hST
    rw [Finset.disjoint_left] at hST ⊢
    intro j hjS hjT
    unfold liftedSubsetOfModPSubset at hjS hjT
    rw [Finset.mem_map] at hjS hjT
    rcases hjS with ⟨i, hiS, rfl⟩
    rcases hjT with ⟨k, hiT, hik⟩
    have hki : k = i :=
      (modPIndexToLiftedEmbedding primeData d hsize).injective hik
    subst k
    exact hST hiS hiT

/--
Selected lifted-factor product scaled by the leading coefficient of the integer
core, matching the product formed by the executable recombination candidate
checker.
-/
def scaledLiftedFactorProduct
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) : Hex.ZPoly :=
  Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) (liftedFactorProduct d S)

/--
Corrected recovered-coordinate representation of an integer factor at a Hensel
lift.  The selected lifted product represents a monic-coordinate factor modulo
`p^k`; dilating that monic factor by `leadingCoeff core` and taking primitive
part recovers the integer factor of `core`.

The `monic_dvd` field pins the monic coordinate down to the canonical bounded
representative: it must divide `(toMonic core).monic`, the monic polynomial the
Hensel lift is actually built on.  This forces a Mignotte coefficient bound on
`monicFactor` (via `defaultFactorCoeffBound_valid`), which is what makes the
exact-recovery lemma `candidate_eq_of_bound` applicable; without it the residue
link alone admits non-canonical witnesses.

This is the data-bearing carrier behind the public proof-level
`RepresentsIntegerFactorAtLift` predicate.
-/
structure RecoveredAtLift
    (core : Hex.ZPoly) (d : Hex.LiftData) (factor : Hex.ZPoly)
    (S : LiftedFactorSubset d) where
  monicFactor : Hex.ZPoly
  congr :
    Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
      Hex.ZPoly.reduceModPow monicFactor d.p d.k
  dilate_eq :
    Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
      factor
  monic_dvd :
    monicFactor ∣ (Hex.ZPoly.toMonic core).monic

/--
An integer factor is represented by a subset of the lifted local factors when
the unscaled selected product recovers a monic-coordinate witness whose
leading-coefficient dilation has primitive part equal to the integer factor.

The public predicate is proof-only; helper lemmas can unpack the underlying
`RecoveredAtLift` witness when they need the monic-coordinate data.
-/
@[expose]
def RepresentsIntegerFactorAtLift
    (core : Hex.ZPoly) (d : Hex.LiftData) (factor : Hex.ZPoly)
    (S : LiftedFactorSubset d) : Prop :=
  Nonempty (RecoveredAtLift core d factor S)

namespace RepresentsIntegerFactorAtLift

/-- Pack a data-bearing recovered-coordinate witness into the public predicate. -/
theorem ofRecovered
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (h : RecoveredAtLift core d factor S) :
    RepresentsIntegerFactorAtLift core d factor S :=
  ⟨h⟩

/--
Eliminator exposing the monic-coordinate witness, its modular congruence, and
the dilation equality locally.
-/
theorem elim
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    {motive : Prop}
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (h :
      ∀ monicFactor : Hex.ZPoly,
        Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
          Hex.ZPoly.reduceModPow monicFactor d.p d.k →
        Hex.ZPoly.primitivePart
            (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
          factor →
        motive) :
    motive := by
  rcases hrep with ⟨hrec⟩
  exact h hrec.monicFactor hrec.congr hrec.dilate_eq

end RepresentsIntegerFactorAtLift

/-- Dilation commutes with integer coefficient scaling. -/
private theorem dilate_scale (c a : Int) (p : Hex.ZPoly) :
    Hex.ZPoly.dilate c (Hex.DensePoly.scale a p) =
      Hex.DensePoly.scale a (Hex.ZPoly.dilate c p) := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.ZPoly.coeff_dilate, Hex.DensePoly.coeff_scale (R := Int) a p n (Int.mul_zero a),
    Hex.DensePoly.coeff_scale (R := Int) a (Hex.ZPoly.dilate c p) n (Int.mul_zero a),
    Hex.ZPoly.coeff_dilate]
  ring

/-- A positive scalar multiple has the same primitive part. -/
private theorem primitivePart_scale_of_pos {a : Int} (ha : 0 < a) (p : Hex.ZPoly) :
    Hex.ZPoly.primitivePart (Hex.DensePoly.scale a p) =
      Hex.ZPoly.primitivePart p := by
  have hC :
      Hex.ZPoly.primitivePart (Hex.DensePoly.C a : Hex.ZPoly) =
        (1 : Hex.ZPoly) := by
    have hscale :
        Hex.DensePoly.scale a (1 : Hex.ZPoly) =
          (Hex.DensePoly.C a : Hex.ZPoly) := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Int) a (1 : Hex.ZPoly) n (Int.mul_zero a)]
      change a * (Hex.DensePoly.C (1 : Int)).coeff n =
        (Hex.DensePoly.C a : Hex.ZPoly).coeff n
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
        ring
    rw [← hscale]
    simpa [Hex.ZPoly.primitivePart] using
      Hex.DensePoly.primitivePart_scale_of_primitive ha
        (by
          change Hex.DensePoly.content (Hex.DensePoly.C (1 : Int)) = 1
          simp)
  rw [← Hex.ZPoly.C_mul_eq_scale, Hex.ZPoly.primitivePart_mul, hC]
  simp

/--
Primitive-part recovery is unchanged if the monic-coordinate witness is first
replaced by its primitive part before a variable dilation.
-/
private theorem primitivePart_dilate_primitivePart
    (lc : Int) (m : Hex.ZPoly) :
    Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc m) =
      Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate lc (Hex.ZPoly.primitivePart m)) := by
  by_cases hcontent : Hex.ZPoly.content m = 0
  · have hprim_zero : Hex.ZPoly.primitivePart m = 0 := by
      simpa [Hex.ZPoly.primitivePart, Hex.ZPoly.content] using
        Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero m hcontent
    have hm_zero : m = 0 := by
      have hrec := Hex.ZPoly.content_mul_primitivePart m
      rw [hcontent, hprim_zero] at hrec
      simpa using hrec.symm
    subst m
    rw [hprim_zero]
  · have hcontent_pos : 0 < Hex.ZPoly.content m := by
      have hnonneg : 0 ≤ Hex.ZPoly.content m := by
        unfold Hex.ZPoly.content Hex.DensePoly.content
        exact Int.natCast_nonneg _
      omega
    have hrec : m = Hex.DensePoly.scale (Hex.ZPoly.content m) (Hex.ZPoly.primitivePart m) :=
      (Hex.ZPoly.content_mul_primitivePart m).symm
    have hprim_idem :
        Hex.ZPoly.primitivePart (Hex.ZPoly.primitivePart m) =
          Hex.ZPoly.primitivePart m :=
      Hex.ZPoly.primitivePart_eq_self_of_primitive
        (Hex.ZPoly.primitivePart m)
        (Hex.ZPoly.primitivePart_primitive m hcontent)
    rw [hrec, dilate_scale, primitivePart_scale_of_pos hcontent_pos,
      primitivePart_scale_of_pos hcontent_pos, hprim_idem]

/--
Transfer a lifted representation of a monic correspondent for
`(toMonic core).monic` back to a representation of the original integer factor.
-/
theorem representsIntegerFactorAtLift_of_monicCorrespondent
    {core M factor g : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hM : M = (Hex.ZPoly.toMonic core).monic)
    (hM_monic : Hex.DensePoly.Monic M)
    (hrep : RepresentsIntegerFactorAtLift M d g S)
    (hrecover :
      Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) g) = factor) :
    RepresentsIntegerFactorAtLift core d factor S := by
  rcases hrep with ⟨hrec⟩
  refine RepresentsIntegerFactorAtLift.ofRecovered
    { monicFactor := hrec.monicFactor
      congr := hrec.congr
      dilate_eq := ?_
      monic_dvd := ?_ }
  · have hM_lc : Hex.DensePoly.leadingCoeff M = (1 : Int) := hM_monic
    have hg :
        Hex.ZPoly.primitivePart hrec.monicFactor = g := by
      simpa [hM_lc] using hrec.dilate_eq
    rw [primitivePart_dilate_primitivePart, hg, hrecover]
  · rw [← hM]
    have htoM : (Hex.ZPoly.toMonic M).monic = M :=
      Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one M hM_monic
    simpa [htoM] using hrec.monic_dvd

/--
Proof-side form of the executable recombination candidate, using the selected
lifted-factor product directly.  The executable-list version is introduced
later, after the list-selection identification has been developed, and is proved equal
to this definition.
-/
def liftedFactorProductCandidate (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)

/--
Proof-side candidate for recovering an integer factor of a possibly non-monic
core from a selected lifted-factor product.  The selected product is first
centred in the Hensel modulus, then transported back from the `toMonic`
coordinate system by `X ↦ leadingCoeff core * X`, and finally made primitive
with canonical sign.
-/
def liftedRecoveryCandidate
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) <|
        Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)

namespace liftedRecoveryCandidate

/-- On monic cores, the recovered non-monic candidate collapses to the existing
unscaled lifted-product candidate. -/
theorem eq_productCandidate_of_lc_one
    {core : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hlead : Hex.DensePoly.leadingCoeff core = (1 : Int)) :
    liftedRecoveryCandidate core d S = liftedFactorProductCandidate d S := by
  unfold liftedRecoveryCandidate liftedFactorProductCandidate
  rw [hlead, Hex.ZPoly.dilate_one]

end liftedRecoveryCandidate

/-- Scaled variant of the recombination candidate: centred lift of the
leading-coefficient-scaled selected lifted-factor product, primitivised and
sign-normalised.  This is the primitive non-monic supporting lemma used by the scaled
recombination search. -/
def scaledRecombinationCandidate
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k)

/--
Proof-facing package for the square-free Hensel subset correspondence over the
executable `PrimeChoiceData`/`LiftData` surface.

The two proposition parameters are hooks for the precise admissible-prime and
successful-lift hypotheses supplied by the later analytic Hensel proof.  The
caller theorems below depend only on the resulting existence and uniqueness
fields, so downstream exhaustive-recombination proofs can be written against a
stable executable API.
-/
structure HenselSubsetCorrespondenceHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (admissiblePrime successfulLift : Prop) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  admissible_prime : admissiblePrime
  successful_lift : successfulLift
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Hex.normalizeFactorSign factor = factor →
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃ S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor S →
      RepresentsIntegerFactorAtLift core d factor T →
      S = T

/--
Caller-facing square-free Hensel subset correspondence: an irreducible
integer factor of the core has a unique representing subset of the executable
lifted local factors.
-/
theorem existsUnique_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hsign : Hex.normalizeFactorSign factor = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S := by
  rcases h.exists_subset hsign hirr hdvd with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro T hT
  exact (h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT).symm

/-- Existence projection from the executable Hensel subset-correspondence API. -/
theorem exists_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hsign : Hex.normalizeFactorSign factor = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃ S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S :=
  h.exists_subset hsign hirr hdvd

/-- Uniqueness projection from the executable Hensel subset-correspondence API. -/
theorem unique_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly} {S T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hS : RepresentsIntegerFactorAtLift core d factor S)
    (hT : RepresentsIntegerFactorAtLift core d factor T) :
    S = T :=
  h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT

/--
Descent wrapper for lifted Hensel subset representations.

Once the mod-`p` subset partition, the lifted-subset correspondence, and the
forward mod-`p`-to-lift transport are available, any lifted representation of
an irreducible integer factor is the canonical lift of its unique mod-`p`
representing subset.  This packages the purely structural part of the descent
argument; the analytic Hensel facts remain supplied by the input hypotheses.
-/
theorem henselLiftData_represents_modP_of_lifted
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hsize S))
    {factor : Hex.ZPoly} {T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hT : RepresentsIntegerFactorAtLift core d factor T) :
    ∃ S : ModPFactorSubset primeData,
      T = liftedSubsetOfModPSubset primeData d hsize S ∧
        RepresentsIntegerFactorModP primeData factor S := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  have hS_lift :
      RepresentsIntegerFactorAtLift core d factor
        (liftedSubsetOfModPSubset primeData d hsize S) :=
    hlifted_of_modP hirr hdvd hS_mod
  have hT_eq :
      T = liftedSubsetOfModPSubset primeData d hsize S := by
    exact (hcorr.unique_subset hirr hdvd hS_lift hT).symm
  exact ⟨S, hT_eq, hS_mod⟩

/--
Proof-facing package for transporting the mod-`p` subset partition through a
successful Hensel lift.

The fields isolate the analytic Hensel obligations: the lift preserves the
factor count, every mod-`p` selected subset represents the same integer factor
after lifting, and every lifted representation descends to a mod-`p` selected
subset.  The caller theorems below combine these fields with
`ModPSubsetPartitionHypotheses` to recover the existing lifted-subset
correspondence API.
-/
structure HenselSubsetLiftHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData)
    (admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop) :
    Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  admissible_prime : admissiblePrime
  square_free_reduction : squareFreeReduction
  successful_lift : successfulLift
  coprime_lift : coprimeLift
  represents_lifted_of_modP :
    ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorModP primeData factor S →
      RepresentsIntegerFactorAtLift core d factor
        (liftedSubsetOfModPSubset primeData d factor_count_eq S)
  represents_modP_of_lifted :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ S : ModPFactorSubset primeData,
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData factor S

/--
Explicit descent-only package for the lifted Hensel side.

This gives the reverse transport obligation a name independent of the full
`HenselSubsetCorrespondenceHypotheses` API.  Callers still have to prove the
descent field; the point of the package is that they can combine that proof
with forward Hensel transport without first constructing the lifted subset
correspondence.
-/
structure HenselLiftDescentHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (successfulLift coprimeLift : Prop) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  successful_lift : successfulLift
  coprime_lift : coprimeLift
  represents_modP_of_lifted :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ S : ModPFactorSubset primeData,
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData factor S

/--
Data-bearing reverse-descent witness for `toMonicPrimeData?` surfaces.

The lifted representation still recovers the original integer `factor`, but the
descended mod-`p` subset represents the monic correspondent stored inside the
`RecoveredAtLift` witness.  This is the sound replacement for asking the same
subset to represent the non-monic original factor modulo prime data selected for
`(toMonic core).monic`.
-/
structure MonicDescent
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (factor : Hex.ZPoly) (T : LiftedFactorSubset d)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) where
  modPSubset : ModPFactorSubset primeData
  subset_eq : T = liftedSubsetOfModPSubset primeData d hsize modPSubset
  recovered : RecoveredAtLift core d factor T
  represents_monic :
    RepresentsIntegerFactorModP primeData recovered.monicFactor modPSubset

namespace MonicDescent

/-- Pack the explicit monic-correspondent reverse-descent fields. -/
def ofRecovered
    {core factor : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {T : LiftedFactorSubset d}
    {hsize : d.liftedFactors.size = primeData.factorsModP.size}
    (S : ModPFactorSubset primeData)
    (hT :
      T = liftedSubsetOfModPSubset primeData d hsize S)
    (hrec : RecoveredAtLift core d factor T)
    (hmod : RepresentsIntegerFactorModP primeData hrec.monicFactor S) :
    MonicDescent core primeData d factor T hsize where
  modPSubset := S
  subset_eq := hT
  recovered := hrec
  represents_monic := hmod

/-- The monic descent witness still carries the original lifted representation. -/
theorem representsAtLift
    {core factor : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {T : LiftedFactorSubset d}
    {hsize : d.liftedFactors.size = primeData.factorsModP.size}
    (h : MonicDescent core primeData d factor T hsize) :
    RepresentsIntegerFactorAtLift core d factor T :=
  RepresentsIntegerFactorAtLift.ofRecovered h.recovered

/-- Projection of the original-factor recovery equality. -/
theorem dilate_eq
    {core factor : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {T : LiftedFactorSubset d}
    {hsize : d.liftedFactors.size = primeData.factorsModP.size}
    (h : MonicDescent core primeData d factor T hsize) :
    Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) h.recovered.monicFactor) =
      factor :=
  h.recovered.dilate_eq

/-- Projection that the monic correspondent divides the monic transform. -/
theorem monic_dvd
    {core factor : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {T : LiftedFactorSubset d}
    {hsize : d.liftedFactors.size = primeData.factorsModP.size}
    (h : MonicDescent core primeData d factor T hsize) :
    h.recovered.monicFactor ∣ (Hex.ZPoly.toMonic core).monic :=
  h.recovered.monic_dvd

end MonicDescent

/--
Descent-only package for the to-monic reverse direction.

Unlike `HenselLiftDescentHypotheses`, this package does not claim that a lifted
representation of the original non-monic factor descends to a mod-`p`
representation of that same factor.  It descends to the monic correspondent
recorded by `RecoveredAtLift`, while retaining the dilation equality back to the
original factor.
-/
structure MonicDescentHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (successfulLift coprimeLift : Prop) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  successful_lift : successfulLift
  coprime_lift : coprimeLift
  descends :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ (S : ModPFactorSubset primeData) (hrec : RecoveredAtLift core d factor T),
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData hrec.monicFactor S

namespace MonicDescentHypotheses

/--
Existential form for consumers that want the subset, recovered witness, and
monic mod-`p` representation without depending on the carrier's field names.
-/
theorem exists_descent
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {successfulLift coprimeLift : Prop}
    (h : MonicDescentHypotheses core B primeData d successfulLift coprimeLift)
    {T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor T) :
    ∃ (S : ModPFactorSubset primeData) (hrec : RecoveredAtLift core d factor T),
      T = liftedSubsetOfModPSubset primeData d h.factor_count_eq S ∧
        RepresentsIntegerFactorModP primeData hrec.monicFactor S :=
  h.descends hirr hdvd hrep

/-- Carrier form of `exists_descent`, for consumers that prefer named fields. -/
theorem exists_carrier
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {successfulLift coprimeLift : Prop}
    (h : MonicDescentHypotheses core B primeData d successfulLift coprimeLift)
    {T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor T) :
    ∃ _ : MonicDescent core primeData d factor T h.factor_count_eq, True := by
  rcases h.exists_descent hirr hdvd hrep with ⟨S, hrec, hT, hmod⟩
  exact ⟨MonicDescent.ofRecovered S hT hrec hmod, trivial⟩

end MonicDescentHypotheses

/-- **Lift-stage pairwise-disjointness.** Non-associated irreducible integer
divisors of `core` are represented by disjoint subsets of the lifted local
factors.  This is the lift-stage sibling of
`modPFactorSubset_disjoint_of_not_associated`: descend each lifted
representation to its unique mod-`p` subset via the descent package, apply the
mod-`p` disjointness theorem, and reflect disjointness back through
`liftedSubsetOfModPSubset`.  No `LiftedFactorSubsetPartition` /
`InitialLiftedFactorSubsetPartitionEvidence` is assumed; this lemma is what a
non-circular producer of the `pairwise_disjoint` field calls. -/
theorem representsIntegerFactorAtLift_disjoint_of_not_associated
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hprime : Hex.Nat.Prime primeData.p)
    (hmod :
      ModPSubsetPartitionHypotheses core primeData admissiblePrime squareFreeReduction)
    (hcore_modP_nz :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false)
    (hsqfree :
      Squarefree
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (@monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))))
    (hdescent :
      HenselLiftDescentHypotheses core B primeData d successfulLift coprimeLift)
    {f g : Hex.ZPoly} {S T : LiftedFactorSubset d}
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f)) (hf_dvd : f ∣ core)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g)) (hg_dvd : g ∣ core)
    (hS : RepresentsIntegerFactorAtLift core d f S)
    (hT : RepresentsIntegerFactorAtLift core d g T)
    (hnotassoc :
      ¬ Associated (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)) :
    Disjoint S T := by
  -- Descend each lifted representation to its unique mod-`p` subset.
  obtain ⟨S₀, hS_eq, hS_mod⟩ :=
    hdescent.represents_modP_of_lifted hf_irr hf_dvd hS
  obtain ⟨T₀, hT_eq, hT_mod⟩ :=
    hdescent.represents_modP_of_lifted hg_irr hg_dvd hT
  -- Disjointness holds at the mod-`p` level for the descended subsets.
  have hdisj0 : Disjoint S₀ T₀ :=
    modPFactorSubset_disjoint_of_not_associated hprime hmod hcore_modP_nz hsqfree
      hf_irr hf_dvd hg_irr hg_dvd hS_mod hT_mod hnotassoc
  -- Reflect disjointness back through the canonical lift.
  rw [hS_eq, hT_eq]
  exact
    (liftedSubsetOfModPSubset_disjoint_iff primeData d hdescent.factor_count_eq S₀ T₀).mpr
      hdisj0

/--
Non-circular assembly of `HenselSubsetLiftHypotheses` from explicit forward
Hensel transport and lifted-side descent.
-/
theorem henselSubsetLiftHypotheses_of_forwardTransport_descent
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hadmissible : admissiblePrime)
    (hsquareFree : squareFreeReduction)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData d
        successfulLift coprimeLift)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hdescent.factor_count_eq S)) :
    HenselSubsetLiftHypotheses core B primeData d
      admissiblePrime squareFreeReduction successfulLift coprimeLift where
  lift_eq := hdescent.lift_eq
  factor_count_eq := hdescent.factor_count_eq
  admissible_prime := hadmissible
  square_free_reduction := hsquareFree
  successful_lift := hdescent.successful_lift
  coprime_lift := hdescent.coprime_lift
  represents_lifted_of_modP := by
    intro factor S hirr hdvd hrep
    exact hlifted_of_modP hirr hdvd hrep
  represents_modP_of_lifted := by
    intro factor T hirr hdvd hrep
    exact hdescent.represents_modP_of_lifted hirr hdvd hrep

/--
The mod-`p` subset selected for an irreducible integer factor has a unique
lifted representative through the Hensel transport package.
-/
theorem existsUnique_modPSubset_lifting_to_henselRepresentation
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S ∧
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hlift.factor_count_eq S) := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  refine ⟨S, ⟨hS_mod, hlift.represents_lifted_of_modP hirr hdvd hS_mod⟩, ?_⟩
  intro T hT
  exact hmod.unique_subset hirr hdvd hT.1 hS_mod

/--
Composing the mod-`p` subset partition with Hensel-lift transport gives the
caller-facing lifted-factor subset correspondence.
-/
theorem existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  let liftedS := liftedSubsetOfModPSubset primeData d hlift.factor_count_eq S
  have hS_lift : RepresentsIntegerFactorAtLift core d factor liftedS :=
    hlift.represents_lifted_of_modP hirr hdvd hS_mod
  refine ⟨liftedS, hS_lift, ?_⟩
  intro T hT
  rcases hlift.represents_modP_of_lifted hirr hdvd hT with ⟨U, hT_eq, hU_mod⟩
  have hUS : U = S :=
    hmod.unique_subset hirr hdvd hU_mod hS_mod
  rw [hT_eq, hUS]

/--
The mod-`p` partition plus Hensel transport produces the existing
`HenselSubsetCorrespondenceHypotheses` package, so downstream callers can
use the stable lifted-factor API without depending on the intermediate
mod-`p` vocabulary.
-/
def henselSubsetCorrespondence_of_modPSubsetPartition
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift) :
    HenselSubsetCorrespondenceHypotheses core B primeData d
      admissiblePrime successfulLift where
  lift_eq := hlift.lift_eq
  admissible_prime := hlift.admissible_prime
  successful_lift := hlift.successful_lift
  exists_subset := by
    intro factor _hsign hirr hdvd
    exact
      (existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
        hmod hlift hirr hdvd).exists
  unique_subset := by
    intro factor S T hirr hdvd hS hT
    rcases
      existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
        hmod hlift hirr hdvd with
      ⟨U, hU, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/-- The `Hex.centeredLiftPoly` operation is invariant under prior reduction by
the same modulus. -/
private theorem centeredLiftPoly_reduceModPow_eq
    (f : Hex.ZPoly) (p k : Nat) (hp : 0 < p) :
    Hex.centeredLiftPoly (Hex.ZPoly.reduceModPow f p k) (p ^ k) =
      Hex.centeredLiftPoly f (p ^ k) := by
  have hpkpos : 0 < p ^ k := Nat.pow_pos hp
  have hpkne : p ^ k ≠ 0 := Nat.ne_of_gt hpkpos
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.coeff_centeredLiftPoly, Hex.coeff_centeredLiftPoly,
    Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpkpos]
  unfold Hex.centeredModNat
  rw [if_neg hpkne, if_neg hpkne, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- Precision-gated exact recovery for `liftedRecoveryCandidate` in the
dilation-coordinate model. -/
theorem liftedRecoveryCandidate_eq_factor_of_congruence_of_bound
    {core factor monicFactor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (monicFactor.coeff i).natAbs ≤ B')
    (hcong :
      Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
        Hex.ZPoly.reduceModPow monicFactor d.p d.k)
    (hdilate :
      Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
        factor)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hprecision : 2 * B' < d.p ^ d.k) :
    liftedRecoveryCandidate core d S = factor := by
  have hcl :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = monicFactor := by
    rw [← centeredLiftPoly_reduceModPow_eq (liftedFactorProduct d S) d.p d.k d.p_pos,
      hcong]
    exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
      monicFactor d.p d.k B' hvalid hprecision
  unfold liftedRecoveryCandidate
  rw [hcl, hdilate]
  exact hfactor_norm

namespace RecoveredAtLift

/--
Exact recovery of the executable recovered candidate from the corrected
monic-coordinate representation carrier.
-/
theorem candidate_eq_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hrep : RecoveredAtLift core d factor S)
    (B' : Nat)
    (hvalid : ∀ i, (hrep.monicFactor.coeff i).natAbs ≤ B')
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hprecision : 2 * B' < d.p ^ d.k) :
    liftedRecoveryCandidate core d S = factor :=
  liftedRecoveryCandidate_eq_factor_of_congruence_of_bound
    B' hvalid hrep.congr hrep.dilate_eq hfactor_norm hprecision

/--
Exact recovery driven directly by the carrier's `monic_dvd` field.

This is the producer half of the recovery contract: the `monic_dvd` field
forces `monicFactor ∣ (toMonic core).monic`, so `defaultFactorCoeffBound_valid`
discharges the Mignotte coefficient bound at
`B' := defaultFactorCoeffBound (toMonic core).monic` with no separate validity
obligation on the caller.  The only remaining precision hypothesis is that the
Hensel modulus clears twice that bound.
-/
theorem candidate_eq_of_monic_dvd
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hrep : RecoveredAtLift core d factor S)
    (hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k) :
    liftedRecoveryCandidate core d S = factor :=
  hrep.candidate_eq_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic)
    (fun i =>
      defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hmonic_ne
        hrep.monicFactor hrep.monic_dvd i)
    hfactor_norm hprecision

end RecoveredAtLift

/--
Abstract-bound variant of
`centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision`: takes an
arbitrary `B' : Nat`, an explicit validity hypothesis
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and the scaled-product
congruence in place of the public representation predicate.  The body just
threads `B'` and `hvalid` into `centeredLiftPoly_eq_of_reduceModPow_eq`
(which already accepts an abstract bound).  The original core-shape theorem is
a wrapper around this variant.
-/
theorem centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.centeredLiftPoly
        (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
        (d.p ^ d.k) =
      factor :=
  Hex.centeredLiftPoly_eq_of_reduceModPow_eq
    factor (scaledLiftedFactorProduct core d S) d.p d.k
    B' hvalid hprecision hscaled

/--
Mignotte recoverability for one represented integer factor.

If the scaled selected lifted product is congruent to an integer divisor of
`core` modulo the Hensel modulus, and that modulus is beyond twice the default
Mignotte coefficient bound for `core`, then the executable centred-lift
operation recovers the integer factor exactly.

This is a thin wrapper over the abstract-bound variant
`centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
HO-1 callers should prefer the `_of_bound` variant directly with
`B' := defaultFactorCoeffBound f`, bypassing the squareFreeCore-bound
monotonicity obligation called out by
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`.
-/
theorem centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    Hex.centeredLiftPoly
        (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
        (d.p ^ d.k) =
      factor :=
  centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hscaled hprecision

end

end HexBerlekampZassenhausMathlib
