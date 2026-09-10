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

public import HexBerlekampZassenhausMathlib.ModPFactor
public import HexBerlekampZassenhausMathlib.FactorBound
import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor

public section
set_option backward.proofsInPublic true

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
@[expose]
def modPIndexToLiftedEmbedding
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    ModPFactorIndex primeData ↪ LiftedFactorIndex d where
  toFun := liftedIndexOfModPIndex primeData d hsize
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval :=
      congrArg (fun x : LiftedFactorIndex d => x.val) hij
    simpa [liftedIndexOfModPIndex] using hval

/--
Transport a selected subset of modular factors to the corresponding selected
subset of lifted factors, once the lift stage is known to preserve factor count.
-/
@[expose]
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
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hji' :
        (modPIndexToLiftedEmbedding primeData d hsize) j =
          (modPIndexToLiftedEmbedding primeData d hsize) i := by
      exact hji
    exact (modPIndexToLiftedEmbedding primeData d hsize).injective hji' ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

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
square-free part, matching the product formed by the executable recombination candidate
checker.
-/
@[expose]
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
  /-- The monic-coordinate factor represented by the selected lifted factors. -/
  monicFactor : Hex.ZPoly
  /-- The selected lifted product agrees with the monic factor modulo the lift modulus. -/
  congr :
    Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
      Hex.ZPoly.reduceModPow monicFactor d.p d.k
  /-- Dilation by the input leading coefficient recovers the original factor. -/
  dilate_eq :
    Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
      factor
  /-- The monic-coordinate factor divides the transformed input. -/
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
square-free part from a selected lifted-factor product.  The selected product is first
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

/-- On monic square-free parts, the recovered non-monic candidate collapses to the existing
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
  /-- The lift data is the lift selected from these inputs. -/
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  /-- The selected prime satisfies the caller's admissibility condition. -/
  admissible_prime : admissiblePrime
  /-- The multifactor Hensel lift satisfies the caller's success condition. -/
  successful_lift : successfulLift
  /-- Every normalized irreducible divisor has a representing lifted subset. -/
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Hex.normalizeFactorSign factor = factor →
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃ S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S
  /-- The lifted subset representing an irreducible divisor is unique. -/
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor S →
      RepresentsIntegerFactorAtLift core d factor T →
      S = T


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
  /-- The lift data is the lift selected from these inputs. -/
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  /-- The lift preserves the number of modular factors. -/
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  /-- The selected prime satisfies the caller's admissibility condition. -/
  admissible_prime : admissiblePrime
  /-- Reduction modulo the selected prime preserves square-freeness. -/
  square_free_reduction : squareFreeReduction
  /-- The multifactor Hensel lift satisfies the caller's success condition. -/
  successful_lift : successfulLift
  /-- The lifted factors satisfy the caller's coprimality condition. -/
  coprime_lift : coprimeLift
  /-- A modular representation gives a representation by the corresponding lifted factors. -/
  represents_lifted_of_modP :
    ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorModP primeData factor S →
      RepresentsIntegerFactorAtLift core d factor
        (liftedSubsetOfModPSubset primeData d factor_count_eq S)
  /-- Every lifted representation descends to a corresponding modular representation. -/
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
  /-- The lift data is the lift selected from these inputs. -/
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  /-- The lift preserves the number of modular factors. -/
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  /-- The multifactor Hensel lift satisfies the caller's success condition. -/
  successful_lift : successfulLift
  /-- The lifted factors satisfy the caller's coprimality condition. -/
  coprime_lift : coprimeLift
  /-- Every lifted representation descends to a corresponding modular representation. -/
  represents_modP_of_lifted :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ S : ModPFactorSubset primeData,
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData factor S

/--
Data-bearing reverse descent from a monic-coordinate lift.

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
  /-- The modular subset underlying the selected lifted factors. -/
  modPSubset : ModPFactorSubset primeData
  /-- Lifting the modular subset gives the original lifted subset. -/
  subset_eq : T = liftedSubsetOfModPSubset primeData d hsize modPSubset
  /-- The lifted subset recovers the original-coordinate factor. -/
  recovered : RecoveredAtLift core d factor T
  /-- The modular subset represents the recovered monic-coordinate factor. -/
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
  /-- The lift data is the lift selected from these inputs. -/
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  /-- The lift preserves the number of modular factors. -/
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  /-- The multifactor Hensel lift satisfies the caller's success condition. -/
  successful_lift : successfulLift
  /-- The lifted factors satisfy the caller's coprimality condition. -/
  coprime_lift : coprimeLift
  /-- A lifted representation descends to its modular subset and monic correspondent. -/
  descends :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ (S : ModPFactorSubset primeData) (hrec : RecoveredAtLift core d factor T),
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData hrec.monicFactor S

namespace MonicDescentHypotheses


end MonicDescentHypotheses


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
  rw [ite_eq_right hpkne, ite_eq_right hpkne, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- Precision-conditional exact recovery for `liftedRecoveryCandidate` in the
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
(which already accepts an abstract bound).  The original input-shape theorem is
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
  callers should prefer the `_of_bound` variant directly with
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
