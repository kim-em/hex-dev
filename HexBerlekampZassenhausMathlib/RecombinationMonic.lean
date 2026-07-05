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

public import HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects monicness/squarefreeness of the recombination candidate and the degree cover.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-! ### Monicness of the executable recombination candidate -/

/--
Under monic lifted local factors and modulus `2 ≤ d.p ^ d.k`, the executable
recombination candidate `recombinationCandidate d T` is monic for every lifted
subset `T`.

The proof mirrors the chain inside
`natDegree_toPolynomial_recombinationCandidate_eq_sum`: the lifted-factor product
is monic by `liftedFactorProduct_monic`, the centered lift preserves monicness
under the modulus bound (`monic_centeredLiftPoly_of_monic`), and a monic
polynomial is fixed by `primitivePart` and `normalizeFactorSign` (via
`monic_primitive_sign_normalized_of_monic`), so the full normalisation chain
collapses to the centred lift, which is monic.
-/
theorem recombinationCandidate_monic
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    Hex.DensePoly.Monic (recombinationCandidate d T) := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hcl_monic :
      Hex.DensePoly.Monic (Hex.centeredLiftPoly lp (d.p ^ d.k)) :=
    monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  have hnorm : Hex.normalizeFactorSign (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
      Hex.centeredLiftPoly lp (d.p ^ d.k) :=
    zpoly_normalize_factor_sign_of_monic hcl_monic
  have hprim :
      Hex.ZPoly.primitivePart (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
        Hex.centeredLiftPoly lp (d.p ^ d.k) :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive _
      (zpoly_primitive_of_monic hcl_monic)
  have hrec_eq :
      recombinationCandidate d T = Hex.centeredLiftPoly lp (d.p ^ d.k) := by
    unfold recombinationCandidate
    rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct, ← hlp_def,
      hprim, hnorm]
  rw [hrec_eq]
  exact hcl_monic

/-- The `Polynomial ℤ` image of a monic-conditions recombination candidate is
monic. Caller-side packaging of `recombinationCandidate_monic` through
`HexPolyMathlib.leadingCoeff_toPolynomial`. -/
theorem toPolynomial_recombinationCandidate_monic
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic := by
  show (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T

/-- The `Polynomial ℤ` image of a recombination candidate inherits squarefreeness
from a square-free `target`, given `candidate ∣ target` (supplied by the
executable quotient witness `hquot`).

The reverse-coverage proof for the main candidate divisibility theorem
(see `representedFactor_dvd_recombinationCandidate_of_subset`, #4457) needs
`toPolynomial candidate` square-free to factor it into a Multiset of pairwise
non-associated irreducibles. -/
theorem toPolynomial_recombinationCandidate_squarefree
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) := by
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  exact Squarefree.squarefree_of_dvd
    (HexPolyMathlib.toPolynomial_dvd hcand_dvd_target) hpartition.target_squarefree

/-- Scaled-candidate counterpart of `toPolynomial_recombinationCandidate_squarefree`:
inherits squarefreeness from a squarefree `target` via the exact-quotient witness.
Consumed by the scaled `mem_T_iff_*` chain for the primitive recursive
recombination coverage proof (#4647 / #4737). -/
theorem toPolynomial_scaledRecombinationCandidate_squarefree
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient) :
    Squarefree (HexPolyZMathlib.toPolynomial
      (scaledRecombinationCandidate core d T)) := by
  have hmul : quotient * scaledRecombinationCandidate core d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : scaledRecombinationCandidate core d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  exact Squarefree.squarefree_of_dvd
    (HexPolyMathlib.toPolynomial_dvd hcand_dvd_target) hpartition.target_squarefree

/-- Abstract-bound variant of `exists_mem_representedSubset_of_degree_cover`:
takes `B' : Nat`, a per-factor coefficient bound
`hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. The per-factor
`natDegree` identity step now routes through the sound partition-based
`natDegree_toPolynomial_eq_sum_of_represents`, so the abstract-bound
hypotheses are no longer consumed by that step. -/
theorem exists_mem_representedSubset_of_degree_cover_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (_hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (_hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (_hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  -- Candidate-side: natDegree(recombinationCandidate d T) = ∑ j ∈ T, f j.
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_recombinationCandidate_eq_sum
      hd_modulus hd_liftedFactor_monic T
  -- Each represented factor: natDegree(g) = ∑ j ∈ S_of g, f j.
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    exact natDegree_toPolynomial_eq_sum_of_represents
      hcore_monic hd_modulus hd_liftedFactor_monic hpartition hg_irr hg_dvd
      hg_SJ hg_rep
  -- Pairwise disjointness of the representing subsets, via partition.
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  -- The biUnion is contained in T.
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  -- ∑ T f = ∑ (gs.biUnion S_of) f.
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  -- ∑ (T \ biUnion) f = 0 by additive splitting on the subset.
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  -- Positivity of each summand forces T \ biUnion to be empty.
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  -- Conclude pointwise coverage.
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/-- Reverse-coverage finite degree-counting step (issue #4468).

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose `gs` is a finite family of `Hex.ZPoly` elements such that each
`g ∈ gs` is

* an irreducible divisor of `target` and of `recombinationCandidate d T`,
* represented at the lift by a subset `S_of g ⊆ T ⊆ J`,
* primitive (`content = 1`) and sign-normalized,

and the family is pairwise non-associated in `Polynomial ℤ` (so that the
partition's `pairwise_disjoint` field makes the `S_of g` pairwise disjoint).
If the candidate's `natDegree` decomposes as the sum of the `natDegree`s of
the family, then every index `i ∈ T` lies in some `S_of g`.

This is the finite Finset bookkeeping ingredient of the reverse-coverage
existence lemma (successor split from #4465). It does not extract irreducible
factors itself; the downstream `mem_T_iff_exists_irreducibleFactor_representingSubset`
assembler (#4467) supplies `gs` from `UniqueFactorizationMonoid.normalizedFactors`
together with the non-association hypothesis.

This is a thin wrapper over `exists_mem_representedSubset_of_degree_cover_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hvalid` per-factor: each `g ∈ gs` divides `target` via `h_each`, hence divides
`core` via `htarget_dvd_core`, and `defaultFactorCoeffBound_valid` supplies the
coefficient bound. -/
theorem exists_mem_representedSubset_of_degree_cover
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  have hvalid : ∀ g ∈ gs, ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound core := by
    intro g hg i
    obtain ⟨_, hg_dvd_target, _, _, _, _, _, _⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
    exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i
  intro i hi
  exact exists_mem_representedSubset_of_degree_cover_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition
    htarget_dvd_core _hTJ gs S_of h_each hvalid
    h_pairwise_not_associated h_degree_total hi

/-- Abstract-bound variant of
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core`:
takes `B' : Nat`, a per-factor coefficient bound
`hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B'`, the leading-coefficient
bound `hcore_lc_le : (leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. The proof mirrors the
core-shape original but invokes the `_of_bound` sibling
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`
at the per-factor `natDegree` identity step. -/
theorem exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_recombinationCandidate_eq_sum
      hd_modulus hd_liftedFactor_monic T
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
      B' (hvalid g hg) hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hpartition hg_irr hg_dvd hg_SJ hg_rep hprecision
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/--
Primitive + positive-leading-core variant of
`exists_mem_representedSubset_of_degree_cover` (#4646 chain).

Identical to the monic variant except the per-factor natDegree identity routes
through `natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core`
instead of the monic-core version.

This is a thin wrapper over
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core`. The per-factor
`hvalid` is discharged via the divisor chain `g ∣ target ∣ core` plus
`defaultFactorCoeffBound_valid`; `hcore_lc_le` is discharged via
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self (core.size - 1)`
together with `leadingCoeff_eq_coeff_last`.
-/
theorem exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hvalid : ∀ g ∈ gs, ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound core := by
    intro g hg i
    obtain ⟨_, hg_dvd_target, _, _, _, _, _, _⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
    exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i
  intro i hi
  exact exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hd_modulus
    hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
    htarget_dvd_core _hTJ gs S_of h_each hvalid
    h_pairwise_not_associated h_degree_total hi

/--
Abstract-bound variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`:
takes a universal bound `B'` valid on every normalised `Polynomial ℤ` factor
of the recombination candidate, together with the precision hypothesis
`2 * B' < d.p ^ d.k`, in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The abstract bound is consumed only at the call to the abstract-bound
support-containment lemma
`representingSubset_subset_of_dvd_recombinationCandidate_of_bound`, which is
vestigial in precision (the structural support field of the partition does
not depend on it). The bound is threaded purely for API parity with the
broader `_of_bound` propagation chain. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly) (x := HexPolyZMathlib.toPolynomial (recombinationCandidate d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  have hg_norm_sign : Hex.normalizeFactorSign g = g := by
    apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlc :
        (HexPolyZMathlib.toPolynomial g).leadingCoeff =
          Hex.DensePoly.leadingCoeff g :=
      HexPolyMathlib.leadingCoeff_toPolynomial g
    rw [← hlc, hg_toPolynomial]
    exact Int.nonneg_of_normalize_eq_self hlead_normalized
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne hcore_monic hprecision hpartition hTJ hg_irr_toPoly
      hg_dvd_target hg_dvd_cand hSJ hSrep
  have hcand_monic_poly :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hg_monic_poly : gPoly.Monic := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic_poly.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic_poly.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hg_monic_hex : Hex.DensePoly.Monic g := by
    have hlead : (HexPolyZMathlib.toPolynomial g).leadingCoeff = 1 := by
      rw [hg_toPolynomial]
      exact hg_monic_poly
    rwa [HexPolyMathlib.leadingCoeff_toPolynomial] at hlead
  have hg_content : Hex.ZPoly.content g = 1 :=
    zpoly_primitive_of_monic hg_monic_hex
  have hg_norm_sign : Hex.normalizeFactorSign g = g :=
    zpoly_normalize_factor_sign_of_monic hg_monic_hex
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/--
Package a normalized irreducible factor of a recombination candidate as an
executable `Hex.ZPoly` factor with the represented subset facts needed by the
reverse-coverage degree argument.

The normalized-factor membership supplies an irreducible divisor of
`toPolynomial (recombinationCandidate d T)`. Since the candidate is monic, that
normalized divisor is monic too. Transporting the divisor back through
`HexPolyZMathlib.ofPolynomial` gives a `Hex.ZPoly` divisor of the candidate and
hence of `target`; the partition then provides its representing subset, and the
support-containment field forces that subset to lie in `T`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via `htarget_dvd_core`),
so `defaultFactorCoeffBound_valid` discharges the universal bound hypothesis.
-/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic hprecision
    hpartition htarget_dvd_core hTJ hrecord hquot hg_mem
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the candidate
  -- by chaining `g ∣ candidate ∣ target ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core`:
takes a universal bound `B'` valid on every normalised `Polynomial ℤ` factor
of the recombination candidate, together with the precision hypothesis
`2 * B' < d.p ^ d.k`, in place of the core-shape `defaultFactorCoeffBound core`
precision constraint.

As in the support-containment chain, the abstract bound is consumed only at
the call to
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound`,
which is vestigial in precision (the structural support field of the
partition does not depend on it). The bound is threaded purely for API parity
with the broader `_of_bound` propagation chain. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly) (x := HexPolyZMathlib.toPolynomial (recombinationCandidate d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_target with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  have hg_norm_sign : Hex.normalizeFactorSign g = g := by
    apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlc :
        (HexPolyZMathlib.toPolynomial g).leadingCoeff =
          Hex.DensePoly.leadingCoeff g :=
      HexPolyMathlib.leadingCoeff_toPolynomial g
    rw [← hlc, hg_toPolynomial]
    exact Int.nonneg_of_normalize_eq_self hlead_normalized
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne hcore_primitive hcore_lc_pos hcore_monic hprecision hpartition hTJ
      hg_irr_toPoly hg_dvd_target hg_dvd_cand hSJ hSrep
  have hcand_monic_poly :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hg_monic_poly : gPoly.Monic := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic_poly.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic_poly.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hg_monic_hex : Hex.DensePoly.Monic g := by
    have hlead : (HexPolyZMathlib.toPolynomial g).leadingCoeff = 1 := by
      rw [hg_toPolynomial]
      exact hg_monic_poly
    rwa [HexPolyMathlib.leadingCoeff_toPolynomial] at hlead
  obtain ⟨_, hg_content, hg_norm_sign⟩ :=
    monic_primitive_sign_normalized_of_monic hg_monic_hex
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/-- Primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`
(#4646 chain).

The monic-core hypothesis is threaded only through
`representingSubset_subset_of_dvd_recombinationCandidate` (vestigial there);
all essential algebra runs on the always-monic recombination candidate, so
the proof body is identical to the monic version except for the routing
through the primitive-core variants of the helpers.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via `htarget_dvd_core`),
so `defaultFactorCoeffBound_valid` discharges the universal bound hypothesis. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_primitive hcore_lc_pos hcore_monic hd_modulus hd_liftedFactor_monic
    hprecision hpartition htarget_dvd_core hTJ hrecord hquot hg_mem
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the candidate
  -- by chaining `g ∣ candidate ∣ target ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Reverse-coverage existence theorem for the recombination candidate.

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose the candidate `recombinationCandidate d T` is recordable and admits an
exact quotient against `target`. Then every local index `i ∈ T` lies in the
representing subset `S_g` of some irreducible `Hex.ZPoly` divisor `g` of the
candidate, with `S_g ⊆ J`.

The proof packages the UFD normalized factorisation of
`HexPolyZMathlib.toPolynomial (recombinationCandidate d T)` through the
per-factor lemma `exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`
(#4467), then closes the degree-counting obligation of
`exists_mem_representedSubset_of_degree_cover` (#4468) using monicness and
squarefreeness of the candidate together with
`Polynomial.natDegree_multiset_prod_of_monic`.

Together with the forward divisor extraction
`exists_representingSubset_dvd_recombinationCandidate_of_exactQuotient`, this
theorem supplies the bidirectional content the main candidate divisibility
theorem (#4457) needs to relate every `i ∈ T` to a partition-representing
irreducible divisor of the recombination candidate. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  -- Candidate properties: nonzero, monic, squarefree.
  have hcand_ne :
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_monic :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hcand_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) :=
    toPolynomial_recombinationCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) with hnf_def
  -- Squarefreeness ↦ Nodup of the normalized factor multiset.
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hcand_ne).mp
      hcand_squarefree
  -- Per-normalized-factor monicness: each normalized divisor of a monic poly is monic.
  have hnf_monic : ∀ gPoly ∈ normFactors, gPoly.Monic := by
    intro gPoly hgPoly
    have hg_norm_eq : normalize gPoly = gPoly :=
      UniqueFactorizationMonoid.normalize_normalized_factor gPoly hgPoly
    have hg_dvd_cand :
        gPoly ∣ HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hgPoly
    obtain ⟨r, hr⟩ := hg_dvd_cand
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have := congrArg Polynomial.leadingCoeff hg_norm_eq
      rwa [Polynomial.leadingCoeff_normalize] at this
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  -- Product of normalized factors equals the (monic) candidate.
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_ne,
      hcand_monic.normalize_eq_self]
  -- Per-normalized-factor data, indexed by hex factor `g = ofPolynomial gPoly`.
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ recombinationCandidate d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
        B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic hprecision
        hpartition htarget_dvd_core hTJ hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  -- Choose `S_of g` via the lemma for `g`'s normalized-factor membership.
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  -- Membership in `gs` is membership of `toPolynomial g` in `normFactors`.
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  -- Per-element data for `exists_mem_representedSubset_of_degree_cover`.
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  -- Pairwise non-association via normalize_eq + injectivity of `toPolynomial`.
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  -- Degree of candidate equals the sum of degrees of `gs` (via prod of monic).
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod_of_monic _ hnf_monic]
  -- Apply the finite degree-cover lemma.
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_bound
      B' hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      gs S_of h_each (fun g hg => hvalid g (mem_gs.mp hg))
      h_pairwise h_degree_total hi
  -- Extract the witness for `g`.
  have hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Default-bound wrapper for
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound`. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
    hTJ hrecord hquot hi
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Primitive + positive-leading-core variant of
`mem_T_iff_exists_irreducibleFactor_representingSubset` (#4646 chain).

Same proof structure as the monic variant, but the per-factor representing
subset is obtained via
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core`
and the final degree-cover application uses the primitive-core variant
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core`.
-/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_ne :
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_monic :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hcand_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) :=
    toPolynomial_recombinationCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) with hnf_def
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hcand_ne).mp
      hcand_squarefree
  have hnf_monic : ∀ gPoly ∈ normFactors, gPoly.Monic := by
    intro gPoly hgPoly
    have hg_norm_eq : normalize gPoly = gPoly :=
      UniqueFactorizationMonoid.normalize_normalized_factor gPoly hgPoly
    have hg_dvd_cand :
        gPoly ∣ HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hgPoly
    obtain ⟨r, hr⟩ := hg_dvd_cand
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have := congrArg Polynomial.leadingCoeff hg_norm_eq
      rwa [Polynomial.leadingCoeff_normalize] at this
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_ne,
      hcand_monic.normalize_eq_self]
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ recombinationCandidate d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
        B' hvalid hcore_ne hcore_primitive hcore_lc_pos hcore_monic hd_modulus
        hd_liftedFactor_monic hprecision hpartition htarget_dvd_core hTJ
        hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod_of_monic _ hnf_monic]
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
      B' hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ gs S_of h_each
      (fun g hg => hvalid g (mem_gs.mp hg)) h_pairwise h_degree_total hi
  have hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Primitive + positive-leading-core variant of
`mem_T_iff_exists_irreducibleFactor_representingSubset` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound`.
-/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' i => by
      have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
      have hg_dvd_cand : g ∣ recombinationCandidate d T := by
        rcases hg_poly_dvd with ⟨r, hr⟩
        refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
        apply HexPolyZMathlib.equiv.injective
        simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
          HexPolyZMathlib.toPolynomial_ofPolynomial]
        exact hr
      have hg_dvd_core : g ∣ core := by
        rcases hg_dvd_cand with ⟨r₁, hr₁⟩
        rcases hcand_dvd_core with ⟨r₂, hr₂⟩
        refine ⟨r₁ * r₂, ?_⟩
        rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
      exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
    hcore_ne hcore_primitive hcore_lc_pos hcore_monic
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi

/--
Package reverse candidate support in the form consumed by the cover-at-min
assembler: every selected local index in a recorded recombination candidate
belongs to the representing subset of an irreducible integer factor that
divides both the recursive target and the candidate.
-/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  obtain ⟨f, S, hf_irr, hf_dvd_candidate, hrep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      hrecord hquot hi
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_candidate hcand_dvd_target
  exact ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_candidate, hSJ, hiS, hrep⟩

/-- Default-bound wrapper for
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound`. -/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
    hTJ hrecord hquot hi
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/--
Cover-at-min containment from recombination-candidate support: when the
recorded candidate at `T ⊆ J` exactly divides `target`, the cover witness at
`J.min'` has its representing subset contained in `T`.

This is the form consumed by the prefix-none recombination-search assembler:
it combines the reverse-support coverage packaging
(`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd`) applied
at `i := J.min' hne` with the forward-support containment
(`representingSubset_subset_of_dvd_recombinationCandidate`) to obtain the
single cover factor whose representing subset both contains `J.min' hne`
and is contained in `T`.
-/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_cand, hSJ, hmin_in_S, hrep⟩ :=
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      hrecord hquot hmin_in_T
  have hST : S ⊆ T :=
    hpartition.support_subset_of_dvd_recombinationCandidate
      hf_irr hf_dvd_target hTJ
      hcore_monic
      (by
        rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
        exact hf_dvd_cand)
      hSJ hrep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hmin_in_S, hrep, hST⟩

/-- Default-bound wrapper for
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound`. -/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
    hne hmin_in_T hrecord hquot
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd` (#4646 chain).

Routes through the abstract-bound
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound`
supporting lemma; the remaining divisor repackaging is precision-agnostic. -/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  obtain ⟨f, S, hf_irr, hf_dvd_candidate, hrep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
      B' hvalid hcore_ne hcore_primitive hcore_lc_pos hcore_monic hcore_lc_le
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_candidate hcand_dvd_target
  exact ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_candidate, hSJ, hiS, hrep⟩

/-- Primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      (Hex.ZPoly.defaultFactorCoeffBound core)
      (fun g hg_mem' i => by
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core := by
          rcases hg_dvd_cand with ⟨r₁, hr₁⟩
          rcases hcand_dvd_core with ⟨r₂, hr₂⟩
          refine ⟨r₁ * r₂, ?_⟩
          rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
        exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
      hcore_ne hcore_primitive hcore_lc_pos
      hcore_monic
      (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi

/-- Abstract-bound primitive + positive-leading-core variant of
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd` (#4646 chain).

Routes through
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`
and
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound`. -/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_cand, hSJ, hmin_in_S, hrep⟩ :=
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      B' hvalid hcore_ne hcore_primitive hcore_lc_pos hcore_monic hcore_lc_le
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hmin_in_T
  have hvalid_f : ∀ i, (f.coeff i).natAbs ≤ B' := by
    have hcand_poly_ne_zero :
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
    have hf_poly_dvd :
        HexPolyZMathlib.toPolynomial f ∣
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
      rcases hf_dvd_cand with ⟨r, hr⟩
      refine ⟨HexPolyZMathlib.toPolynomial r, ?_⟩
      rw [← HexPolyZMathlib.toPolynomial_mul, hr]
    obtain ⟨gPoly, hg_mem, hg_assoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hcand_poly_ne_zero hf_irr hf_poly_dvd
    let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
    have hg_toPoly : HexPolyZMathlib.toPolynomial g = gPoly :=
      HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
    have hg_bound : ∀ i, (g.coeff i).natAbs ≤ B' :=
      hvalid g (by rw [hg_toPoly]; exact hg_mem)
    obtain ⟨u, hu⟩ := hg_assoc
    obtain ⟨c, hc_unit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have hc_abs_one : c.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hc_unit
    intro i
    have hg_coeff : g.coeff i = gPoly.coeff i := by
      have := HexPolyZMathlib.coeff_toPolynomial g i
      rw [hg_toPoly] at this
      exact this.symm
    have hgPoly_coeff_f : gPoly.coeff i = f.coeff i * c := by
      have hmul : (HexPolyZMathlib.toPolynomial f * Polynomial.C c).coeff i =
          (HexPolyZMathlib.toPolynomial f).coeff i * c :=
        Polynomial.coeff_mul_C _ _ _
      rw [← hu, ← hcu, hmul, HexPolyZMathlib.coeff_toPolynomial]
    have hbound := hg_bound i
    rw [hg_coeff, hgPoly_coeff_f, Int.natAbs_mul, hc_abs_one,
      Nat.mul_one] at hbound
    exact hbound
  have hST : S ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' hvalid_f hcore_ne hcore_primitive hcore_lc_pos hcore_monic hprecision
      hpartition hTJ hf_irr hf_dvd_target hf_dvd_cand hSJ hrep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hmin_in_S, hrep, hST⟩

/-- Primitive + positive-leading-core variant of
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact
    coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      (Hex.ZPoly.defaultFactorCoeffBound core)
      (fun g hg_mem' i => by
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core := by
          rcases hg_dvd_cand with ⟨r₁, hr₁⟩
          rcases hcand_dvd_core with ⟨r₂, hr₂⟩
          refine ⟨r₁ * r₂, ?_⟩
          rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
        exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
      hcore_ne hcore_primitive hcore_lc_pos hcore_monic
      (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hne hmin_in_T hrecord hquot

end

end HexBerlekampZassenhausMathlib
