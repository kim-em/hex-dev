/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.IntReductionMod
public import HexBerlekampZassenhausMathlib.CLDColumnBound
public import HexBerlekampZassenhausMathlib.Classical.SupportPartition
public import HexBerlekampZassenhausMathlib.Hensel.DirectLift
public import HexBerlekampZassenhausMathlib.Lattice.CandidateCorrectness
public import HexBerlekampZassenhausMathlib.Lattice.DirectRecovery
public import HexBerlekampZassenhausMathlib.Lattice.DirectSupport
public import HexBerlekampZassenhausMathlib.Modular.PrimePlan
public import HexBerlekampZassenhausMathlib.Recovery
public import HexBerlekampZassenhausMathlib.PartitionRefinement
public import HexBerlekampZassenhausMathlib.Termination
public import HexGramSchmidtMathlib.Int.Swap
public import HexLLLMathlib.ShortVector
public import Mathlib.FieldTheory.Perfect

import all HexBerlekampZassenhausMathlib.RecombinationSplit

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate CLD adequacy

`DirectAdequacy` is the central proof boundary.  It packages the semantic lift,
exact-recovery precision, genuine-support partition, local divisibility, and
short CLD vectors.  The ordinary recovery floor proves the forward inclusion
`W ≤ L'`, which is enough for split irreducibility and the single-all-ones
certificate.  A larger resultant bound additionally proves `L' ≤ W`.

Every polynomial and support in this module is expressed in the original
coordinates and uses `Hex.ZPoly.directLiftData`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial



/-!
# Lattice geometry

The van Hoeij knapsack basis `[I_r | Ã; 0 | diag(p^(a-l_j))]` is upper-triangular
with strictly positive diagonal (1's in the `I_r` block, `p^(a-l_j)` in the
`D` block), so its rows are LLL-independent.  This is the entry condition to the
proven LLL short-vector bound `HexLLLMathlib.lllNative_first_row_norm_sq_le`.
-/

/-- The BHKS knapsack lattice basis is upper-triangular: below-diagonal entries
vanish.  Follows from the block structure `[I_r | Ã; 0 | diag]`. -/
theorem bhksLatticeBasis_basis_lowerZero
    (f : Hex.ZPoly) (p a : Nat) (lifted : Array Hex.ZPoly)
    (i j : Fin (lifted.size + (f.degree?.getD 0)))
    (hji : j.val < i.val) :
    (Hex.bhksLatticeBasis f p a lifted).basis[i][j] = 0 := by
  simp only [Hex.bhksLatticeBasis]
  erw [Hex.Matrix.getElem_ofFn]
  simp only [Fin.eta]
  by_cases hi : i.val < lifted.size
  · -- i in the I_r block ⟹ j < i < r, top-left identity off-diagonal is 0.
    have hj : j.val < lifted.size := by omega
    rw [Hex.bhksLatticeEntry_topLeft _ _ _ _ _ _ i j hi hj]
    have : i.val ≠ j.val := by omega
    simp [this]
  · -- i in the D block.
    have hir : lifted.size ≤ i.val := by omega
    by_cases hj : j.val < lifted.size
    · exact Hex.bhksLatticeEntry_bottomLeft _ _ _ _ _ _ i j hir hj
    · have hjr : lifted.size ≤ j.val := by omega
      exact Hex.bhksLatticeEntry_bottomRight_offDiag _ _ _ _ _ _ i j hir hjr (by omega)

/-- The BHKS knapsack lattice basis has strictly positive diagonal (needs
`0 < p`): `1` in the `I_r` block, `p^(a-l_j) > 0` in the `D` block. -/
theorem bhksLatticeBasis_basis_diagPos
    (f : Hex.ZPoly) (p a : Nat) (hp : 0 < p) (lifted : Array Hex.ZPoly)
    (i : Fin (lifted.size + (f.degree?.getD 0))) :
    0 < (Hex.bhksLatticeBasis f p a lifted).basis[i][i] := by
  simp only [Hex.bhksLatticeBasis]
  erw [Hex.Matrix.getElem_ofFn]
  simp only [Fin.eta]
  by_cases hi : i.val < lifted.size
  · rw [Hex.bhksLatticeEntry_topLeft _ _ _ _ _ _ i i hi hi]
    simp
  · have hir : lifted.size ≤ i.val := by omega
    rw [Hex.bhksLatticeEntry_bottomRight_diag _ _ _ _ _ _ i hir]
    exact Int.ofNat_lt.mpr (Nat.pow_pos hp)

/-- The BHKS knapsack lattice basis is LLL-independent
(`Hex.Matrix.independent`), so the proven LLL short-vector bound applies to it. -/
theorem bhksLatticeBasis_basis_independent
    (f : Hex.ZPoly) (p a : Nat) (hp : 0 < p) (lifted : Array Hex.ZPoly) :
    (Hex.bhksLatticeBasis f p a lifted).basis.independent := by
  intro k
  exact Hex.GramSchmidt.Int.gramDet_pos_of_upperTriangular_pos_diag
    (Hex.bhksLatticeBasis f p a lifted).basis
    (fun i j hji => bhksLatticeBasis_basis_lowerZero f p a lifted i j hji)
    (fun i => bhksLatticeBasis_basis_diagPos f p a hp lifted i)
    (k.val + 1) (Nat.succ_le_of_lt k.isLt) (Nat.succ_pos _)

/-- The first row of the LLL-reduced BHKS knapsack
lattice is a short vector: its squared Euclidean norm is bounded by the LLL
approximation factor `(1/(δ-1/4))^(n-1)` (at `δ = 3/4`) times the squared norm
of *any* nonzero lattice vector.  This is the direct application of the proven
`HexLLLMathlib.lllNative_first_row_norm_sq_le` to the BHKS basis,
using `bhksLatticeBasis_basis_independent`.  It is the concrete "the LLL-reduced
basis contains a short vector" fact that the van Hoeij adequacy argument feeds:
the true-factor `0-1` indicator vectors are short lattice vectors, so the reduced
basis's leading vector is at least as short. -/
theorem bhksLatticeBasis_lllNative_first_row_short
    (f : Hex.ZPoly) (p a : Nat) (hp : 0 < p) (lifted : Array Hex.ZPoly)
    (hn : 1 ≤ (Hex.bhksLatticeBasis f p a lifted).factorCount
      + (Hex.bhksLatticeBasis f p a lifted).coeffWidth)
    (x : Fin ((Hex.bhksLatticeBasis f p a lifted).factorCount
      + (Hex.bhksLatticeBasis f p a lifted).coeffWidth) → ℤ)
    (hx : x ∈ HexLLLMathlib.latticeSubmodule (Hex.bhksLatticeBasis f p a lifted).basis)
    (hx0 : x ≠ 0) :
    ‖HexLLLMathlib.intRowToEuclidean
        (Hex.Matrix.row
          (Hex.lllNative (Hex.bhksLatticeBasis f p a lifted).basis (3 / 4)
            Hex.lll_delta_lower Hex.lll_delta_upper hn)
          ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)‖ ^ 2 ≤
      (((1 / ((3 : Rat) / 4 - 1 / 4)) ^
          (((Hex.bhksLatticeBasis f p a lifted).factorCount
            + (Hex.bhksLatticeBasis f p a lifted).coeffWidth) - 1) : Rat) : ℝ) *
        ‖HexLLLMathlib.intVectorToEuclidean x‖ ^ 2 :=
  HexLLLMathlib.lllNative_first_row_norm_sq_le
    (Hex.bhksLatticeBasis f p a lifted).basis (3 / 4)
    Hex.lll_delta_lower Hex.lll_delta_upper hn
    (bhksLatticeBasis_basis_independent f p a hp lifted) x hx hx0


/-!
# The `W ⊆ L'` adequacy assembly

Both executable certificates use the count lower bound
`(normalizedFactors (toPolynomial core)).card ≤
  (bhksEquivalenceClassIndicators …).size`: each irreducible factor of `core`
yields a true lifted-factor support whose `0/1` indicator is the first block of
a short vector of the direct-coordinate BHKS lattice
(`BHKS.supportShortVectorData_of_recoveredLift`); the Gram-Schmidt
prefix-survivor lemma places it in the projected row span (`W ⊆ L'`,
`BHKS.cutProjectionHypotheses_of_shortVectors`), so the RREF signature classes
refine the true-support partition
(`BHKS.supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size`),
whose length `DirectAdequacy.factorCount` identifies with the number of
irreducible factors of `core`.
-/

private theorem foldl_max_le_init (l : List Nat) (g : Nat → Nat) (acc : Nat) :
    acc ≤ l.foldl (fun a j => max a (g j)) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem le_foldl_max {g : Nat → Nat} :
    ∀ {l : List Nat} {j : Nat}, j ∈ l →
      ∀ acc, g j ≤ l.foldl (fun a j => max a (g j)) acc := by
  intro l
  induction l with
  | nil => intro j hj; cases hj
  | cons x xs ih =>
      intro j hj acc
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_le_init _ _ _)
      · exact ih hj' _

/-- Every direct CLD column bound is dominated by the CLD floor. -/
theorem two_mul_bhksCoeffBound_le_cldCoeffFloor (core : Hex.ZPoly) (j : Nat) :
    2 * Hex.bhksCoeffBound core j ≤
      Hex.cldCoeffFloor core := by
  by_cases hj : j ≤ core.degree?.getD 0
  · have hmem : j ∈ List.range (core.degree?.getD 0 + 1) :=
      List.mem_range.mpr (by omega)
    have hle := le_foldl_max
      (g := fun j => Hex.bhksCoeffBound core j) hmem 0
    simp only [Hex.cldCoeffFloor]
    omega
  · have hz : Hex.bhksCoeffBound core j = 0 := by
      simp only [Hex.bhksCoeffBound, BHKS.hex_choose_eq,
        Nat.choose_eq_zero_of_lt (show core.degree?.getD 0 - 1 < j by omega)]
      simp
    omega

/-- Public restatement of the canonical-reduction absorption of
`centeredLiftPoly`: centring the reduction equals centring the raw polynomial. -/
theorem centeredLiftPoly_reduceModPow_absorb
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

/-- The lifted-factor product over a singleton subset is the lifted factor. -/
theorem liftedFactorProduct_singleton (d : Hex.LiftData) (i : LiftedFactorIndex d) :
    liftedFactorProduct d ({i} : LiftedFactorSubset d) = liftedFactor d i := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [toPolynomial_liftedFactorProduct, Finset.prod_singleton]

/-- Each direct Hensel factor has positive degree. -/
theorem directLiftedFactor_degree_pos
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    0 < (liftedFactor (Hex.ZPoly.directLiftData core B data) i).degree?.getD 0 := by
  have h :=
    henselLiftData_liftedFactor_natDegree_pos
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
      facts.targetMonic facts.invariant hval.prime.one_lt hprecision
      hval.monic facts.productModP hval.natDegree_pos i
  rwa [HexPolyMathlib.natDegree_toPolynomial] at h

/-- The full direct lift, scaled once by the input leading coefficient,
factors through each local factor modulo the lift modulus. -/
theorem directLiftedFactor_core_congr
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    Hex.ZPoly.congr core
      (liftedFactor (Hex.ZPoly.directLiftData core B data) i *
        Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
          (liftedFactorProduct (Hex.ZPoly.directLiftData core B data)
            ((Finset.univ : LiftedFactorSubset
              (Hex.ZPoly.directLiftData core B data)) \ {i})))
      ((Hex.ZPoly.directLiftData core B data).p ^
        (Hex.ZPoly.directLiftData core B data).k) := by
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk_eq : d.k = Hex.precisionForCoeffBound B data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hpk : 1 < d.p ^ d.k := by
    rw [hp_eq, hk_eq]
    exact Nat.one_lt_pow (by omega) hval.prime.one_lt
  have hprod :
      Hex.ZPoly.congr
        (liftedFactorProduct d Finset.univ)
        (Hex.ZPoly.monicTarget core d.p d.k)
        (d.p ^ d.k) := by
    rw [hp_eq, hk_eq]
    change Hex.ZPoly.congr
      (liftedFactorProduct
        (Hex.henselLiftData
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        Finset.univ)
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (data.p ^ Hex.precisionForCoeffBound B data.p)
    exact henselLiftData_liftedFactorProduct_univ_congr_core
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
      facts.invariant hval.prime.one_lt hprecision
  have hscaled :
      Hex.ZPoly.congr
        (scaledLiftedFactorProduct core d Finset.univ)
        core (d.p ^ d.k) :=
    scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget
      hpk (by simpa [hp_eq, hk_eq] using hgcd) hprod
  have hsplit :
      liftedFactorProduct d Finset.univ =
        liftedFactor d i *
          liftedFactorProduct d
            ((Finset.univ : LiftedFactorSubset d) \ {i}) := by
    rw [liftedFactorProduct_eq_mul_sdiff_of_subset
      (Finset.subset_univ ({i} : LiftedFactorSubset d)),
      liftedFactorProduct_singleton]
  have hscaled_eq :
      scaledLiftedFactorProduct core d Finset.univ =
        liftedFactor d i *
          Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (liftedFactorProduct d
              ((Finset.univ : LiftedFactorSubset d) \ {i})) := by
    rw [scaledLiftedFactorProduct, hsplit, Hex.DensePoly.mul_scale]
  rw [hscaled_eq] at hscaled
  simpa only [d] using Hex.ZPoly.congr_symm _ _ _ hscaled

/-- Distinct factors in the direct Hensel basis remain coprime modulo the
full lift modulus. -/
theorem directLiftedFactors_isCoprime
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (i j : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data))
    (hji : j ≠ i) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.directLiftData core B data) i)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.directLiftData core B data).p ^
              (Hex.ZPoly.directLiftData core B data).k))))
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.directLiftData core B data) j)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.directLiftData core B data).p ^
              (Hex.ZPoly.directLiftData core B data).k)))) := by
  classical
  letI := data.bounds
  let k := Hex.precisionForCoeffBound B data.p
  let target := Hex.ZPoly.monicTarget core data.p k
  let d := Hex.ZPoly.directLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq target k data
  let S : ModPFactorSubset data :=
    modPSubsetOfLiftedSubset data d hsize
      ({i} : LiftedFactorSubset d)
  have hS :
      liftedSubsetOfModPSubset data d hsize S =
        ({i} : LiftedFactorSubset d) :=
    liftedSubset_modPSubset data d hsize _
  have hcomp :=
    henselLiftData_liftedSubset_complement_isCoprime_mod_p
      target k data facts.targetMonic
      (natPrime_of_hexNatPrime hval.prime) facts.invariant
      hval.prime.one_lt hprecision hval.monic facts.productModP
      hval.irreducible hval.nodup S
  change IsCoprime
      ((HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d
          (liftedSubsetOfModPSubset data d hsize S))).map
            (Int.castRingHom (ZMod data.p)))
      ((HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d
          ((Finset.univ : LiftedFactorSubset d) \
            liftedSubsetOfModPSubset data d hsize S))).map
            (Int.castRingHom (ZMod data.p))) at hcomp
  rw [hS, liftedFactorProduct_singleton] at hcomp
  have hjmem :
      j ∈ ((Finset.univ : LiftedFactorSubset d) \ ({i} :
        LiftedFactorSubset d)) := by
    simp [hji]
  have hjdvd :
      ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
        (Int.castRingHom (ZMod data.p))) ∣
      ((HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d
          ((Finset.univ : LiftedFactorSubset d) \ ({i} :
            LiftedFactorSubset d)))).map
              (Int.castRingHom (ZMod data.p))) := by
    rw [toPolynomial_liftedFactorProduct, Polynomial.map_prod]
    exact Finset.dvd_prod_of_mem
      (fun x : LiftedFactorIndex d =>
        (HexPolyZMathlib.toPolynomial (liftedFactor d x)).map
          (Int.castRingHom (ZMod data.p))) hjmem
  have hcopp :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
          (Int.castRingHom (ZMod data.p)))
        ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
          (Int.castRingHom (ZMod data.p))) :=
    hcomp.of_isCoprime_of_dvd_right hjdvd
  haveI : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hpow := HexHenselMathlib.coprime_mod_p_lifts
    (HexPolyZMathlib.toPolynomial (liftedFactor d i))
    (HexPolyZMathlib.toPolynomial (liftedFactor d j))
    data.p d.k
    (by simp [d, Hex.ZPoly.directLiftData]; omega)
    hcopp
  change IsCoprime
    ((HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
      (Int.castRingHom (ZMod (d.p ^ d.k))))
    ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
      (Int.castRingHom (ZMod (d.p ^ d.k))))
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  rw [hp_eq]
  exact hpow

/-- A direct Hensel factor remains irreducible after reduction at its selected
prime. -/
theorem directLiftedFactor_map_irreducible
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    Irreducible
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.directLiftData core B data) i)).map
          (Int.castRingHom (ZMod data.p))) := by
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  let j := modPIndexOfLiftedIndex data d hsize i
  have hji :
      liftedIndexOfModPIndex data d hsize j = i := by
    apply Fin.ext
    rfl
  have hmod := facts.liftedModP j
  rw [hji] at hmod
  have hmap :
      (HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
          (Int.castRingHom (ZMod data.p)) =
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor data j) := by
    rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod, hmod]
  rw [hmap]
  exact hval.irreducible j

/-- A direct Hensel factor remains irreducible after reduction at the prime
stored in the canonical lift data. -/
theorem directLiftedFactor_map_irreducible_at_liftPrime
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    Irreducible
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.directLiftData core B data) i)).map
          (Int.castRingHom
            (ZMod (Hex.ZPoly.directLiftData core B data).p))) := by
  let d := Hex.ZPoly.directLiftData core B data
  change Irreducible
    ((HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
      (Int.castRingHom (ZMod d.p)))
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  rw [hp_eq]
  exact directLiftedFactor_map_irreducible core B data hval facts i

/-- Every direct Hensel factor has degree at most the input polynomial.  Reduction at
the selected prime preserves both degrees, and the direct factor congruence
makes the local factor divide the reduced square-free part. -/
theorem directLiftedFactor_natDegree_le_core
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    (HexPolyZMathlib.toPolynomial
      ((Hex.ZPoly.directLiftData core B data).liftedFactors.getD i.val 1)).natDegree ≤
        (HexPolyZMathlib.toPolynomial core).natDegree := by
  classical
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  let q := HexPolyZMathlib.toPolynomial (liftedFactor d i)
  let h := liftedFactorProduct d
    ((Finset.univ : LiftedFactorSubset d) \ {i})
  let φ := Int.castRingHom (ZMod data.p)
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk_eq : d.k = Hex.precisionForCoeffBound B data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hp_dvd : data.p ∣ d.p ^ d.k := by
    rw [hp_eq]
    exact dvd_pow_self data.p (by rw [hk_eq]; omega)
  have hfac :=
    directLiftedFactor_core_congr
      core B data hval facts hprecision hgcd i
  have hfac_p :
      Hex.ZPoly.congr core
        (liftedFactor d i *
          Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) h)
        data.p := by
    exact Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd
      (by simpa only [d, h] using hfac)
  have hmap :
      (HexPolyZMathlib.toPolynomial core).map φ =
        q.map φ *
          (HexPolyZMathlib.toPolynomial
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) h)).map φ := by
    have hm :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ data.p hfac_p
    simpa only [q, φ, HexPolyZMathlib.toPolynomial_mul,
      Polynomial.map_mul] using hm
  have hdiv :
      q.map φ ∣ (HexPolyZMathlib.toPolynomial core).map φ :=
    ⟨_, hmap⟩
  have hadm :
      Hex.leadingCoeffAdmissible core data.p :=
    Hex.isGoodPrime_leadingCoeffAdmissible core data.p hval.good
  have hcore_degree_map :
      ((HexPolyZMathlib.toPolynomial core).map φ).natDegree =
        (HexPolyZMathlib.toPolynomial core).natDegree := by
    exact
      IntReductionMod.natDegree_map_intCast_zmod_eq_of_leadingCoeffModP_ne_zero
        core hadm
  have hcore_map_ne :
      (HexPolyZMathlib.toPolynomial core).map φ ≠ 0 := by
    intro hzero
    have hdegree_pos :
        0 < (HexPolyZMathlib.toPolynomial core).natDegree := by
      rwa [HexPolyMathlib.natDegree_toPolynomial]
    rw [hzero, Polynomial.natDegree_zero] at hcore_degree_map
    omega
  haveI : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hq_monic : q.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _
      (facts.liftedMonic i)
  have hq_degree_map : (q.map φ).natDegree = q.natDegree :=
    hq_monic.natDegree_map φ
  have hgetD :
      (Hex.ZPoly.directLiftData core B data).liftedFactors.getD i.val 1 =
        liftedFactor (Hex.ZPoly.directLiftData core B data) i := by
    unfold liftedFactor
    simp [Array.getD]
  rw [hgetD]
  calc
    q.natDegree = (q.map φ).natDegree := hq_degree_map.symm
    _ ≤ ((HexPolyZMathlib.toPolynomial core).map φ).natDegree :=
      Polynomial.natDegree_le_of_dvd hdiv hcore_map_ne
    _ = (HexPolyZMathlib.toPolynomial core).natDegree := hcore_degree_map

private theorem intCast_isUnit_of_gcd_eq_one
    (a : Int) (M : Nat)
    (h : Int.gcd a (Int.ofNat M) = 1) :
    IsUnit ((a : Int) : ZMod M) := by
  have hcop : IsCoprime a (Int.ofNat M) :=
    Int.isCoprime_iff_gcd_eq_one.mpr h
  have hmap := hcop.map (Int.castRingHom (ZMod M))
  apply isCoprime_zero_right.mp
  simpa using hmap

/-- A direct Hensel factor is coprime modulo the lift modulus to its own CLD
quotient. -/
theorem directLiftedFactor_isCoprime_cldQuotient
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data)) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.directLiftData core B data) i)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.directLiftData core B data).p ^
              (Hex.ZPoly.directLiftData core B data).k))))
      ((HexPolyZMathlib.toPolynomial
        (Hex.cldQuotientMod core
          (liftedFactor (Hex.ZPoly.directLiftData core B data) i)
          (Hex.ZPoly.directLiftData core B data).p
          (Hex.ZPoly.directLiftData core B data).k)).map
            (Int.castRingHom (ZMod
              ((Hex.ZPoly.directLiftData core B data).p ^
                (Hex.ZPoly.directLiftData core B data).k)))) := by
  classical
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  let q := HexPolyZMathlib.toPolynomial (liftedFactor d i)
  let complement :=
    liftedFactorProduct d
      ((Finset.univ : LiftedFactorSubset d) \ {i})
  let φ := Int.castRingHom (ZMod (d.p ^ d.k))
  let h := (HexPolyZMathlib.toPolynomial
    (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) complement)).map φ
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk_eq : d.k = Hex.precisionForCoeffBound B data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hmodulus : 1 < d.p ^ d.k := by
    rw [hp_eq, hk_eq]
    exact Nat.one_lt_pow (by omega) hval.prime.one_lt
  have hcomp_unscaled :
      IsCoprime (q.map φ)
        ((HexPolyZMathlib.toPolynomial complement).map φ) := by
    unfold complement
    rw [toPolynomial_liftedFactorProduct, Polynomial.map_prod,
      IsCoprime.prod_right_iff]
    intro j hj
    have hji : j ≠ i := by
      simpa using (Finset.mem_sdiff.mp hj).2
    simpa only [q, φ] using
      directLiftedFactors_isCoprime core B data hval facts hprecision i j hji
  have hgcd' :
      Int.gcd (Hex.DensePoly.leadingCoeff core)
        (Int.ofNat (d.p ^ d.k)) = 1 := by
    rw [hp_eq, hk_eq]
    exact hgcd
  have hscalar :
      IsUnit (φ (Hex.DensePoly.leadingCoeff core)) :=
    intCast_isUnit_of_gcd_eq_one _ _ hgcd'
  have hCscalar :
      IsUnit (Polynomial.C (φ (Hex.DensePoly.leadingCoeff core))) :=
    Polynomial.isUnit_C.mpr hscalar
  have hscale :
      h = Polynomial.C (φ (Hex.DensePoly.leadingCoeff core)) *
        (HexPolyZMathlib.toPolynomial complement).map φ := by
    unfold h
    rw [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C, Polynomial.map_mul, Polynomial.map_C]
  have hcomp : IsCoprime (q.map φ) h := by
    rw [hscale]
    exact (isCoprime_mul_unit_left_right hCscalar _ _).mpr hcomp_unscaled
  have hp : _root_.Nat.Prime d.p := by
    rw [hp_eq]
    exact natPrime_of_hexNatPrime hval.prime
  letI : Fact (_root_.Nat.Prime d.p) := ⟨hp⟩
  have hirr :=
    directLiftedFactor_map_irreducible_at_liftPrime
      core B data hval facts i
  have hsep :
      (q.map (Int.castRingHom (ZMod d.p))).Separable :=
    PerfectField.separable_of_irreducible (by simpa only [q] using hirr)
  have hderivP :
      IsCoprime
        (q.map (Int.castRingHom (ZMod d.p)))
        ((q.derivative).map (Int.castRingHom (ZMod d.p))) := by
    simpa only [Polynomial.derivative_map] using
      (Polynomial.separable_def _).mp hsep
  have hderivPow := HexHenselMathlib.coprime_mod_p_lifts q q.derivative
    d.p d.k (by rw [hk_eq]; omega) hderivP
  have hderiv :
      IsCoprime (q.map φ) ((q.map φ).derivative) := by
    simpa only [φ, Polynomial.derivative_map] using hderivPow
  have hfac :
      Hex.ZPoly.congr core
        (liftedFactor d i *
          Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) complement)
        (d.p ^ d.k) :=
    directLiftedFactor_core_congr
      core B data hval facts hprecision hgcd i
  exact BHKS.isCoprime_cldQuotientMod
    core (liftedFactor d i)
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) complement)
      d.p d.k hmodulus (facts.liftedMonic i)
      (directLiftedFactor_degree_pos core B data hval facts hprecision i)
      hfac (by simpa only [q, h, φ] using hcomp)
      (by simpa only [q, φ] using hderiv)



/--
Production-bounded BHKS reverse containment from the algebraic lift facts.

This is the assembly point between the LLL geometry and the resultant
contradiction.  The deliberately coarse `R`, `V`, and `E` used by
`Hex.bhksBound` dominate, respectively, support-vector coordinates, retained
row coordinates, and the adjusted full vector.
-/
theorem bhksProjectedRowSpanInt_le_trueSupportSpanInt
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (trueSupports : Set (Set (Fin liftedFactors.size)))
    (hf : f ≠ 0) (hfdeg : 0 < f.degree?.getD 0)
    (hf_lc_coprime :
      IsCoprime ((p ^ a : Nat) : Int)
        (HexPolyZMathlib.toPolynomial f).leadingCoeff)
    (hp2 : 2 ≤ p) (hp500 : p ≤ 500)
    (hr : liftedFactors.size ≤ f.degree?.getD 0)
    (hk : 1 < p ^ a)
    (hprecision : 2 * Hex.bhksBound f < p ^ a)
    (hcut : ∀ j : Fin (f.degree?.getD 0),
      Hex.bhksCoeffCutThreshold p f j.val ≤ a)
    (hrows : 1 ≤ liftedFactors.size + f.degree?.getD 0)
    (hind : (Hex.bhksLatticeBasis f p a liftedFactors).basis.independent)
    (hcover : ∀ i : Fin liftedFactors.size,
      ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin liftedFactors.size, i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty)
    (data : ∀ S : trueSupports,
      BHKS.SupportShortVectorData
        (Hex.bhksLatticeBasis f p a liftedFactors) S.1)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hdeg_le : ∀ i : Fin liftedFactors.size,
      (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i.val 1)).natDegree ≤
          (HexPolyZMathlib.toPolynomial f).natDegree)
    (hcop : ∀ i j : Fin liftedFactors.size, j ≠ i →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hown : ∀ i : Fin liftedFactors.size,
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (Hex.cldQuotientMod f
            (liftedFactors.getD i.val 1) p a)).map
              (Int.castRingHom (ZMod (p ^ a)))))
    (hsupport :
      ∀ q : Polynomial ℤ,
        Irreducible q → q ∣ HexPolyZMathlib.toPolynomial f →
        ∃ S ∈ trueSupports, ∀ i ∈ S,
          (HexPolyZMathlib.toPolynomial
            (liftedFactors.getD i.val 1)).map
              (Int.castRingHom (ZMod (p ^ a))) ∣
            q.map (Int.castRingHom (ZMod (p ^ a)))) :
    BHKS.projectedRowSpanInt
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis f p a liftedFactors) hrows) ≤
      BHKS.trueSupportSpanInt trueSupports := by
  let L := Hex.bhksLatticeBasis f p a liftedFactors
  let n := f.degree?.getD 0
  let r := liftedFactors.size
  let R := 4 * n + n * n * n
  let V := (2 * n) * 2 ^ (2 * n) * R
  have hN : r + n ≤ 2 * n := by omega
  have hRadius : Hex.bhksCutRadiusSq4 L ≤ R := by
    have hsq : r * r ≤ n * n := Nat.mul_le_mul hr hr
    have hcube : n * r * r ≤ n * n * n := by
      calc
        n * r * r = n * (r * r) := by simp [Nat.mul_assoc]
        _ ≤ n * (n * n) := Nat.mul_le_mul_left n hsq
        _ = n * n * n := by simp [Nat.mul_assoc]
    change 4 * r + n * r * r ≤ R
    dsimp only [R]
    exact Nat.add_le_add (Nat.mul_le_mul_left 4 hr) hcube
  have hretained :
      ∀ j : Fin (L.factorCount + L.coeffWidth),
        j.val < Hex.bhksCutPrefixCount L
          (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix →
        ∀ x : Fin (L.factorCount + L.coeffWidth),
          (((Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.row j)[x]).natAbs ≤ V := by
    intro j hj x
    have hraw := BHKS.traceRetainedRow_coord_natAbs_le L hrows hind j hj x
    have hpow : 2 ^ (r + n) ≤ 2 ^ (2 * n) :=
      Nat.pow_le_pow_right (by omega) hN
    have hbound :
        (r + n) * 2 ^ (r + n) * Hex.bhksCutRadiusSq4 L ≤ V := by
      dsimp only [V]
      exact Nat.mul_le_mul (Nat.mul_le_mul hN hpow) hRadius
    exact hraw.trans (by
      simpa only [L, r, n, Hex.bhksLatticeBasis] using hbound)
  have hdata :
      ∀ S (x : Fin (L.factorCount + L.coeffWidth)),
        (data S).vector[x].natAbs ≤ R := by
    intro S x
    exact ((data S).coord_natAbs_le x).trans hRadius
  have hncard : trueSupports.ncard ≤ 2 ^ n := by
    calc
      trueSupports.ncard ≤ Nat.card (Set (Fin r)) :=
        Set.ncard_le_card trueSupports
      _ = 2 ^ r := by simp
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hr
  apply BHKS.projectedRowSpanInt_le_trueSupportSpanInt_of_no_bad
    L (BHKS.bhksLatticeBasis_blockForm f p a liftedFactors) hrows
    trueSupports hcover hdisjoint hne data V R hretained hdata
  intro w hwL hwzero hwnonzero hwBound
  apply BHKS.no_badVector f p a liftedFactors trueSupports
    hf hfdeg hf_lc_coprime hp2 hp500 hr hk hprecision hcut
    hfac hdeg_le hcop hown
    hsupport w hwL hwzero hwnonzero
  intro x
  have hx := hwBound x
  dsimp only [V, R] at hx ⊢
  apply hx.trans
  have hncard' :
      trueSupports.ncard ≤ 2 ^ f.degree?.getD 0 := by
    simpa only [n] using hncard
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (4 * f.degree?.getD 0 +
      f.degree?.getD 0 * f.degree?.getD 0 * f.degree?.getD 0) hncard')
    (2 * f.degree?.getD 0 * 2 ^ (2 * f.degree?.getD 0) *
      (4 * f.degree?.getD 0 +
        f.degree?.getD 0 * f.degree?.getD 0 * f.degree?.getD 0) +
      2 * f.degree?.getD 0 * 2 ^ (2 * f.degree?.getD 0) *
        (4 * f.degree?.getD 0 +
          f.degree?.getD 0 * f.degree?.getD 0 * f.degree?.getD 0) *
        (4 * f.degree?.getD 0 +
          f.degree?.getD 0 * f.degree?.getD 0 * f.degree?.getD 0))

/-- The direct lift and its genuine-support partition at an ordinary
recombination-adequate precision.  This is the shared algebraic context for
both the inexpensive forward cut theorem and the full resultant argument. -/
structure DirectAdequacy
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData) where
  /-- The Hensel precision contains at least one prime-power digit. -/
  precision : 1 ≤ Hex.precisionForCoeffBound B data.p
  /-- The input leading coefficient is invertible modulo the lift modulus. -/
  inputScale_coprime :
    Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1
  /-- The modulus is large enough for unique centred coefficient recovery. -/
  recovery :
    2 * Hex.ZPoly.defaultFactorCoeffBound core <
      data.p ^ Hex.precisionForCoeffBound B data.p
  /-- The semantic properties of the direct-coordinate Hensel lift. -/
  lift : DirectLiftFacts core B data
  /-- The genuine-factor supports partition all modular factors. -/
  partition : DirectSupportPartition core B data Finset.univ core

/-- Build the unique direct adequacy context from the semantic prime plan and
the executable recovery floor. -/
theorem directAdequacy
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (_hB_ne : B ≠ 0) :
    DirectAdequacy core B data := by
  letI := data.bounds
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_size : 0 < core.size :=
    Hex.ZPoly.size_pos_of_ne_zero core hcore_ne
  have hp2 : 2 ≤ data.p :=
    hval.prime.two_le
  have hspec :
      2 * B < data.p ^ Hex.precisionForCoeffBound B data.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hprecision :
      1 ≤ Hex.precisionForCoeffBound B data.p := by
    by_contra hnot
    have hkzero : Hex.precisionForCoeffBound B data.p = 0 := by omega
    rw [hkzero, pow_zero] at hspec
    omega
  have hadm :
      Hex.leadingCoeffAdmissible core data.p :=
    Hex.isGoodPrime_leadingCoeffAdmissible core data.p hval.good
  have hcast :
      ((Hex.DensePoly.leadingCoeff core : Int) : ZMod data.p) ≠ 0 := by
    have hpolyCast :=
      (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
        (p := data.p) (f := core)).mpr hadm
    simpa [HexPolyMathlib.leadingCoeff_toPolynomial] using hpolyCast
  have hgcd :
      Int.gcd (Hex.DensePoly.leadingCoeff core)
        (Int.ofNat
          (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1 :=
    gcd_primePow_eq_one_of_cast_ne_zero
      (Hex.DensePoly.leadingCoeff core) data.p
      (Hex.precisionForCoeffBound B data.p)
      (natPrime_of_hexNatPrime hval.prime) hcast
  have hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p := by
    have hbound :=
      Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
    omega
  have facts :
      DirectLiftFacts core B data :=
    directLiftFacts core B data hval hcore_size hprecision hgcd
  exact
    { precision := hprecision
      inputScale_coprime := hgcd
      recovery := hrecovery
      lift := facts
      partition :=
        directSupportPartition_initial core B data
          hcore_prim hcore_lc_pos hcore_pos hcore_sqfree hrecovery
          hval hprecision hgcd }

namespace DirectAdequacy

/-- Every lifted-factor index belongs to a genuine support. -/
theorem cover
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (A : DirectAdequacy core B data)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hval : ModPFactorization core data) :
    ∀ i, ∃ U ∈ directTrueSupports core B data, i ∈ U :=
  directTrueSupports.cover hcore_prim hcore_lc_pos A.recovery
    hval A.precision A.inputScale_coprime A.partition

/-- Two genuine supports sharing an index are equal. -/
theorem disjoint
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (A : DirectAdequacy core B data) :
    ∀ U ∈ directTrueSupports core B data,
      ∀ V ∈ directTrueSupports core B data,
        ∀ i, i ∈ U → i ∈ V → U = V :=
  directTrueSupports.eq_of_mem_inter A.partition

/-- The number of genuine supports equals the number of normalized irreducible factors. -/
theorem factorCount
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (A : DirectAdequacy core B data)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hval : ModPFactorization core data)
    (hcore_ne : core ≠ 0) :
    (directTrueSupports core B data).ncard =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card :=
  directTrueSupports.ncard_eq_normalizedFactors_card
    hcore_prim hcore_lc_pos A.recovery hval A.precision
    A.inputScale_coprime A.partition hcore_ne

/-- Every local factor divides the input modulo the full direct lift modulus. -/
theorem localFactor
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (A : DirectAdequacy core B data)
    (hval : ModPFactorization core data) :
    ∀ i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data),
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic
          ((Hex.ZPoly.directLiftData core B data).liftedFactors.getD i.val 1) ∧
        0 <
          ((Hex.ZPoly.directLiftData core B data).liftedFactors.getD
            i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr core
          ((Hex.ZPoly.directLiftData core B data).liftedFactors.getD i.val 1 * h)
          ((Hex.ZPoly.directLiftData core B data).p ^
            (Hex.ZPoly.directLiftData core B data).k) := by
  intro i
  let d := Hex.ZPoly.directLiftData core B data
  have hgetD :
      d.liftedFactors.getD i.val 1 = liftedFactor d i := by
    have hi : i.val < d.liftedFactors.size := by
      simpa only [d] using i.isLt
    unfold liftedFactor
    simp [Array.getD, hi]
  refine
    ⟨Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
      (liftedFactorProduct d
        ((Finset.univ : LiftedFactorSubset d) \ {i})), ?_, ?_, ?_⟩
  · rw [hgetD]
    exact A.lift.liftedMonic i
  · rw [hgetD]
    exact directLiftedFactor_degree_pos
      core B data hval A.lift A.precision i
  · rw [hgetD]
    exact directLiftedFactor_core_congr core B data hval A.lift
      A.precision A.inputScale_coprime i

/-- The CLD vector of every genuine direct support is short at the ordinary
recombination floor. -/
noncomputable def shortVector
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (A : DirectAdequacy core B data)
    (hval : ModPFactorization core data)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B) :
    ∀ U : directTrueSupports core B data,
      BHKS.SupportShortVectorData
        (Hex.bhksLatticeBasis core
          (Hex.ZPoly.directLiftData core B data).p
          (Hex.ZPoly.directLiftData core B data).k
          (Hex.ZPoly.directLiftData core B data).liftedFactors) U.1 := by
  classical
  let d := Hex.ZPoly.directLiftData core B data
  have hp2 : 2 ≤ data.p :=
    hval.prime.two_le
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk_eq : d.k = Hex.precisionForCoeffBound B data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk1 : 1 < d.p ^ d.k := by
    rw [hp_eq, hk_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt A.precision) hval.prime.one_lt
  have hsep : ∀ j,
      2 * Hex.bhksCoeffBound core j < d.p ^ d.k := by
    intro j
    have hcolumn :=
      two_mul_bhksCoeffBound_le_cldCoeffFloor core j
    have hfloor :=
      Hex.cldCoeffFloor_le_bhksRecoveryFloor core
    have hspec :=
      Hex.precisionForCoeffBound_spec hp2 B
    rw [hp_eq, hk_eq]
    omega
  have hthreshold : ∀ j,
      Hex.bhksCoeffCutThreshold d.p core j ≤ d.k := by
    intro j
    have hcolumn :=
      two_mul_bhksCoeffBound_le_cldCoeffFloor core j
    have hfloor :=
      Hex.cldCoeffFloor_le_bhksRecoveryFloor core
    rw [hp_eq, hk_eq]
    unfold Hex.bhksCoeffCutThreshold Hex.precisionForCoeffBound
    exact Hex.ceilLogP_le_of_le_pow hp2 _ _
      (Hex.le_pow_ceilLogP hp2 (2 * B + 1) |>.trans' (by omega))
  intro U
  let S : ModPFactorSubset data := Classical.choose U.2
  have hS := Classical.choose_spec U.2
  let C : DirectFactorCertificate core B data S :=
    Classical.choice hS.1
  rw [← hS.2]
  have hDp : C.recoveredLift.p = d.p := by
    rfl
  have hDa : C.recoveredLift.a = d.k := by
    rfl
  have hDf : C.recoveredLift.f = core := by
    rfl
  apply BHKS.supportShortVectorData_of_recoveredLift C.recoveredLift
  · rw [hDp, hp_eq]
    exact hp2
  · rw [hDp, hDa]
    exact hk1
  · intro j
    rw [hDf, hDp, hDa]
    exact hsep j
  · intro j
    rw [hDf, hDp, hDa]
    exact hthreshold j
  · intro i _
    rw [hDf, hDp, hDa]
    exact A.localFactor hval i

end DirectAdequacy

/-- At the ordinary recovery floor, every genuine direct support survives the
Gram--Schmidt cut.  This is the forward half `W ≤ L'`; unlike exact span it
does not require the larger resultant bound. -/
theorem directCutProjection
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth) :
    BHKS.CutProjectionHypotheses
      (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis core
          (Hex.ZPoly.directLiftData core B data).p
          (Hex.ZPoly.directLiftData core B data).k
          (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)
      (directTrueSupports core B data) := by
  classical
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  let A := directAdequacy core B data hcore_lc_pos hcore_pos
    hcore_prim hcore_sqfree hval hB_floor hB_ne
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  exact
    BHKS.cutProjectionHypotheses_of_shortVectors _ hrows
      (bhksLatticeBasis_basis_independent core d.p d.k
        (by rw [hp_eq]; exact hval.prime.pos) d.liftedFactors)
      _ (A.shortVector hval hB_floor)

/-- At the ordinary recovery floor, the executable CLD partition has at least
one class for every irreducible integer factor. -/
theorem directFactorCount_le_classCount
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth) :
    (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card ≤
      (Hex.bhksEquivalenceClassIndicators
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.directLiftData core B data).p
            (Hex.ZPoly.directLiftData core B data).k
            (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)).size := by
  let A := directAdequacy core B data hcore_lc_pos hcore_pos
    hcore_prim hcore_sqfree hval hB_floor hB_ne
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcover := A.cover hcore_prim hcore_lc_pos hval
  have hdisjoint := A.disjoint
  calc
    (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card =
        (directTrueSupports core B data).ncard :=
      (A.factorCount hcore_prim hcore_lc_pos hval hcore_ne).symm
    _ =
        (BHKS.supportPartitionByMinColumn
          (directTrueSupports core B data)).length :=
      (BHKS.supportPartitionByMinColumn_length_eq_ncard_of_partition
        (directTrueSupports core B data) hcover hdisjoint
        directTrueSupports.nonempty).symm
    _ ≤
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis core
              (Hex.ZPoly.directLiftData core B data).p
              (Hex.ZPoly.directLiftData core B data).k
              (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows)).size :=
      BHKS.supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size
        _ _ (directCutProjection core B data hcore_lc_pos hcore_pos
          hcore_prim hcore_sqfree hval hB_floor hB_ne hrows)

/--
At an adequate precision, the projected CLD lattice is exactly the span of
the direct modular supports of the normalized irreducible integer factors.
All algebraic inputs use `directLiftData`; no dilation-coordinate lift appears
in the statement or proof.
-/
theorem directProjectedSpan_eq
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hval : ModPFactorization core data)
    (hp500 : data.p ≤ 500)
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hadequate :
      2 * Hex.bhksBound core <
        (Hex.ZPoly.directLiftData core B data).p ^
          (Hex.ZPoly.directLiftData core B data).k)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis core
        (Hex.ZPoly.directLiftData core B data).p
        (Hex.ZPoly.directLiftData core B data).k
        (Hex.ZPoly.directLiftData core B data).liftedFactors).coeffWidth) :
    BHKS.projectedRowSpanInt
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core
            (Hex.ZPoly.directLiftData core B data).p
            (Hex.ZPoly.directLiftData core B data).k
            (Hex.ZPoly.directLiftData core B data).liftedFactors) hrows) =
      BHKS.trueSupportSpanInt (directTrueSupports core B data) := by
  classical
  letI := data.bounds
  let d := Hex.ZPoly.directLiftData core B data
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_size : 0 < core.size :=
    Hex.ZPoly.size_pos_of_ne_zero core hcore_ne
  let A := directAdequacy core B data hcore_lc_pos hcore_pos
    hcore_prim hcore_sqfree hval hB_floor hB_ne
  have hp2 : 2 ≤ data.p :=
    hval.prime.two_le
  have hp_eq : d.p = data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk_eq : d.k = Hex.precisionForCoeffBound B data.p := by
    simp [d, Hex.ZPoly.directLiftData]
  have hk1 : 1 < d.p ^ d.k := by
    rw [hp_eq, hk_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt A.precision) hval.prime.one_lt
  have hthreshold : ∀ j,
      Hex.bhksCoeffCutThreshold d.p core j ≤ d.k := by
    intro j
    have hcolumn :=
      two_mul_bhksCoeffBound_le_cldCoeffFloor core j
    have hfloor :=
      Hex.cldCoeffFloor_le_bhksRecoveryFloor core
    rw [hp_eq, hk_eq]
    unfold Hex.bhksCoeffCutThreshold Hex.precisionForCoeffBound
    exact Hex.ceilLogP_le_of_le_pow hp2 _ _
      (Hex.le_pow_ceilLogP hp2 (2 * B + 1) |>.trans' (by omega))
  have facts :
      DirectLiftFacts core B data :=
    A.lift
  have hpartition :
      DirectSupportPartition core B data Finset.univ core :=
    A.partition
  have hfac :
      ∀ i : LiftedFactorIndex d,
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic (d.liftedFactors.getD i.val 1) ∧
          0 < (d.liftedFactors.getD i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr core
            (d.liftedFactors.getD i.val 1 * h) (d.p ^ d.k) := by
    intro i
    have hgetD :
        d.liftedFactors.getD i.val 1 = liftedFactor d i := by
      unfold liftedFactor
      simp [Array.getD]
    refine
      ⟨Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
        (liftedFactorProduct d
          ((Finset.univ : LiftedFactorSubset d) \ {i})), ?_, ?_, ?_⟩
    · rw [hgetD]
      exact facts.liftedMonic i
    · rw [hgetD]
      exact directLiftedFactor_degree_pos
        core B data hval facts A.precision i
    · rw [hgetD]
      exact directLiftedFactor_core_congr
        core B data hval facts A.precision A.inputScale_coprime i
  have hcut :
      BHKS.CutProjectionHypotheses
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors) hrows)
        (directTrueSupports core B data) :=
    directCutProjection core B data hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hval hB_floor hB_ne hrows
  apply le_antisymm
  · have hsize :
        d.liftedFactors.size = data.factorsModP.size :=
      henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data
    have htargetSize :
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p)).size = core.size :=
      Hex.ZPoly.monicTarget_size_eq core data.p
        (Hex.precisionForCoeffBound B data.p)
        (by simpa [d, hp_eq, hk_eq] using hk1)
        A.inputScale_coprime hcore_size
    have htargetDegree :
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p)).degree?.getD 0 =
            core.degree?.getD 0 := by
      rw [Hex.DensePoly.degree?_eq_some_of_pos_size _ (by
        rw [htargetSize]
        exact hcore_size)]
      rw [Hex.DensePoly.degree?_eq_some_of_pos_size core hcore_size]
      simp only [Option.getD_some, htargetSize]
    have hr : d.liftedFactors.size ≤ core.degree?.getD 0 := by
      rw [hsize, ← htargetDegree]
      exact hval.factorCount_le_degree_of_product
        facts.targetMonic facts.productModP
    have hlcCoprime :
        IsCoprime ((d.p ^ d.k : Nat) : Int)
          (HexPolyZMathlib.toPolynomial core).leadingCoeff := by
      rw [HexPolyMathlib.leadingCoeff_toPolynomial]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr
        (by simpa [d, Hex.ZPoly.directLiftData] using
          A.inputScale_coprime)).symm
    have hdeg :
        ∀ i : LiftedFactorIndex d,
          (HexPolyZMathlib.toPolynomial
            (d.liftedFactors.getD i.val 1)).natDegree ≤
              (HexPolyZMathlib.toPolynomial core).natDegree := by
      intro i
      exact directLiftedFactor_natDegree_le_core
        core B data hcore_pos hval facts A.precision
          A.inputScale_coprime i
    have hcop :
        ∀ i j : LiftedFactorIndex d, j ≠ i →
          IsCoprime
            ((HexPolyZMathlib.toPolynomial
              (d.liftedFactors.getD i.val 1)).map
                (Int.castRingHom (ZMod (d.p ^ d.k))))
            ((HexPolyZMathlib.toPolynomial
              (d.liftedFactors.getD j.val 1)).map
                (Int.castRingHom (ZMod (d.p ^ d.k)))) := by
      intro i j hji
      simpa [liftedFactor, Array.getD] using
        directLiftedFactors_isCoprime
          core B data hval facts A.precision i j hji
    have hown :
        ∀ i : LiftedFactorIndex d,
          IsCoprime
            ((HexPolyZMathlib.toPolynomial
              (d.liftedFactors.getD i.val 1)).map
                (Int.castRingHom (ZMod (d.p ^ d.k))))
            ((HexPolyZMathlib.toPolynomial
              (Hex.cldQuotientMod core
                (d.liftedFactors.getD i.val 1) d.p d.k)).map
                  (Int.castRingHom (ZMod (d.p ^ d.k)))) := by
      intro i
      simpa [liftedFactor, Array.getD] using
        directLiftedFactor_isCoprime_cldQuotient
          core B data hval facts A.precision A.inputScale_coprime i
    have hsupport :
        ∀ q : Polynomial ℤ,
          Irreducible q → q ∣ HexPolyZMathlib.toPolynomial core →
          ∃ U ∈ directTrueSupports core B data, ∀ i ∈ U,
            (HexPolyZMathlib.toPolynomial
              (d.liftedFactors.getD i.val 1)).map
                (Int.castRingHom (ZMod (d.p ^ d.k))) ∣
              q.map (Int.castRingHom (ZMod (d.p ^ d.k))) := by
      intro q hq_irr hq_dvd
      let raw := HexPolyZMathlib.ofPolynomial q
      let factor := Hex.normalizeFactorSign raw
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor) q := by
        simpa [factor, raw] using normalizeFactorSign_associated raw
      have hfactor_irr :
          Irreducible (HexPolyZMathlib.toPolynomial factor) :=
        hassoc.symm.irreducible hq_irr
      have hfactor_dvd : factor ∣ core :=
        HexPolyMathlib.toPolynomial_dvd_iff.mp
          (hassoc.dvd.trans hq_dvd)
      have hfactor_norm :
          Hex.normalizeFactorSign factor = factor := by
        simpa [factor] using Hex.normalizeFactorSign_idem raw
      obtain ⟨S, _, hrep⟩ :=
        hpartition.existsSupport hfactor_irr hfactor_dvd
      let C : DirectFactorCertificate core B data S :=
        directFactorCertificate hcore_prim hcore_lc_pos A.recovery
          hval A.precision A.inputScale_coprime hfactor_irr hfactor_dvd
          hfactor_norm hrep
      refine
        ⟨(↑(directLiftedSupport core B data S) :
            Set (LiftedFactorIndex d)),
          ⟨S, ⟨C⟩, rfl⟩, ?_⟩
      intro i hi
      have hiDvd :=
        C.liftedFactor_map_dvd hcore_lc_pos i (by simpa [d] using hi)
      have hCfactor : C.factor = factor := by
        rfl
      rw [hCfactor] at hiDvd
      have hfactorMapDvd :
          (HexPolyZMathlib.toPolynomial factor).map
              (Int.castRingHom (ZMod (d.p ^ d.k))) ∣
            q.map (Int.castRingHom (ZMod (d.p ^ d.k))) :=
        Polynomial.map_dvd _ hassoc.dvd
      have hgetD' :
          (Hex.ZPoly.directLiftData core B data).liftedFactors.getD i.val 1 =
            liftedFactor (Hex.ZPoly.directLiftData core B data) i := by
        unfold liftedFactor
        simp [Array.getD]
      have hgetD :
          d.liftedFactors.getD i.val 1 = liftedFactor d i := by
        simpa only [d] using hgetD'
      rw [hgetD]
      simpa only [d] using hiDvd.trans hfactorMapDvd
    exact bhksProjectedRowSpanInt_le_trueSupportSpanInt
      core d.p d.k d.liftedFactors (directTrueSupports core B data)
      hcore_ne hcore_pos hlcCoprime
      (by rw [hp_eq]; exact hp2) (by rw [hp_eq]; exact hp500)
      hr hk1 hadequate (fun j => hthreshold j.val) hrows
      (bhksLatticeBasis_basis_independent core d.p d.k
        (by rw [hp_eq]; omega) d.liftedFactors)
      (A.cover hcore_prim hcore_lc_pos hval)
      A.disjoint directTrueSupports.nonempty
      (A.shortVector hval hB_floor) (A.localFactor hval)
      hdeg hcop hown hsupport
  · exact BHKS.trueSupportSpanInt_le_projectedRowSpanInt _ _ hcut

end

end HexBerlekampZassenhausMathlib
