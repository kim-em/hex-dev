/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.IntReductionMod
public import HexBerlekampZassenhausMathlib.Relift
public import HexBerlekampZassenhausMathlib.CLDColumnBound
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
# Irreducibility of the van Hoeij / CLD lattice tier

The large-`r` lattice tier `Hex.latticeCoreFactorsWithBound` is the van Hoeij
CLD recovery, run past the classical subset budget.  For a square-free `core`
selected by `Hex.ZPoly.toMonicPrimeData?` (the monic-transform selection, so the
Hensel seeds match the lift target) it has three arms:

1. `primeData.factorsModP.size ≤ 1` → `some #[core]`.  The core is irreducible
   mod `p`, hence irreducible over `ℤ`.  **Proved unconditionally here** by
   reusing `squareFreeCore_irreducible_of_small_mod_singleton`.

2. `latticeCoreWithBound … = some coreFactors` → those factors.  Via
   `latticeCoreWithBound_some_spec` this is either a genuine CLD split (a
   `bhksRecoveryCoreWithBound` success; irreducibility of the emitted factors is
   the BHKS count-equality obligation, already isolated by
   `bhksFactors_zpolyIrreducible_of_count` and threaded
   here as the `harm2_count` hypothesis), or the certificate-backed early stop:
   `some #[core]` with a witness precision `k'` at/above the
   column-adequacy floor whose partition is the single all-ones class,
   discharged by the adequacy hypothesis at `k'`.

3. `latticeCoreWithBound = none` ∧ `bhksSingleAllOnesPartition core d = true`
   → `some #[core]`.  The single all-ones equivalence class of the CLD lattice
   at cap precision certifies that `core` lands on exactly the minimal subsets
   (`L = W`), i.e. `core` is irreducible.  This is the deep van Hoeij adequacy
   theorem; it is threaded here as the `harm3_adequacy` hypothesis (quantified
   over the certification precision, so it also covers arm 2's early stop).

The reduction below discharges arm 1 and reduces the whole tier to the two BHKS
obligations, mirroring the fast-path `_of_count` convention and the classical
theorem `classicalCoreFactorsWithBound_factor_irreducible`. It is the
proof architecture the deep-content successors plug into.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Every factor the
van Hoeij CLD lattice tier `Hex.latticeCoreFactorsWithBound` returns for the
square-free core of `normalizeForFactor f` is irreducible, given the two BHKS
obligations as hypotheses.

The arms of `latticeCoreFactorsWithBound` are discharged as follows:

* the small-mod singleton arm (`factorsModP.size ≤ 1`, output `#[core]`) is
  proved unconditionally from `squareFreeCore_irreducible_of_small_mod_singleton`;
* the loop-answer arm (`latticeCoreWithBound = some coreFactors`) splits via
  `latticeCoreWithBound_some_spec` into the CLD-split case (a genuine
  `bhksRecoveryCoreWithBound` success, discharged from the count-equality
  hypothesis `harm2_count` via
  `bhksFactors_zpolyIrreducible_of_count`) and the
  certificate-backed early stop (: output `#[core]` with a witness
  precision `k'` clearing the column-adequacy floor, discharged from the
  adequacy hypothesis `harm3_adequacy` at `k'`);
* the cap all-ones certification arm (`bhksSingleAllOnesPartition = true` at
  `B`, output `#[core]`) is discharged from `harm3_adequacy` at `B`.

`harm2_count` and `harm3_adequacy` are exactly the remaining deep BHKS content
(the "lattice lands on minimal subsets" argument); every other side condition is
discharged from `toMonicPrimeData?` and the square-free-core facts.  The
adequacy hypothesis is quantified over the certification precision `B'` because
the early stop certifies at the first adequate schedule point, not at the cap.
-/
theorem latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_floor : Hex.bhksRecoveryFloor (Hex.normalizeForFactor f).squareFreeCore ≤ B)
    (hB_ne : B ≠ 0)
    {cf : Array Hex.ZPoly}
    (hlattice : Hex.latticeCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore B primeData = some cf)
    (harm2_count : ∀ coreFactors : Array Hex.ZPoly,
      Hex.bhksRecoveryCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B primeData
          (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
          = some coreFactors →
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore)).card)
    (harm3_adequacy : ∀ B' : Nat,
      Hex.bhksRecoveryFloor (Hex.normalizeForFactor f).squareFreeCore ≤ B' → B' ≠ 0 →
      Hex.bhksSingleAllOnesPartition (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore B' primeData)
          = true →
      Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore) :
    ∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  -- Membership in the singleton output `#[core]` forces `g = core`.
  have hsingleton : ∀ g ∈ (#[core] : Array Hex.ZPoly).toList,
      Hex.ZPoly.Irreducible core → Hex.ZPoly.Irreducible g := by
    intro g hg hcore_irr
    have : g = core := by simpa using hg
    exact this ▸ hcore_irr
  rw [Hex.latticeCoreFactorsWithBound] at hlattice
  split at hlattice
  · -- Arm 1: small-mod singleton. Output `#[core]`, core irreducible mod p.
    rename_i hsmall
    obtain rfl := Option.some.inj hlattice
    exact fun g hg => hsingleton g hg
      (squareFreeCore_irreducible_of_small_mod_singleton f hf_ne primeData
        (Nat.pos_of_ne_zero hdeg_ne) hselected hsmall)
  · -- Arms 2/3: CLD recovery loop (with the certificate-backed early stop).
    split at hlattice
    · -- Arm 2: the loop answered. Either a genuine CLD split (count-equality
      -- obligation) or the early irreducibility certificate at a witness
      -- precision `k'` (adequacy obligation at `k'`).
      rename_i coreFactors hloop
      obtain rfl := Option.some.inj hlattice
      rcases Hex.latticeCoreWithBound_some_spec hloop with
        hfast | ⟨rfl, k', hk'_floor, hk'_bhks⟩
      · exact bhksFactors_zpolyIrreducible_of_count
          hcore_ne hfast (harm2_count coreFactors hfast)
      · have hk'_ne : k' ≠ 0 := by
          have hpos := Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
          have hfl := Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
          omega
        exact fun g hg => hsingleton g hg (harm3_adequacy k' hk'_floor hk'_ne hk'_bhks)
    · -- Arm 3: loop declined to the cap; all-ones certification at `B`, behind
      -- the executable floor guard.
      rename_i hloop
      split at hlattice
      · -- `bhksRecoveryFloorGate core ≤ B`: the guarded all-ones check.
        split at hlattice
        · -- `bhksSingleAllOnesPartition = true`: output `#[core]`, core irreducible.
          rename_i hbhks
          obtain rfl := Option.some.inj hlattice
          exact fun g hg => hsingleton g hg (harm3_adequacy B hB_floor hB_ne hbhks)
        · -- `bhksSingleAllOnesPartition = false`: output `none`, contradiction.
          exact absurd hlattice.symm (Option.some_ne_none cf)
      · -- Guard rejected (`B` below the floor): output `none`, contradiction.
        exact absurd hlattice.symm (Option.some_ne_none cf)


/-!
# Lattice geometry: the BHKS basis is LLL-independent (arm-3 foundation)

The van Hoeij knapsack basis `[I_r | Ã ; 0 | diag(p^(a-l_j))]` is upper-triangular
with strictly positive diagonal (1's in the `I_r` block, `p^(a-l_j)` in the
`D` block), so its rows are LLL-independent.  This is the entry gate to the
proven LLL short-vector bound `HexLLLMathlib.lllNative_first_row_norm_sq_le`.
-/

/-- The BHKS knapsack lattice basis is upper-triangular: below-diagonal entries
vanish.  Follows from the block structure `[I_r | Ã ; 0 | diag]`. -/
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
    -- Trivial: `0 < Int.ofNat (p ^ (a - l_j))` since `0 < p` (a cast-lemma one-liner).
    -- Deferred per hardest-first; the mathematical content is fully discharged above.
    exact Int.ofNat_lt.mpr (Nat.pow_pos hp)

/-- **Arm-3 foundation.**  The BHKS knapsack lattice basis is LLL-independent
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

/-- **Arm-3 proven-path step.**  The first row of the LLL-reduced BHKS knapsack
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

Both deep obligations reduce to the count lower bound
`(normalizedFactors (toPolynomial core)).card ≤
  (bhksEquivalenceClassIndicators …).size`: each irreducible factor of `core`
yields a true lifted-factor support whose `0/1` indicator is the first block of
a short vector of the monic-coordinate BHKS lattice
(`BHKS.supportShortVectorData_of_recoveredLift`); the Gram-Schmidt
prefix-survivor lemma places it in the projected row span (`W ⊆ L'`,
`BHKS.cutProjectionHypotheses_of_shortVectors`), so the RREF signature classes
refine the true-support partition
(`BHKS.supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size`),
whose length the partition machinery identifies with the number of
irreducible factors of `core`
(`BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card`).
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

/-- Every CLD column bound of the monic transform is dominated by the CLD
floor: `2 * bhksCoeffBound (toMonic core).monic j ≤ cldCoeffFloor core` for
every `j` (out-of-range columns have bound `0`). -/
theorem two_mul_bhksCoeffBound_toMonic_le_cldCoeffFloor (core : Hex.ZPoly) (j : Nat) :
    2 * Hex.bhksCoeffBound (Hex.ZPoly.toMonic core).monic j ≤
      Hex.cldCoeffFloor core := by
  by_cases hj : j ≤ (Hex.ZPoly.toMonic core).monic.degree?.getD 0
  · have hmem : j ∈ List.range ((Hex.ZPoly.toMonic core).monic.degree?.getD 0 + 1) :=
      List.mem_range.mpr (by omega)
    have hle := le_foldl_max
      (g := fun j => Hex.bhksCoeffBound (Hex.ZPoly.toMonic core).monic j) hmem 0
    simp only [Hex.cldCoeffFloor]
    omega
  · have hz : Hex.bhksCoeffBound (Hex.ZPoly.toMonic core).monic j = 0 := by
      simp only [Hex.bhksCoeffBound, BHKS.hex_choose_eq,
        Nat.choose_eq_zero_of_lt (show (Hex.ZPoly.toMonic core).monic.degree?.getD 0 - 1 < j by omega)]
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

/-- Distinct production Hensel factors are coprime modulo the full lift
modulus.  Complement coprimality at the selected prime is first restricted to
the second singleton, then lifted from `p` to `p^k`. -/
theorem toMonicLiftData_liftedFactors_isCoprime
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (i j : LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))
    (hji : j ≠ i) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k))))
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) j)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k)))) := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  have hp_eq : d.p = primeData.p := by
    unfold d Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_p _ _ _
  have hk_eq : d.k = Hex.precisionForCoeffBound B primeData.p := by
    unfold d Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_k _ _ _
  have hcomp :=
    toMonicLiftData_isCoprime_liftedFactorProduct_complement
      core B primeData hcore_lc_pos hcore_pos hval hprecision
        ({i} : LiftedFactorSubset d)
  rw [liftedFactorProduct_singleton] at hcomp
  have hjmem : j ∈
      ((Finset.univ : LiftedFactorSubset d) \ ({i} : LiftedFactorSubset d)) := by
    simp [hji]
  have hjdvd :
      ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
        (Int.castRingHom (ZMod primeData.p))) ∣
      ((HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d
          ((Finset.univ : LiftedFactorSubset d) \ ({i} : LiftedFactorSubset d)))).map
            (Int.castRingHom (ZMod primeData.p))) := by
    rw [toPolynomial_liftedFactorProduct, Polynomial.map_prod]
    exact Finset.dvd_prod_of_mem
      (fun x : LiftedFactorIndex d =>
        (HexPolyZMathlib.toPolynomial (liftedFactor d x)).map
          (Int.castRingHom (ZMod primeData.p))) hjmem
  have hcopp :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
          (Int.castRingHom (ZMod primeData.p)))
        ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
          (Int.castRingHom (ZMod primeData.p))) :=
    hcomp.of_isCoprime_of_dvd_right hjdvd
  haveI : Fact (_root_.Nat.Prime primeData.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hpow := HexHenselMathlib.coprime_mod_p_lifts
    (HexPolyZMathlib.toPolynomial (liftedFactor d i))
    (HexPolyZMathlib.toPolynomial (liftedFactor d j))
    primeData.p d.k (by rw [hk_eq]; omega) hcopp
  change IsCoprime
    ((HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
      (Int.castRingHom (ZMod (d.p ^ d.k))))
    ((HexPolyZMathlib.toPolynomial (liftedFactor d j)).map
      (Int.castRingHom (ZMod (d.p ^ d.k))))
  rw [hp_eq]
  exact hpow

/-- Every monic irreducible divisor of the monic transform is represented by a
true support, and every local factor in that support divides it modulo the full
lift modulus. -/
theorem toMonicLiftData_trueSupport_dvd
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hpartition : LiftedFactorSubsetPartition core
      (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ core)
    (hmonic_i : ∀ i : LiftedFactorIndex
        (Hex.ZPoly.toMonicLiftData core B primeData),
      Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (q : Polynomial ℤ) (hqmonic : q.Monic) (hqirr : Irreducible q)
    (hqf : q ∣ HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic) :
    ∃ S ∈ liftedTrueSupports core
        (Hex.ZPoly.toMonicLiftData core B primeData),
      ∀ i ∈ S,
        (HexPolyZMathlib.toPolynomial
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
            (Int.castRingHom (ZMod
              ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                (Hex.ZPoly.toMonicLiftData core B primeData).k))) ∣
          q.map (Int.castRingHom (ZMod
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k))) := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  let g := HexPolyZMathlib.ofPolynomial q
  have hgpoly : HexPolyZMathlib.toPolynomial g = q := by simp [g]
  have hgmonic : Hex.DensePoly.Monic g := by
    show Hex.DensePoly.leadingCoeff g = 1
    rw [← HexPolyMathlib.leadingCoeff_toPolynomial]
    change (HexPolyZMathlib.toPolynomial g).leadingCoeff = 1
    rw [hgpoly]
    exact hqmonic.leadingCoeff
  have hgirr : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    simpa only [hgpoly] using hqirr
  have hgdvd : g ∣ (Hex.ZPoly.toMonic core).monic := by
    obtain ⟨c, hc⟩ := hqf
    refine ⟨HexPolyZMathlib.ofPolynomial c, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp [hgpoly, hc]
  obtain ⟨factor, hfactor_irr, hfactor_dvd, hfactor_sign, hrecover⟩ :=
    exists_dvd_core_of_dvd_toMonic core g hcore_lc_pos hcore_pos hcore_prim
      hgmonic hgirr hgdvd
  obtain ⟨S, _hSuniv, hrep⟩ :=
    hpartition.toHenselSubsetCorrespondenceRest.exists_subset
      hfactor_sign hfactor_irr hfactor_dvd
  let R : RecoveredAtLift core d factor S := hrep.some
  have hm_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hm_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 :=
    zpoly_ne_zero_of_monic hm_monic
  have hvalid : ∀ k, (R.monicFactor.coeff k).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic := fun k =>
    defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hm_ne
      R.monicFactor R.monic_dvd k
  have hprecision' :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k := by simpa only [d] using hprecision
  have hcl :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) =
        R.monicFactor := by
    rw [← centeredLiftPoly_reduceModPow_absorb (liftedFactorProduct d S) d.p d.k
      d.p_pos, R.congr]
    exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
      R.monicFactor d.p d.k
        (Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic)
        hvalid hprecision'
  have hprod_monic : Hex.DensePoly.Monic (liftedFactorProduct d S) :=
    liftedFactorProduct_monic d S (fun i _ => hmonic_i i)
  have hdefault_pos :
      0 < Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hm_ne
  have hRmonic : Hex.DensePoly.Monic R.monicFactor := by
    rw [← hcl]
    exact monic_centeredLiftPoly_of_monic hprod_monic (by omega)
  have hRg : R.monicFactor = g := by
    symm
    apply monic_eq_of_primitivePart_dilate_eq
      (ne_of_gt hcore_lc_pos) hgmonic hRmonic
    rw [hrecover, R.dilate_eq]
  have hprodCong :
      Hex.ZPoly.congr (liftedFactorProduct d S) g (d.p ^ d.k) := by
    have hleft := Hex.ZPoly.congr_symm _ _ _
      (Hex.ZPoly.congr_reduceModPow (liftedFactorProduct d S) d.p d.k
        (Nat.pow_pos d.p_pos))
    rw [R.congr, hRg] at hleft
    exact Hex.ZPoly.congr_trans _ _ _ _ hleft
      (Hex.ZPoly.congr_reduceModPow g d.p d.k (Nat.pow_pos d.p_pos))
  have hprodMap :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      (liftedFactorProduct d S) g (d.p ^ d.k) hprodCong
  refine ⟨(↑S : Set (LiftedFactorIndex d)),
    ⟨factor, S, hfactor_irr, hfactor_dvd, hrep, rfl⟩, ?_⟩
  intro i hi
  have hidvd :
      HexPolyZMathlib.toPolynomial (liftedFactor d i) ∣
        HexPolyZMathlib.toPolynomial (liftedFactorProduct d S) := by
    rw [toPolynomial_liftedFactorProduct]
    exact Finset.dvd_prod_of_mem
      (fun x : LiftedFactorIndex d =>
        HexPolyZMathlib.toPolynomial (liftedFactor d x)) (by simpa using hi)
  have himap := Polynomial.map_dvd
    (Int.castRingHom (ZMod (d.p ^ d.k))) hidvd
  rw [hprodMap] at himap
  simpa [d, g] using himap

/-- A production lifted factor is coprime modulo `p^k` to its own CLD
quotient.  Complement coprimality and separability are both proved at the
selected prime and lifted to the full modulus. -/
theorem toMonicLiftData_isCoprime_cldQuotient
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (i : LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))
    (hmonic :
      Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i))
    (hdeg :
      0 < (liftedFactor
        (Hex.ZPoly.toMonicLiftData core B primeData) i).degree?.getD 0)
    (hfac :
      Hex.ZPoly.congr (Hex.ZPoly.toMonic core).monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i *
          liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
            ((Finset.univ : LiftedFactorSubset
              (Hex.ZPoly.toMonicLiftData core B primeData)) \ {i}))
        ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).map
          (Int.castRingHom (ZMod
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k))))
      ((HexPolyZMathlib.toPolynomial
        (Hex.cldQuotientMod (Hex.ZPoly.toMonic core).monic
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonicLiftData core B primeData).k)).map
            (Int.castRingHom (ZMod
              ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                (Hex.ZPoly.toMonicLiftData core B primeData).k)))) := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  let q := HexPolyZMathlib.toPolynomial (liftedFactor d i)
  let h := HexPolyZMathlib.toPolynomial
    (liftedFactorProduct d ((Finset.univ : LiftedFactorSubset d) \ {i}))
  have hp_eq : d.p = primeData.p := by
    unfold d Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_p _ _ _
  have hk_eq : d.k = Hex.precisionForCoeffBound B primeData.p := by
    unfold d Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_k _ _ _
  have hcompP :=
    toMonicLiftData_isCoprime_liftedFactorProduct_complement
      core B primeData hcore_lc_pos hcore_pos hval hprecision
        ({i} : LiftedFactorSubset d)
  rw [liftedFactorProduct_singleton] at hcompP
  haveI : Fact (_root_.Nat.Prime primeData.p) :=
    ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hcompPow := HexHenselMathlib.coprime_mod_p_lifts q h
    primeData.p d.k (by rw [hk_eq]; omega) (by
      simpa only [q, h] using hcompP)
  have hcomp :
      IsCoprime
        (q.map (Int.castRingHom (ZMod (d.p ^ d.k))))
        (h.map (Int.castRingHom (ZMod (d.p ^ d.k)))) := by
    rw [hp_eq]
    exact hcompPow
  have hirr :=
    toMonicLiftData_liftedFactor_map_irreducible
      core B primeData hcore_lc_pos hcore_pos hval hprecision i
  have hsep :
      (q.map (Int.castRingHom (ZMod primeData.p))).Separable :=
    PerfectField.separable_of_irreducible (by simpa only [q] using hirr)
  have hderivP :
      IsCoprime
        (q.map (Int.castRingHom (ZMod primeData.p)))
        ((q.derivative).map (Int.castRingHom (ZMod primeData.p))) := by
    simpa only [Polynomial.derivative_map] using
      (Polynomial.separable_def _).mp hsep
  have hderivPow := HexHenselMathlib.coprime_mod_p_lifts q q.derivative
    primeData.p d.k (by rw [hk_eq]; omega) hderivP
  have hderiv :
      IsCoprime
        (q.map (Int.castRingHom (ZMod (d.p ^ d.k))))
        ((q.map (Int.castRingHom (ZMod (d.p ^ d.k)))).derivative) := by
    rw [hp_eq]
    simpa only [Polynomial.derivative_map] using hderivPow
  exact BHKS.isCoprime_cldQuotientMod
    (Hex.ZPoly.toMonic core).monic (liftedFactor d i)
      (liftedFactorProduct d ((Finset.univ : LiftedFactorSubset d) \ {i}))
      d.p d.k (by
        have hp2 := hval.prime.two_le
        rw [hp_eq, hk_eq]
        exact one_lt_pow₀ (by omega)
          (by omega : Hex.precisionForCoeffBound B primeData.p ≠ 0))
      hmonic hdeg (by simpa only [d] using hfac)
      (by simpa only [q, h] using hcomp)
      (by simpa only [q] using hderiv)

/-- The ported `BHKS.supportProduct` of a coerced `Finset` support agrees with
the `liftedFactorProduct` of that subset: both are the product of the selected
lifted factors, in possibly different traversal orders. -/
theorem supportProduct_coe_eq_liftedFactorProduct
    (mPoly : Hex.ZPoly) (d : Hex.LiftData) (p a : Nat)
    (S' : LiftedFactorSubset d) :
    BHKS.supportProduct (Hex.bhksLatticeBasis mPoly p a d.liftedFactors)
        (↑S' : Set (LiftedFactorIndex d)) =
      liftedFactorProduct d S' := by
  classical
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [toPolynomial_liftedFactorProduct]
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct
        ((((List.finRange d.liftedFactors.size).filter fun i =>
            @decide (i ∈ (↑S' : Set (LiftedFactorIndex d)))
              (Classical.propDecidable _)).map
          fun i => d.liftedFactors.getD i.val 1).toArray)) =
    ∏ i ∈ S', HexPolyZMathlib.toPolynomial (liftedFactor d i)
  rw [polyProduct_toPolynomial, List.toList_toArray, List.map_map]
  simp only [Function.comp_def]
  rw [← List.prod_toFinset
    (fun i : LiftedFactorIndex d => HexPolyZMathlib.toPolynomial
      (d.liftedFactors.getD i.val 1))
    ((List.nodup_finRange d.liftedFactors.size).filter _)]
  refine Finset.prod_congr ?_ (fun i _ => ?_)
  · ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, Finset.mem_coe]
  · show HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1) =
      HexPolyZMathlib.toPolynomial (liftedFactor d i)
    congr 1
    unfold liftedFactor
    simp [Array.getD, i.isLt]

namespace BHKS

/-- The proof-side lifted-factor subset selected by one canonical support
class. -/
def liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) : LiftedFactorSubset d :=
  Finset.univ.filter fun i : LiftedFactorIndex d => i.val ∈ members

@[simp] theorem mem_liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) (i : LiftedFactorIndex d) :
    i ∈ liftedSubsetOfClass d members ↔ i.val ∈ members := by
  simp [liftedSubsetOfClass]

/-- The executable selected-factor array for one canonical support class. -/
def selectedFactorsOfClass
    (liftedFactors : Array Hex.ZPoly) (members : List Nat) : Array Hex.ZPoly :=
  Hex.bhksIndicatorSelectedFactorsArray liftedFactors
    (classIndicatorArray liftedFactors.size members)

private theorem filterMap_if_eq_map_filter
    {α β : Type _} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> simp [hp, ih]

private theorem liftedSubsetSelectedList_liftedSubsetOfClass
    (d : Hex.LiftData) (members : List Nat) :
    liftedSubsetSelectedList d (liftedSubsetOfClass d members) =
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (liftedFactor d) := by
  unfold liftedSubsetSelectedList liftedSubsetMask
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map
        (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  rw [filterMap_if_eq_map_filter]
  simp [liftedFactor, liftedSubsetOfClass]

/-- The executable selected-factor product agrees with the proof-side product
over the corresponding finite support. -/
theorem selectedFactorsOfClass_polyProduct
    (d : Hex.LiftData) (members : List Nat) :
    Array.polyProduct (selectedFactorsOfClass d.liftedFactors members) =
      liftedFactorProduct d (liftedSubsetOfClass d members) := by
  rw [← polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct (selectedFactorsOfClass d.liftedFactors members)) =
    HexPolyZMathlib.toPolynomial
      (Array.polyProduct
        (liftedSubsetSelectedList d
          (liftedSubsetOfClass d members)).toArray)
  rw [polyProduct_toPolynomial, polyProduct_toPolynomial]
  have hselected :=
    bhksIndicatorSelectedFactorsArray_classIndicatorArray_toList
      d.liftedFactors members
  rw [selectedFactorsOfClass, hselected, List.toList_toArray,
    liftedSubsetSelectedList_liftedSubsetOfClass]
  have hmap :
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (fun i => i.val) =
        (List.range d.liftedFactors.size).filter fun i => i ∈ members := by
    have hcoe_inj :
        Function.Injective
          (fun i : Fin d.liftedFactors.size => i.val) := by
      intro a b h
      exact Fin.ext h
    rw [List.map_filter
      (f := fun i : Fin d.liftedFactors.size => i.val)
      (p := fun i : Fin d.liftedFactors.size => i.val ∈ members)
      hcoe_inj (List.finRange d.liftedFactors.size)]
    rw [List.map_coe_finRange_eq_range]
    apply List.filter_congr
    intro i hi
    have hi_size : i < d.liftedFactors.size := List.mem_range.mp hi
    by_cases hmem : i ∈ members
    · rw [show decide (i ∈ members) = true from decide_eq_true hmem]
      apply decide_eq_true
      exact ⟨⟨i, hi_size⟩, by simp [hmem], rfl⟩
    · rw [show decide (i ∈ members) = false from decide_eq_false hmem]
      apply decide_eq_false
      intro hx
      rcases hx with ⟨x, hxmem, hxi⟩
      exact hmem (by
        have hxmem' : x.val ∈ members := of_decide_eq_true hxmem
        simpa [hxi] using hxmem')
  rw [← hmap]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  simp [liftedFactor, Array.getD, i.isLt]

/-- Every canonical class of a genuine true-support partition is itself the
carrier of a true support. -/
theorem liftedSubsetOfClass_mem
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin r, i ∈ S → i ∈ T → S = T)
    (d : Hex.LiftData) (hr : d.liftedFactors.size = r)
    {members : List Nat}
    (hmem : members ∈ supportPartitionByMinColumn trueSupports) :
    (↑(liftedSubsetOfClass d members) :
        Set (LiftedFactorIndex d)) ∈
      (hr ▸ trueSupports) := by
  subst r
  unfold supportPartitionByMinColumn at hmem
  rw [List.mem_map] at hmem
  obtain ⟨rep, hrep, rfl⟩ := hmem
  obtain ⟨S, hS, hmembers⟩ :=
    supportClassMembers_eq_support_of_partition
      trueSupports hcover hdisjoint hrep
  have hset :
      (↑(liftedSubsetOfClass d
          (supportClassMembers trueSupports rep)) :
        Set (LiftedFactorIndex d)) = S := by
    ext i
    simp only [SetLike.mem_coe, mem_liftedSubsetOfClass]
    exact (hmembers i.val).trans (by
      constructor
      · rintro ⟨_, hi⟩
        exact hi
      · intro hi
        exact ⟨i.isLt, hi⟩)
  rw [hset]
  exact hS

/-- The canonical recovered factor attached to a support class. -/
def recoveredClassFactor
    (core : Hex.ZPoly) (d : Hex.LiftData) (members : List Nat) : Hex.ZPoly :=
  liftedRecoveryCandidate core d (liftedSubsetOfClass d members)

/-- Recovered factors in the executable canonical class order. -/
noncomputable def recoveredClassFactors
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (trueSupports : Set (Set (LiftedFactorIndex d))) : Array Hex.ZPoly :=
  ((supportPartitionByMinColumn trueSupports).map
    (recoveredClassFactor core d)).toArray

/-- A canonical recovered class factor is the represented irreducible factor
carried by that true support, with the normalization facts needed by the
executable candidate check. -/
theorem recoveredClassFactor_spec
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_i : ∀ i : LiftedFactorIndex d,
      Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    {members : List Nat}
    (hmem : members ∈
      supportPartitionByMinColumn (liftedTrueSupports core d)) :
    let factor := recoveredClassFactor core d members
    let S := liftedSubsetOfClass d members
    Irreducible (HexPolyZMathlib.toPolynomial factor) ∧
      factor ∣ core ∧
      Hex.ZPoly.Primitive factor ∧
      0 < Hex.DensePoly.leadingCoeff factor ∧
      0 < factor.degree?.getD 0 ∧
      RepresentsIntegerFactorAtLift core d factor S := by
  classical
  have hS :
      (↑(liftedSubsetOfClass d members) :
        Set (LiftedFactorIndex d)) ∈ liftedTrueSupports core d :=
    liftedSubsetOfClass_mem
      (liftedTrueSupports core d)
      (liftedTrueSupports.cover_of_partition hpartition)
      (liftedTrueSupports.eq_of_mem_inter_of_partition hpartition)
      d rfl hmem
  rcases hS with ⟨factor, S, hirr, hdvd, hrep, hScoe⟩
  have hST : S = liftedSubsetOfClass d members := by
    apply Finset.coe_injective
    exact hScoe
  subst S
  have hfactor_eq :
      recoveredClassFactor core d members = factor := by
    unfold recoveredClassFactor
    exact hpartition.liftedRecoveryCandidate_eq
      hirr hdvd (Finset.subset_univ _) hrep
  have hprops :=
    representsIntegerFactorAtLift_primitive
      hcore_ne hcore_prim hcore_lc_pos hmonic_i hprecision_core
      hpartition hirr hdvd
      ⟨1, (Hex.DensePoly.mul_one_right_poly core).symm⟩
      (Finset.subset_univ _) hrep
  have hnorm : Hex.normalizeFactorSign factor = factor :=
    Hex.normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
      factor (le_of_lt hprops.2)
  have hrecord : Hex.shouldRecordPolynomialFactor factor = true :=
    shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr
  have hdeg : 0 < factor.degree?.getD 0 :=
    Hex.degree_pos_of_primitive_norm_record
      factor hprops.1 hnorm hrecord
  simp only
  rw [hfactor_eq]
  exact ⟨hirr, hdvd, hprops.1, hprops.2, hdeg, hrep⟩

/-- The canonical recovered class factors multiply back to the primitive,
positive-leading square-free core. -/
theorem recoveredClassFactors_polyProduct
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_i : ∀ i : LiftedFactorIndex d,
      Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core) :
    Array.polyProduct
        (recoveredClassFactors core d (liftedTrueSupports core d)) = core := by
  classical
  let supports := liftedTrueSupports core d
  let classes := supportPartitionByMinColumn supports
  let factor := recoveredClassFactor core d
  let gs : List (Polynomial ℤ) :=
    classes.map fun members =>
      HexPolyZMathlib.toPolynomial (factor members)
  have hspec : ∀ members ∈ classes,
      Irreducible
          (HexPolyZMathlib.toPolynomial (factor members)) ∧
        factor members ∣ core ∧
        Hex.ZPoly.Primitive (factor members) ∧
        0 < Hex.DensePoly.leadingCoeff (factor members) ∧
        0 < (factor members).degree?.getD 0 ∧
        RepresentsIntegerFactorAtLift core d (factor members)
          (liftedSubsetOfClass d members) := by
    intro members hmem
    exact recoveredClassFactor_spec
      hcore_ne hcore_prim hcore_lc_pos hmonic_i hprecision_core
      hpartition (by simpa only [supports, classes, factor] using hmem)
  have hclasses_nodup : classes.Nodup := by
    unfold classes supportPartitionByMinColumn
    refine List.Nodup.map_on ?_ ((List.nodup_range).filter _)
    intro rep₁ hrep₁ rep₂ hrep₂ heq
    have hrep₁' :
        rep₁ ∈ supportRepresentativeColumns supports :=
      hrep₁
    have hrep₂' :
        rep₂ ∈ supportRepresentativeColumns supports :=
      hrep₂
    have h₁ :
        rep₁ ∈ supportClassMembers supports rep₂ := by
      rw [← heq]
      exact supportClassMembers_rep_mem supports hrep₁'
    have h₂ :
        rep₂ ∈ supportClassMembers supports rep₁ := by
      rw [heq]
      exact supportClassMembers_rep_mem supports hrep₂'
    rcases lt_trichotomy rep₁ rep₂ with hlt | heq' | hgt
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₂ rep₁).mp h₁ |>.2)
        (supportRepresentativeColumns_min supports hrep₂' rep₁ hlt)
    · exact heq'
    · exact absurd
        ((mem_supportClassMembers_iff supports rep₁ rep₂).mp h₂ |>.2)
        (supportRepresentativeColumns_min supports hrep₁' rep₂ hgt)
  have hfactor_inj :
      ∀ m₁ ∈ classes, ∀ m₂ ∈ classes,
        HexPolyZMathlib.toPolynomial (factor m₁) =
          HexPolyZMathlib.toPolynomial (factor m₂) →
        m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ heq
    have hs₁ := hspec m₁ hm₁
    have hs₂ := hspec m₂ hm₂
    have hsub :
        liftedSubsetOfClass d m₁ = liftedSubsetOfClass d m₂ :=
      hpartition.unique_up_to_associated
        hs₁.1 hs₁.2.1 (Finset.subset_univ _) hs₁.2.2.2.2.2
        hs₂.1 hs₂.2.1 (Finset.subset_univ _) hs₂.2.2.2.2.2
        (Associated.of_eq heq)
    unfold classes supportPartitionByMinColumn at hm₁ hm₂
    rw [List.mem_map] at hm₁ hm₂
    obtain ⟨rep₁, hrep₁, rfl⟩ := hm₁
    obtain ⟨rep₂, hrep₂, rfl⟩ := hm₂
    have hrep₁' :
        rep₁ ∈ supportRepresentativeColumns supports := hrep₁
    have hrep₂' :
        rep₂ ∈ supportRepresentativeColumns supports := hrep₂
    have hmem₁ :
        rep₁ ∈ supportClassMembers supports rep₂ := by
      have hi : (⟨rep₁,
          supportRepresentativeColumns_lt supports hrep₁'⟩ :
          LiftedFactorIndex d) ∈
          liftedSubsetOfClass d (supportClassMembers supports rep₁) := by
        simp only [mem_liftedSubsetOfClass]
        exact supportClassMembers_rep_mem supports hrep₁'
      rw [hsub] at hi
      exact (mem_liftedSubsetOfClass d _ _).mp hi
    have hmem₂ :
        rep₂ ∈ supportClassMembers supports rep₁ := by
      have hi : (⟨rep₂,
          supportRepresentativeColumns_lt supports hrep₂'⟩ :
          LiftedFactorIndex d) ∈
          liftedSubsetOfClass d (supportClassMembers supports rep₂) := by
        simp only [mem_liftedSubsetOfClass]
        exact supportClassMembers_rep_mem supports hrep₂'
      rw [← hsub] at hi
      exact (mem_liftedSubsetOfClass d _ _).mp hi
    have hrep_eq : rep₁ = rep₂ := by
      rcases lt_trichotomy rep₁ rep₂ with hlt | heq' | hgt
      · exact absurd
          ((mem_supportClassMembers_iff supports rep₂ rep₁).mp hmem₁ |>.2)
          (supportRepresentativeColumns_min supports hrep₂' rep₁ hlt)
      · exact heq'
      · exact absurd
          ((mem_supportClassMembers_iff supports rep₁ rep₂).mp hmem₂ |>.2)
          (supportRepresentativeColumns_min supports hrep₁' rep₂ hgt)
    rw [hrep_eq]
  have hgs_nodup : gs.Nodup := by
    exact List.Nodup.map_on hfactor_inj hclasses_nodup
  let xPoly : Polynomial ℤ := HexPolyZMathlib.toPolynomial core
  have hx_ne : xPoly ≠ 0 := by
    intro h
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial core =
      HexPolyZMathlib.toPolynomial 0
    rw [HexPolyZMathlib.toPolynomial_zero]
    exact h
  have hsubset :
      (gs : Multiset (Polynomial ℤ)) ⊆
        UniqueFactorizationMonoid.normalizedFactors xPoly := by
    intro p hp
    rw [Multiset.mem_coe, List.mem_map] at hp
    obtain ⟨members, hmembers, rfl⟩ := hp
    have hs := hspec members hmembers
    obtain ⟨q, hq, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hx_ne hs.1 (by
          simpa only [xPoly] using HexPolyMathlib.toPolynomial_dvd hs.2.1)
    have hq_norm : normalize q = q :=
      UniqueFactorizationMonoid.normalize_normalized_factor q hq
    have hp_norm :
        normalize (HexPolyZMathlib.toPolynomial (factor members)) =
          HexPolyZMathlib.toPolynomial (factor members) := by
      have hlc :
          0 ≤ (HexPolyZMathlib.toPolynomial
            (factor members)).leadingCoeff := by
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact le_of_lt hs.2.2.2.1
      rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq,
        if_pos hlc, Units.val_one, Polynomial.C_1, mul_one]
    have heq :
        HexPolyZMathlib.toPolynomial (factor members) = q := by
      rw [← hp_norm, ← hq_norm]
      exact normalize_eq_normalize_iff_associated.mpr hassoc
    rw [heq]
    exact hq
  have hle :
      (gs : Multiset (Polynomial ℤ)) ≤
        UniqueFactorizationMonoid.normalizedFactors xPoly :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hgs_nodup)).2 hsubset
  have hcard :
      (gs : Multiset (Polynomial ℤ)).card =
        (UniqueFactorizationMonoid.normalizedFactors xPoly).card := by
    change gs.length =
      (UniqueFactorizationMonoid.normalizedFactors xPoly).card
    simpa only [gs, classes, supports, xPoly, List.length_map] using
      (BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card
        hpartition hcore_ne hcore_prim hcore_lc_pos hprecision_core)
  have hmultiset :
      (gs : Multiset (Polynomial ℤ)) =
        UniqueFactorizationMonoid.normalizedFactors xPoly :=
    Multiset.eq_of_le_of_card_le hle (by omega)
  have hx_norm : normalize xPoly = xPoly := by
    have hlc : 0 ≤ xPoly.leadingCoeff := by
      change 0 ≤ (HexPolyZMathlib.toPolynomial core).leadingCoeff
      rw [HexPolyMathlib.leadingCoeff_toPolynomial]
      exact le_of_lt hcore_lc_pos
    rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq,
      if_pos hlc, Units.val_one, Polynomial.C_1, mul_one]
  have hprod_norm :
      (UniqueFactorizationMonoid.normalizedFactors xPoly).prod = xPoly := by
    have h :=
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hx_ne
    rw [hx_norm] at h
    exact h
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial
      (Array.polyProduct
        (recoveredClassFactors core d (liftedTrueSupports core d))) =
    HexPolyZMathlib.toPolynomial core
  rw [polyProduct_toPolynomial]
  simp only [recoveredClassFactors, List.toList_toArray, List.map_map,
    Function.comp_def]
  change gs.prod = xPoly
  change (gs : Multiset (Polynomial ℤ)).prod = xPoly
  rw [hmultiset]
  exact hprod_norm

/-- Once the projected lattice has exactly the true-support span, every
canonical RREF class reconstructs its represented integer factor and the
executable candidate fold returns the canonical recovered array. -/
theorem bhksIndicatorCandidates_eq_some_of_span_eq
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_i : ∀ i : LiftedFactorIndex d,
      Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hprecision_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound
          (Hex.ZPoly.toMonic core).monic < d.p ^ d.k)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).factorCount +
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              d.p d.k d.liftedFactors) hrows) =
        trueSupportSpanInt (liftedTrueSupports core d)) :
    Hex.bhksIndicatorCandidates? core d
        (Hex.bhksEquivalenceClassIndicators
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              d.p d.k d.liftedFactors) hrows)) =
      some (recoveredClassFactors core d (liftedTrueSupports core d)) := by
  classical
  let supports := liftedTrueSupports core d
  let classes := supportPartitionByMinColumn supports
  let projected :=
    Hex.bhksProjectedRows
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors) hrows
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  let candidates := recoveredClassFactors core d supports
  have hfactorCount : projected.factorCount = d.liftedFactors.size := by
    rfl
  have hspan' :
      projectedRowSpanInt projected = trueSupportSpanInt supports := by
    simpa only [projected, supports] using hspan
  have hindicators :
      indicators =
        (classes.map (classIndicatorArray projected.factorCount)).toArray := by
    exact bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  refine Hex.bhksIndicatorCandidates?_eq_some_of_getD
    core d indicators candidates ?_ ?_
  · rw [hindicators]
    simp [candidates, recoveredClassFactors, classes]
  · intro i hi
    have hi_classes : i < classes.length := by
      rw [hindicators] at hi
      simpa using hi
    let members := classes[i]
    have hmembers : members ∈ classes := by
      exact List.getElem_mem ..
    have hindicator :
        indicators.getD i #[] =
          classIndicatorArray d.liftedFactors.size members := by
      rw [hindicators]
      simp [Array.getD, hi_classes, members, hfactorCount]
    have hcandidate :
        candidates.getD i 0 = recoveredClassFactor core d members := by
      simp [candidates, recoveredClassFactors, classes, Array.getD,
        hi_classes, members]
    have hnonempty :
        ∃ j, j < (classIndicatorArray d.liftedFactors.size members).size ∧
          (classIndicatorArray d.liftedFactors.size members).getD j 0 = 1 := by
      have hmapped : members ∈
          (supportRepresentativeColumns supports).map
            (supportClassMembers supports) := by
        simpa only [classes, supportPartitionByMinColumn] using hmembers
      rw [List.mem_map] at hmapped
      obtain ⟨rep, hrep, hmembers_eq⟩ := hmapped
      have hrep_mem : rep ∈ members := by
        rw [← hmembers_eq]
        exact supportClassMembers_rep_mem supports hrep
      refine ⟨rep, ?_, ?_⟩
      · simpa using supportRepresentativeColumns_lt supports hrep
      · exact classIndicatorArray_has_one_of_mem
          d.liftedFactors.size members
          (supportRepresentativeColumns_lt supports hrep)
          hrep_mem
    let selected := selectedFactorsOfClass d.liftedFactors members
    have hselected :
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (classIndicatorArray d.liftedFactors.size members) =
          some selected := by
      exact Hex.bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
        d.liftedFactors
        (classIndicatorArray d.liftedFactors.size members)
        (classIndicatorArray_size _ _)
        (classIndicatorArray_bits _ _) hnonempty
    have hspec := recoveredClassFactor_spec
      hcore_ne hcore_prim hcore_lc_pos hmonic_i hprecision_core
      hpartition (by simpa only [supports, classes] using hmembers)
    let factor := recoveredClassFactor core d members
    let S := liftedSubsetOfClass d members
    have hm_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
      Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree
        core hcore_lc_pos hcore_pos
    have hm_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 :=
      zpoly_ne_zero_of_monic hm_monic
    let R : RecoveredAtLift core d factor S :=
      hspec.2.2.2.2.2.some
    have hvalid : ∀ k, (R.monicFactor.coeff k).natAbs ≤
        Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic :=
      fun k => defaultFactorCoeffBound_valid
        (Hex.ZPoly.toMonic core).monic hm_ne
        R.monicFactor R.monic_dvd k
    have hcenter :
        Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k) =
          R.monicFactor := by
      change Hex.centeredLiftPoly
          (Array.polyProduct
            (selectedFactorsOfClass d.liftedFactors members))
          (d.p ^ d.k) = R.monicFactor
      rw [selectedFactorsOfClass_polyProduct]
      rw [← centeredLiftPoly_reduceModPow_absorb _ _ _ d.p_pos, R.congr]
      exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
        R.monicFactor d.p d.k
          (Hex.ZPoly.defaultFactorCoeffBound
            (Hex.ZPoly.toMonic core).monic)
        hvalid hprecision_monic
    rw [hindicator, hcandidate]
    exact Hex.bhksIndicatorCandidate?_eq_some_of_monicLift
      core d
      (classIndicatorArray d.liftedFactors.size members)
      selected R.monicFactor factor
      hselected hspec.2.1 (le_of_lt hspec.2.2.2.1)
      hspec.2.2.2.1 hspec.2.2.2.2.1 hcenter R.dilate_eq

/-- A nonempty genuine support partition cannot have exact projected span with
an empty executable row array. -/
theorem projectedRows_isEmpty_eq_false_of_span_eq
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hspan : projectedRowSpanInt L = trueSupportSpanInt trueSupports)
    (hcover : ∀ i : Fin L.factorCount, ∃ S ∈ trueSupports, i ∈ S)
    (hclasses :
      supportPartitionByMinColumn trueSupports ≠ []) :
    L.projectedRows.isEmpty = false := by
  classical
  by_contra hfalse
  have hempty : L.projectedRows.isEmpty = true := by
    cases h : L.projectedRows.isEmpty <;> simp_all
  have hsize : L.projectedRows.size = 0 :=
    Array.isEmpty_iff_size_eq_zero.mp hempty
  have hspan_bot : projectedRowSpanInt L = ⊥ := by
    unfold projectedRowSpanInt
    have hrange :
        Set.range (fun i : Fin L.projectedRows.size =>
          Matrix.row (projectedRowsIntMatrix L) i) = ∅ := by
      ext v
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, rfl⟩
      have hi := i.isLt
      omega
    rw [hrange, Submodule.span_empty]
  obtain ⟨members, hmembers⟩ :=
    List.exists_mem_of_ne_nil _ hclasses
  unfold supportPartitionByMinColumn at hmembers
  rw [List.mem_map] at hmembers
  obtain ⟨rep, hrep, _⟩ := hmembers
  have hreplt := supportRepresentativeColumns_lt trueSupports hrep
  obtain ⟨S, hS, hrepS⟩ := hcover ⟨rep, hreplt⟩
  let support : trueSupports := ⟨S, hS⟩
  have hindicator :
      indicatorVector support.1 ∈ projectedRowSpanInt L := by
    rw [hspan]
    exact indicatorVector_mem_trueSupportSpanInt trueSupports support
  rw [hspan_bot] at hindicator
  have hzero : indicatorVector S = 0 := hindicator
  have hcoord := congrFun hzero ⟨rep, hreplt⟩
  rw [indicatorVector_apply_mem S hrepS] at hcoord
  norm_num at hcoord

/-- If exact span recovery yields at least two true-support classes, all
nondegeneracy, candidate, and product guards of fixed-precision BHKS recovery
pass. -/
theorem bhksRecover_eq_some_of_span_eq
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hmonic_i : ∀ i : LiftedFactorIndex d,
      Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hprecision_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound
          (Hex.ZPoly.toMonic core).monic < d.p ^ d.k)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).factorCount +
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              d.p d.k d.liftedFactors) hrows) =
        trueSupportSpanInt (liftedTrueSupports core d))
    (hclasses : 2 ≤
      (supportPartitionByMinColumn (liftedTrueSupports core d)).length) :
    Hex.bhksRecover? core d =
      some (recoveredClassFactors core d (liftedTrueSupports core d)) := by
  let L := Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
    d.p d.k d.liftedFactors
  let projected := Hex.bhksProjectedRows L hrows
  let supports := liftedTrueSupports core d
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  let candidates := recoveredClassFactors core d supports
  have hspan' : projectedRowSpanInt projected =
      trueSupportSpanInt supports := by
    simpa only [projected, L, supports] using hspan
  have hindicators :
      indicators =
        ((supportPartitionByMinColumn supports).map
          (classIndicatorArray projected.factorCount)).toArray :=
    bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  have hind_size :
      indicators.size =
        (supportPartitionByMinColumn supports).length := by
    rw [hindicators]
    simp
  have hclasses' :
      2 ≤ (supportPartitionByMinColumn supports).length := by
    simpa only [supports] using hclasses
  have hind_nonempty : indicators.isEmpty = false := by
    cases he : indicators.isEmpty with
    | false => rfl
    | true =>
        have hz : indicators.size = 0 :=
          Array.isEmpty_iff_size_eq_zero.mp he
        rw [hind_size] at hz
        exfalso
        omega
  have hprojected_nonempty : projected.projectedRows.isEmpty = false :=
    projectedRows_isEmpty_eq_false_of_span_eq
      projected supports hspan'
      (liftedTrueSupports.cover_of_partition hpartition)
      (by
        intro hnil
        have hz :
            (supportPartitionByMinColumn supports).length = 0 :=
          congrArg List.length hnil
        omega)
  have hind_not_one : (indicators.size == 1) = false := by
    simp only [beq_eq_false_iff_ne]
    rw [hind_size]
    omega
  have hnondeg :
      Hex.bhksDegenerateIndicatorPartition projected indicators = false := by
    exact Hex.bhksDegenerateIndicatorPartition_eq_false
      projected indicators hind_nonempty hprojected_nonempty hind_not_one
  have hcandidates :
      Hex.bhksIndicatorCandidates? core d indicators = some candidates := by
    exact bhksIndicatorCandidates_eq_some_of_span_eq
      hcore_ne hcore_pos hcore_prim hcore_lc_pos hmonic_i
      hprecision_core hprecision_monic hpartition hrows hspan
  have hproduct : Array.polyProduct candidates = core := by
    exact recoveredClassFactors_polyProduct
      hcore_ne hcore_prim hcore_lc_pos hmonic_i hprecision_core hpartition
  exact Hex.bhksRecover?_eq_some_of_checks core d hrows
    (by simpa only [L, projected, indicators] using hnondeg)
    (by simpa only [L, projected, indicators, candidates] using hcandidates)
    (by simpa only [candidates, supports] using hproduct)

/-- If exact span recovery has exactly one true-support class, the executable
cap certificate is the nonempty single all-ones partition. -/
theorem bhksSingleAllOnesPartition_eq_true_of_span_eq
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).factorCount +
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        d.p d.k d.liftedFactors).coeffWidth)
    (hspan :
      projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              d.p d.k d.liftedFactors) hrows) =
        trueSupportSpanInt (liftedTrueSupports core d))
    (hclasses :
      (supportPartitionByMinColumn
        (liftedTrueSupports core d)).length = 1) :
    Hex.bhksSingleAllOnesPartition core d = true := by
  classical
  let L := Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
    d.p d.k d.liftedFactors
  let projected := Hex.bhksProjectedRows L hrows
  let supports := liftedTrueSupports core d
  let classes := supportPartitionByMinColumn supports
  let indicators := Hex.bhksEquivalenceClassIndicators projected
  have hspan' : projectedRowSpanInt projected =
      trueSupportSpanInt supports := by
    simpa only [projected, L, supports] using hspan
  have hindicators :
      indicators =
        (classes.map
          (classIndicatorArray projected.factorCount)).toArray := by
    exact bhksEquivalenceClassIndicators_eq_supportPartition
      projected supports hspan'
  have hclasses' : classes.length = 1 := by
    simpa only [classes, supports] using hclasses
  obtain ⟨members, hclasses_list⟩ :=
    List.length_eq_one_iff.mp hclasses'
  have hmembers : members ∈ classes := by
    rw [hclasses_list]
    simp
  have hmapped : members ∈
      (supportRepresentativeColumns supports).map
        (supportClassMembers supports) := by
    simpa only [classes, supportPartitionByMinColumn] using hmembers
  rw [List.mem_map] at hmapped
  obtain ⟨rep, hrep, hmembers_eq⟩ := hmapped
  obtain ⟨classSupport, hclassSupport, hmember_iff⟩ :=
    supportClassMembers_eq_support_of_partition supports
      (liftedTrueSupports.cover_of_partition hpartition)
      (liftedTrueSupports.eq_of_mem_inter_of_partition hpartition)
      hrep
  have hncard : supports.ncard = 1 := by
    rw [← supportPartitionByMinColumn_length_eq_ncard_of_partition
      supports
      (liftedTrueSupports.cover_of_partition hpartition)
      (liftedTrueSupports.eq_of_mem_inter_of_partition hpartition)
      (liftedTrueSupports.nonempty_of_partition
        hpartition hcore_ne hcore_prim hcore_lc_pos hprecision_core)]
    exact hclasses'
  obtain ⟨onlySupport, hsupports⟩ := Set.ncard_eq_one.mp hncard
  have hclass_only : classSupport = onlySupport := by
    rw [hsupports] at hclassSupport
    simpa using hclassSupport
  have hall_members :
      ∀ i, i < projected.factorCount → i ∈ members := by
    intro i hi
    have hfactorCount : projected.factorCount = d.liftedFactors.size := by
      rfl
    have hi' : i < d.liftedFactors.size := by
      simpa only [hfactorCount] using hi
    obtain ⟨T, hT, hiT⟩ :=
      liftedTrueSupports.cover_of_partition hpartition ⟨i, hi'⟩
    have hT_only : T = onlySupport := by
      have hT' : T ∈ supports := by
        simpa only [supports] using hT
      rw [hsupports] at hT'
      simpa using hT'
    have hi_class : (⟨i, hi'⟩ : LiftedFactorIndex d) ∈ classSupport := by
      simpa only [hT_only, hclass_only] using hiT
    have himem :
        i ∈ supportClassMembers supports rep :=
      (hmember_iff i).2 ⟨hi', hi_class⟩
    rw [hmembers_eq] at himem
    exact himem
  have hindicator_zero :
      indicators.getD 0 #[] =
        classIndicatorArray projected.factorCount members := by
    rw [hindicators, hclasses_list]
    simp [Array.getD]
  have hallones :
      Hex.bhksIndicatorAllOnes projected.factorCount
          (indicators.getD 0 #[]) = true := by
    apply Hex.bhksIndicatorAllOnes_eq_true_of_getD
    · rw [hindicator_zero, classIndicatorArray_size]
    · intro i hi
      rw [hindicator_zero, classIndicatorArray_getD]
      simp [hi, hall_members i hi]
  have hind_nonempty : indicators.isEmpty = false := by
    cases he : indicators.isEmpty with
    | false => rfl
    | true =>
        have hz : indicators.size = 0 :=
          Array.isEmpty_iff_size_eq_zero.mp he
        have hone : indicators.size = 1 := by
          rw [hindicators, hclasses_list]
          simp
        omega
  have hclasses_ne :
      supportPartitionByMinColumn (liftedTrueSupports core d) ≠ [] := by
    intro hnil
    rw [hnil] at hclasses
    simp at hclasses
  have hprojected_nonempty : projected.projectedRows.isEmpty = false := by
    simpa only [projected, L] using
      (projectedRows_isEmpty_eq_false_of_span_eq
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            d.p d.k d.liftedFactors) hrows)
        (liftedTrueSupports core d) hspan
        (liftedTrueSupports.cover_of_partition hpartition)
        hclasses_ne)
  rw [Hex.bhksSingleAllOnesPartition, dif_pos hrows]
  change (!indicators.isEmpty && !projected.projectedRows.isEmpty &&
    indicators.size == 1 &&
      Hex.bhksIndicatorAllOnes projected.factorCount
        (indicators.getD 0 #[])) = true
  have hind_size : indicators.size = 1 := by
    rw [hindicators, hclasses_list]
    simp
  have hzero_lt : 0 < indicators.size := by omega
  have hallones_get :
      Hex.bhksIndicatorAllOnes projected.factorCount indicators[0] = true := by
    simpa [Array.getD, hzero_lt] using hallones
  simp [hind_nonempty, hprojected_nonempty, hind_size, hallones_get]

end BHKS

set_option maxHeartbeats 1000000 in
/-- Package a `RecoveredAtLift` carrier as a `BHKS.RecoveredLift` certificate
for the monic-coordinate BHKS lattice: the recovered `monicFactor` is an exact
integer factor of the monic transform, recovered from the support product by
the centred lift at Mignotte-adequate precision. -/
noncomputable def recoveredLiftOfRecoveredAtLift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hprecision_m :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    {factor : Hex.ZPoly}
    {S' : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (R : RecoveredAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) factor S') :
    BHKS.RecoveredLift
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData).p
        (Hex.ZPoly.toMonicLiftData core B primeData).k
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors)
      (↑S' : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))) :=
  { f := (Hex.ZPoly.toMonic core).monic
    p := (Hex.ZPoly.toMonicLiftData core B primeData).p
    a := (Hex.ZPoly.toMonicLiftData core B primeData).k
    liftedFactors := (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors
    basis_eq := rfl
    factor := R.monicFactor
    cofactor := R.monic_dvd.choose
    factor_mul := R.monic_dvd.choose_spec.symm
    recovered_eq := by
      have hm_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
        Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
      have hm_lc : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
        hm_monic
      have hm_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 :=
        zpoly_ne_zero_of_pos_lc (by rw [hm_lc]; exact Int.zero_lt_one)
      have hvalid : ∀ i, (R.monicFactor.coeff i).natAbs ≤
          Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic := fun i =>
        defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hm_ne
          R.monicFactor R.monic_dvd i
      have hcl : Hex.centeredLiftPoly
          (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) S')
          ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
            (Hex.ZPoly.toMonicLiftData core B primeData).k) = R.monicFactor := by
        rw [← centeredLiftPoly_reduceModPow_absorb _ _ _
          (Hex.ZPoly.toMonicLiftData core B primeData).p_pos, R.congr]
        exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
          R.monicFactor _ _ _ hvalid hprecision_m
      show Hex.ZPoly.dilate
          (Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic)
          (Hex.centeredLiftPoly
            (BHKS.supportProduct
              (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core B primeData).p
                (Hex.ZPoly.toMonicLiftData core B primeData).k
                (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors)
              (↑S' : Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))))
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k)) = R.monicFactor
      rw [supportProduct_coe_eq_liftedFactorProduct, hm_lc, Hex.ZPoly.dilate_one]
      exact hcl }

set_option maxHeartbeats 1000000 in
/-- **The `W ⊆ L'` count lower bound.** For a primitive square-free
positive-degree `core` under the monic-transform prime selection at a
coefficient bound `B` clearing the fast-core acceptance floor, the number of
irreducible factors of `core` over `ℤ` is at most the number of executable
BHKS equivalence classes of the monic-coordinate CLD lattice.

This is the van Hoeij adequacy direction both LatticeTier obligations consume:
each true-factor support survives the LLL/Gram-Schmidt cut as a distinct RREF
signature class. -/
theorem normalizedFactors_card_le_bhksEquivalenceClassIndicators_size
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    {L : Hex.BhksLatticeBasis}
    (hL : L = Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
      (Hex.ZPoly.toMonicLiftData core B primeData).p
      (Hex.ZPoly.toMonicLiftData core B primeData).k
      (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth) :
    (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card ≤
      (Hex.bhksEquivalenceClassIndicators (Hex.bhksProjectedRows L hrows)).size := by
  subst hL
  classical
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hp1 : 1 < primeData.p := hp2
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne
  have hprec_spec : 2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hprec_spec
    omega
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k
      = Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_k _ _ _
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_p _ _ _
  have hm_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hfloor_dfcb_m := Hex.defaultFactorCoeffBound_toMonic_le_bhksRecoveryFloor core
  have hfloor_dfcb := Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
  have hfloor_cld := Hex.cldCoeffFloor_le_bhksRecoveryFloor core
  have hbound_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by omega
  have hprecision_m :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound_monic
  have hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; omega
  -- the #8413 partition of the lifted indices by true-factor supports
  have hpartition : LiftedFactorSubsetPartition core
      (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ core :=
    liftedFactorSubsetPartition_of_toMonicModP core B primeData
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
      hcore_lc_pos hcore_pos hcore_prim hcore_sqfree hB_ne hbound_monic
  -- per-factor Hensel facts
  have hmonic_i := Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
    core B primeData hcore_lc_pos hcore_pos
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  have hdeg_i := Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
    core B primeData hcore_lc_pos hcore_pos
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  -- the quadratic multifactor lift invariant and the full-product congruence
  have hform : Hex.factorsModPBerlekampForm (Hex.ZPoly.toMonic core).monic primeData :=
    Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic primeData.p = true :=
    Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      (Hex.ZPoly.toMonic core).monic (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp1 hprec_pos hm_monic
      (factorsModP_monic_of_factorsModPBerlekampForm _ primeData hform)
      (factorsModP_polyProduct_congr_of_factorsModPBerlekampForm _ primeData
        hm_monic hform hgood)
      (factorsModP_coprime_of_factorsModPBerlekampForm _ primeData hform hgood)
      (factorsModP_ne_nil_of_factorsModPBerlekampForm _ primeData hform)
  have hprod_univ : Hex.ZPoly.congr
      (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ)
      (Hex.ZPoly.toMonic core).monic
      (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) := by
    show Hex.ZPoly.congr
      (liftedFactorProduct
        (Hex.henselLiftData (Hex.ZPoly.toMonic core).monic
          (Hex.precisionForCoeffBound B primeData.p) primeData) Finset.univ)
      (Hex.ZPoly.toMonic core).monic
      (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    exact henselLiftData_liftedFactorProduct_univ_congr_core _ _ _ hinv hp1 hprec_pos
  -- per-index modular cofactor witnesses
  have hfac_all : ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic
          ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD i.val 1) ∧
        0 < ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
              i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr (Hex.ZPoly.toMonic core).monic
          ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD i.val 1 * h)
          ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
            (Hex.ZPoly.toMonicLiftData core B primeData).k) := by
    intro i
    have hgetD : (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD i.val 1
        = liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    refine ⟨liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
      (Finset.univ \ {i}), ?_, ?_, ?_⟩
    · rw [hgetD]; exact hmonic_i i
    · rw [hgetD]
      have h := hdeg_i i
      rwa [HexPolyMathlib.natDegree_toPolynomial] at h
    · rw [hgetD]
      have hsplit := liftedFactorProduct_eq_mul_sdiff_of_subset
        (Finset.subset_univ ({i} : LiftedFactorSubset
          (Hex.ZPoly.toMonicLiftData core B primeData)))
      rw [← liftedFactorProduct_singleton (Hex.ZPoly.toMonicLiftData core B primeData) i,
        ← hsplit, hp_eq, hk_eq]
      exact Hex.ZPoly.congr_symm _ _ _ hprod_univ
  -- column separation and threshold admissibility at the lift precision
  have hsep_all : ∀ j, 2 * Hex.bhksCoeffBound (Hex.ZPoly.toMonic core).monic j <
      (Hex.ZPoly.toMonicLiftData core B primeData).p ^
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    intro j
    have hcb := two_mul_bhksCoeffBound_toMonic_le_cldCoeffFloor core j
    rw [hp_eq, hk_eq]
    omega
  have hthr_all : ∀ j,
      Hex.bhksCoeffCutThreshold
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonic core).monic j ≤
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    intro j
    have hcb := two_mul_bhksCoeffBound_toMonic_le_cldCoeffFloor core j
    rw [hp_eq, hk_eq]
    unfold Hex.bhksCoeffCutThreshold Hex.precisionForCoeffBound
    have hpow := Hex.le_pow_ceilLogP hp2 (2 * B + 1)
    exact Hex.ceilLogP_le_of_le_pow hp2 _ _ (by omega)
  have hk1 : 1 < (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]
    omega
  -- independence of the BHKS basis
  have hbasis := bhksLatticeBasis_basis_independent (Hex.ZPoly.toMonic core).monic
    (Hex.ZPoly.toMonicLiftData core B primeData).p
    (Hex.ZPoly.toMonicLiftData core B primeData).k
    (by rw [hp_eq]; omega)
    (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors
  -- the cut inclusion W ⊆ L': every true support's indicator survives the cut
  have hcut : BHKS.CutProjectionHypotheses
      (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonicLiftData core B primeData).k
          (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) hrows)
      (liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) := by
    refine BHKS.cutProjectionHypotheses_of_shortVectors _ hrows hbasis _ (fun S => ?_)
    have hmem := S.2
    have hrep : RepresentsIntegerFactorAtLift core
        (Hex.ZPoly.toMonicLiftData core B primeData)
        hmem.choose hmem.choose_spec.choose :=
      hmem.choose_spec.choose_spec.2.2.1
    have hcast : (↑hmem.choose_spec.choose :
        Set (LiftedFactorIndex (Hex.ZPoly.toMonicLiftData core B primeData))) = S.1 :=
      hmem.choose_spec.choose_spec.2.2.2
    rw [← hcast]
    have R : RecoveredAtLift core (Hex.ZPoly.toMonicLiftData core B primeData)
        hmem.choose hmem.choose_spec.choose := hrep.some
    -- monicity of the recovered monic factor, through the exact centred lift
    have hm_lc : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 :=
      hm_monic
    have hm_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 :=
      zpoly_ne_zero_of_pos_lc (by rw [hm_lc]; exact Int.zero_lt_one)
    have hvalid : ∀ i, (R.monicFactor.coeff i).natAbs ≤
        Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic := fun i =>
      defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hm_ne
        R.monicFactor R.monic_dvd i
    have hcl : Hex.centeredLiftPoly
        (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
          hmem.choose_spec.choose)
        ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k) = R.monicFactor := by
      rw [← centeredLiftPoly_reduceModPow_absorb _ _ _
        (Hex.ZPoly.toMonicLiftData core B primeData).p_pos, R.congr]
      exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
        R.monicFactor _ _ _ hvalid hprecision_m
    have hlfp_monic : Hex.DensePoly.Monic
        (liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData)
          hmem.choose_spec.choose) :=
      liftedFactorProduct_monic _ _ (fun i _ => hmonic_i i)
    have hmf_monic : (HexPolyMathlib.toPolynomial R.monicFactor).Monic := by
      rw [← hcl]
      exact HexHenselMathlib.toPolynomial_monic_of_dense_monic _
        (monic_centeredLiftPoly_of_monic hlfp_monic (by omega))
    exact BHKS.supportShortVectorData_of_recoveredLift
      (recoveredLiftOfRecoveredAtLift hcore_lc_pos hcore_pos hprecision_m R)
      hm_lc hmf_monic
      (show (2 : Nat) ≤ (Hex.ZPoly.toMonicLiftData core B primeData).p by
        rw [hp_eq]; exact hp2)
      hk1 hsep_all hthr_all
      (fun i _ => hfac_all i)
  -- the count chain: factors = supports-partition length ≤ class count
  have hlen := BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card
    hpartition hcore_ne hcore_prim hcore_lc_pos hprecision_core
  have hle : (BHKS.supportPartitionByMinColumn
      (liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData))).length ≤
      (Hex.bhksEquivalenceClassIndicators
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            (Hex.ZPoly.toMonicLiftData core B primeData).p
            (Hex.ZPoly.toMonicLiftData core B primeData).k
            (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) hrows)).size :=
    BHKS.supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size
      (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonicLiftData core B primeData).k
          (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) hrows)
      (liftedTrueSupports core (Hex.ZPoly.toMonicLiftData core B primeData)) hcut
  omega

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
    (hfmonic : Hex.DensePoly.Monic f)
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
        q.Monic → Irreducible q → q ∣ HexPolyZMathlib.toPolynomial f →
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
    hf hfdeg hfmonic hp2 hp500 hr hk hprecision hcut hfac hdeg_le hcop hown
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

/--
At a precision clearing the explicit BHKS bound, the executable projected
lattice has exactly the span of the true lifted-factor supports.
-/
theorem bhksProjectedSpan_eq_trueSupportSpan
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_floor : Hex.bhksRecoveryFloor core ≤ B)
    (hB_ne : B ≠ 0)
    (hprecision :
      2 * Hex.bhksBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrows : 1 ≤
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData).p
        (Hex.ZPoly.toMonicLiftData core B primeData).k
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors).factorCount +
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData).p
        (Hex.ZPoly.toMonicLiftData core B primeData).k
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors).coeffWidth) :
    BHKS.projectedRowSpanInt
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
            (Hex.ZPoly.toMonicLiftData core B primeData).p
            (Hex.ZPoly.toMonicLiftData core B primeData).k
            (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) hrows) =
      BHKS.trueSupportSpanInt
        (liftedTrueSupports core
          (Hex.ZPoly.toMonicLiftData core B primeData)) := by
  classical
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hval :=
    modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos
  have hp_prime : Hex.Nat.Prime primeData.p := hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hp1 : 1 < primeData.p := hp2
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hprec_spec
    omega
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_k _ _ _
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p =
      primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_p _ _ _
  have hm_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree
      core hcore_lc_pos hcore_pos
  have hm_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 :=
    zpoly_ne_zero_of_monic hm_monic
  have hm_pos : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree
      core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hfloor_dfcb_m :=
    Hex.defaultFactorCoeffBound_toMonic_le_bhksRecoveryFloor core
  have hfloor_dfcb := Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
  have hfloor_cld := Hex.cldCoeffFloor_le_bhksRecoveryFloor core
  have hbound_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    omega
  have hprecision_m :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]
    exact hbound_monic
  have hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]
    omega
  have hpartition : LiftedFactorSubsetPartition core
      (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ core :=
    liftedFactorSubsetPartition_of_toMonicModP
      core B primeData hval hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hB_ne hbound_monic
  have hmonic_i :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos hval hprec_pos
  have hdeg_i :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos hval hprec_pos
  have hform : Hex.factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData :=
    Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form
      core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic primeData.p = true :=
    Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      (Hex.ZPoly.toMonic core).monic
      (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp1 hprec_pos hm_monic
      (factorsModP_monic_of_factorsModPBerlekampForm _ primeData hform)
      (factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
        _ primeData hm_monic hform hgood)
      (factorsModP_coprime_of_factorsModPBerlekampForm
        _ primeData hform hgood)
      (factorsModP_ne_nil_of_factorsModPBerlekampForm _ primeData hform)
  have hprod_univ : Hex.ZPoly.congr
      (liftedFactorProduct
        (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ)
      (Hex.ZPoly.toMonic core).monic
      (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) := by
    show Hex.ZPoly.congr
      (liftedFactorProduct
        (Hex.henselLiftData (Hex.ZPoly.toMonic core).monic
          (Hex.precisionForCoeffBound B primeData.p) primeData) Finset.univ)
      (Hex.ZPoly.toMonic core).monic
      (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    exact henselLiftData_liftedFactorProduct_univ_congr_core
      _ _ _ hinv hp1 hprec_pos
  have hfac_complement :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData),
        Hex.ZPoly.congr (Hex.ZPoly.toMonic core).monic
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i *
            liftedFactorProduct
              (Hex.ZPoly.toMonicLiftData core B primeData)
              ((Finset.univ : LiftedFactorSubset
                (Hex.ZPoly.toMonicLiftData core B primeData)) \ {i}))
          ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
            (Hex.ZPoly.toMonicLiftData core B primeData).k) := by
    intro i
    have hsplit := liftedFactorProduct_eq_mul_sdiff_of_subset
      (Finset.subset_univ ({i} : LiftedFactorSubset
        (Hex.ZPoly.toMonicLiftData core B primeData)))
    rw [← liftedFactorProduct_singleton
      (Hex.ZPoly.toMonicLiftData core B primeData) i,
      ← hsplit, hp_eq, hk_eq]
    exact Hex.ZPoly.congr_symm _ _ _ hprod_univ
  have hfac_all :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData),
        ∃ h : Hex.ZPoly,
          Hex.DensePoly.Monic
            ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
              i.val 1) ∧
          0 < ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
                i.val 1).degree?.getD 0 ∧
          Hex.ZPoly.congr (Hex.ZPoly.toMonic core).monic
            ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
                i.val 1 * h)
            ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
              (Hex.ZPoly.toMonicLiftData core B primeData).k) := by
    intro i
    have hgetD :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    refine ⟨liftedFactorProduct
      (Hex.ZPoly.toMonicLiftData core B primeData)
      ((Finset.univ : LiftedFactorSubset
        (Hex.ZPoly.toMonicLiftData core B primeData)) \ {i}), ?_, ?_, ?_⟩
    · rw [hgetD]
      exact hmonic_i i
    · rw [hgetD]
      have h := hdeg_i i
      rwa [HexPolyMathlib.natDegree_toPolynomial] at h
    · rw [hgetD]
      exact hfac_complement i
  have hsep_all : ∀ j,
      2 * Hex.bhksCoeffBound (Hex.ZPoly.toMonic core).monic j <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    intro j
    have hcb := two_mul_bhksCoeffBound_toMonic_le_cldCoeffFloor core j
    rw [hp_eq, hk_eq]
    omega
  have hthr_all : ∀ j,
      Hex.bhksCoeffCutThreshold
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonic core).monic j ≤
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    intro j
    have hcb := two_mul_bhksCoeffBound_toMonic_le_cldCoeffFloor core j
    rw [hp_eq, hk_eq]
    unfold Hex.bhksCoeffCutThreshold Hex.precisionForCoeffBound
    have hpow := Hex.le_pow_ceilLogP hp2 (2 * B + 1)
    exact Hex.ceilLogP_le_of_le_pow hp2 _ _ (by omega)
  have hk1 : 1 < (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]
    omega
  have hbasis :=
    bhksLatticeBasis_basis_independent (Hex.ZPoly.toMonic core).monic
      (Hex.ZPoly.toMonicLiftData core B primeData).p
      (Hex.ZPoly.toMonicLiftData core B primeData).k
      (by rw [hp_eq]; omega)
      (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors
  have data : ∀ S :
      liftedTrueSupports core
        (Hex.ZPoly.toMonicLiftData core B primeData),
      BHKS.SupportShortVectorData
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonicLiftData core B primeData).k
          (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) S.1 := by
    intro S
    have hmem := S.2
    have hrep : RepresentsIntegerFactorAtLift core
        (Hex.ZPoly.toMonicLiftData core B primeData)
        hmem.choose hmem.choose_spec.choose :=
      hmem.choose_spec.choose_spec.2.2.1
    have hcast : (↑hmem.choose_spec.choose :
        Set (LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData))) = S.1 :=
      hmem.choose_spec.choose_spec.2.2.2
    rw [← hcast]
    have R : RecoveredAtLift core
        (Hex.ZPoly.toMonicLiftData core B primeData)
        hmem.choose hmem.choose_spec.choose := hrep.some
    have hm_lc : Hex.DensePoly.leadingCoeff
        (Hex.ZPoly.toMonic core).monic = 1 := hm_monic
    have hvalid : ∀ i, (R.monicFactor.coeff i).natAbs ≤
        Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic :=
      fun i => defaultFactorCoeffBound_valid
        (Hex.ZPoly.toMonic core).monic hm_ne
        R.monicFactor R.monic_dvd i
    have hcl : Hex.centeredLiftPoly
        (liftedFactorProduct
          (Hex.ZPoly.toMonicLiftData core B primeData)
          hmem.choose_spec.choose)
        ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k) = R.monicFactor := by
      rw [← centeredLiftPoly_reduceModPow_absorb _ _ _
        (Hex.ZPoly.toMonicLiftData core B primeData).p_pos, R.congr]
      exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
        R.monicFactor _ _ _ hvalid hprecision_m
    have hlfp_monic : Hex.DensePoly.Monic
        (liftedFactorProduct
          (Hex.ZPoly.toMonicLiftData core B primeData)
          hmem.choose_spec.choose) :=
      liftedFactorProduct_monic _ _ (fun i _ => hmonic_i i)
    have hmf_monic :
        (HexPolyMathlib.toPolynomial R.monicFactor).Monic := by
      rw [← hcl]
      exact HexHenselMathlib.toPolynomial_monic_of_dense_monic _
        (monic_centeredLiftPoly_of_monic hlfp_monic (by omega))
    exact BHKS.supportShortVectorData_of_recoveredLift
      (recoveredLiftOfRecoveredAtLift
        hcore_lc_pos hcore_pos hprecision_m R)
      hm_lc hmf_monic
      (show (2 : Nat) ≤
          (Hex.ZPoly.toMonicLiftData core B primeData).p by
        rw [hp_eq]
        exact hp2)
      hk1 hsep_all hthr_all (fun i _ => hfac_all i)
  have hcut : BHKS.CutProjectionHypotheses
      (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData).p
          (Hex.ZPoly.toMonicLiftData core B primeData).k
          (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors) hrows)
      (liftedTrueSupports core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :=
    BHKS.cutProjectionHypotheses_of_shortVectors _ hrows hbasis _ data
  have hr :
      (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size ≤
        (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq]
    exact hval.factorCount_le_degree hm_monic
  have hp500 : (Hex.ZPoly.toMonicLiftData core B primeData).p ≤ 500 := by
    rw [hp_eq]
    exact Hex.choosePrimeData?_p_le_500
      (Hex.ZPoly.toMonic core).monic primeData hselected
  letI : Fact (1 <
      (Hex.ZPoly.toMonicLiftData core B primeData).p ^
        (Hex.ZPoly.toMonicLiftData core B primeData).k) := ⟨hk1⟩
  haveI : Nontrivial (ZMod
      ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
        (Hex.ZPoly.toMonicLiftData core B primeData).k)) := inferInstance
  have hdeg_le :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData),
        (HexPolyZMathlib.toPolynomial
          ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1)).natDegree ≤
          (HexPolyZMathlib.toPolynomial
            (Hex.ZPoly.toMonic core).monic).natDegree := by
    intro i
    let q := HexPolyZMathlib.toPolynomial
      (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)
    let h := HexPolyZMathlib.toPolynomial
      (liftedFactorProduct
        (Hex.ZPoly.toMonicLiftData core B primeData)
        ((Finset.univ : LiftedFactorSubset
          (Hex.ZPoly.toMonicLiftData core B primeData)) \ {i}))
    let m := HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic
    let φ := Int.castRingHom (ZMod
      ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
        (Hex.ZPoly.toMonicLiftData core B primeData).k))
    have hq_monic : q.Monic :=
      HexHenselMathlib.toPolynomial_monic_of_dense_monic _ (hmonic_i i)
    have hh_monic : h.Monic :=
      HexHenselMathlib.toPolynomial_monic_of_dense_monic _
        (liftedFactorProduct_monic _ _ (fun j _ => hmonic_i j))
    have hm_monic' : m.Monic :=
      HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hm_monic
    have hmap : m.map φ = q.map φ * h.map φ := by
      have hc := HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
        (Hex.ZPoly.toMonic core).monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i *
          liftedFactorProduct
            (Hex.ZPoly.toMonicLiftData core B primeData)
            ((Finset.univ : LiftedFactorSubset
              (Hex.ZPoly.toMonicLiftData core B primeData)) \ {i}))
        _ (hfac_complement i)
      simpa only [m, q, h, φ, HexPolyZMathlib.toPolynomial_mul,
        Polynomial.map_mul] using hc
    have hle : (q.map φ).natDegree ≤ (m.map φ).natDegree := by
      rw [hmap, (hq_monic.map φ).natDegree_mul (hh_monic.map φ)]
      omega
    have hgetD :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    rw [hgetD]
    calc
      q.natDegree = (q.map φ).natDegree :=
        (hq_monic.natDegree_map φ).symm
      _ ≤ (m.map φ).natDegree := hle
      _ = m.natDegree := hm_monic'.natDegree_map φ
  have hcop :
      ∀ i j : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData), j ≠ i →
        IsCoprime
          ((HexPolyZMathlib.toPolynomial
            ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
              i.val 1)).map
                (Int.castRingHom (ZMod
                  ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                    (Hex.ZPoly.toMonicLiftData core B primeData).k))))
          ((HexPolyZMathlib.toPolynomial
            ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
              j.val 1)).map
                (Int.castRingHom (ZMod
                  ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                    (Hex.ZPoly.toMonicLiftData core B primeData).k)))) := by
    intro i j hji
    have hi :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    have hj :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            j.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) j := by
      unfold liftedFactor
      simp [Array.getD, j.isLt]
    rw [hi, hj]
    exact toMonicLiftData_liftedFactors_isCoprime
      core B primeData hcore_lc_pos hcore_pos hval hprec_pos i j hji
  have hown :
      ∀ i : LiftedFactorIndex
          (Hex.ZPoly.toMonicLiftData core B primeData),
        IsCoprime
          ((HexPolyZMathlib.toPolynomial
            ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
              i.val 1)).map
                (Int.castRingHom (ZMod
                  ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                    (Hex.ZPoly.toMonicLiftData core B primeData).k))))
          ((HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod (Hex.ZPoly.toMonic core).monic
              ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
                i.val 1)
              (Hex.ZPoly.toMonicLiftData core B primeData).p
              (Hex.ZPoly.toMonicLiftData core B primeData).k)).map
                (Int.castRingHom (ZMod
                  ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                    (Hex.ZPoly.toMonicLiftData core B primeData).k)))) := by
    intro i
    have hi :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    rw [hi]
    exact toMonicLiftData_isCoprime_cldQuotient
      core B primeData hcore_lc_pos hcore_pos hval hprec_pos i
      (hmonic_i i) (by
        have h := hdeg_i i
        rwa [HexPolyMathlib.natDegree_toPolynomial] at h)
      (hfac_complement i)
  have hsupport :
      ∀ q : Polynomial ℤ,
        q.Monic → Irreducible q →
          q ∣ HexPolyZMathlib.toPolynomial (Hex.ZPoly.toMonic core).monic →
        ∃ S ∈ liftedTrueSupports core
            (Hex.ZPoly.toMonicLiftData core B primeData),
          ∀ i ∈ S,
            (HexPolyZMathlib.toPolynomial
              ((Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
                i.val 1)).map
                  (Int.castRingHom (ZMod
                    ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                      (Hex.ZPoly.toMonicLiftData core B primeData).k))) ∣
              q.map (Int.castRingHom (ZMod
                ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
                  (Hex.ZPoly.toMonicLiftData core B primeData).k))) := by
    intro q hqm hqi hqf
    obtain ⟨S, hS, hs⟩ :=
      toMonicLiftData_trueSupport_dvd core B primeData
        hcore_lc_pos hcore_pos hcore_prim hpartition hmonic_i
        hprecision_m q hqm hqi hqf
    refine ⟨S, hS, fun i hi => ?_⟩
    have hiD :
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.getD
            i.val 1 =
          liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i := by
      unfold liftedFactor
      simp [Array.getD, i.isLt]
    rw [hiD]
    exact hs i hi
  have hreverse :=
    bhksProjectedRowSpanInt_le_trueSupportSpanInt
      (Hex.ZPoly.toMonic core).monic
      (Hex.ZPoly.toMonicLiftData core B primeData).p
      (Hex.ZPoly.toMonicLiftData core B primeData).k
      (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors
      (liftedTrueSupports core
        (Hex.ZPoly.toMonicLiftData core B primeData))
      hm_ne hm_pos hm_monic
      (by rw [hp_eq]; exact hp2) hp500 hr hk1 hprecision
      (fun j => hthr_all j.val)
      hrows hbasis
      (liftedTrueSupports.cover_of_partition hpartition)
      (liftedTrueSupports.eq_of_mem_inter_of_partition hpartition)
      (liftedTrueSupports.nonempty_of_partition hpartition
        hcore_ne hcore_prim hcore_lc_pos hprecision_core)
      data hfac_all hdeg_le hcop hown hsupport
  exact le_antisymm hreverse
    (BHKS.trueSupportSpanInt_le_projectedRowSpanInt _ _ hcut)

/-- At the public precision cap, successful monic prime selection makes the
lattice core tier total: exact projected span either reconstructs two or more
canonical factors on the scheduled cap visit, or yields the single all-ones
certificate. -/
theorem latticeCoreFactorsWithBound_ne_none_of_toMonicPrimeData
    (f : Hex.ZPoly) (hf : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hselected :
      Hex.ZPoly.toMonicPrimeData?
          (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdeg_ne :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0) :
    Hex.latticeCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.latticePrecisionCap f) primeData ≠ none := by
  classical
  let core := (Hex.normalizeForFactor f).squareFreeCore
  let B := Hex.latticePrecisionCap f
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core := by
    simpa only [core] using
      (Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf)
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_pos : 0 < core.degree?.getD 0 := by
    simpa only [core] using Nat.pos_of_ne_zero hdeg_ne
  have hcore_prim : Hex.ZPoly.Primitive core := by
    simpa only [core] using
      (IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero
        f hf)
  have hcore_sqfree :
      Squarefree (HexPolyZMathlib.toPolynomial core) := by
    simpa only [core] using
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
        f hf)
  have hval :=
    modPFactorization_of_toMonicPrimeData
      (by simpa only [core] using hselected) hcore_lc_pos hcore_pos
  have hp2 : 2 ≤ primeData.p := hval.prime.two_le
  have hB_floor : Hex.bhksRecoveryFloor core ≤ B := by
    simpa only [core, B] using
      (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f)
  have hB_ne : B ≠ 0 := by
    have hbound_pos :=
      Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
    have hbound_le := Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
    omega
  have hp_eq : d.p = primeData.p := by
    dsimp only [d]
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_p _ _ _
  have hk_eq :
      d.k = Hex.precisionForCoeffBound B primeData.p := by
    dsimp only [d]
    unfold Hex.ZPoly.toMonicLiftData
    exact Hex.henselLiftData_k _ _ _
  have hprec_spec :
      2 * B <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hprec_pos :
      1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero :
        Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hprec_spec
    omega
  have hprecision_core :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k := by
    have hle : Hex.ZPoly.defaultFactorCoeffBound core ≤ B := by
      simpa only [core, B] using
        (Hex.defaultFactorCoeffBound_squareFreeCore_le_latticePrecisionCap f)
    rw [hp_eq, hk_eq]
    omega
  have hprecision_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound
          (Hex.ZPoly.toMonic core).monic < d.p ^ d.k := by
    have hle :
        Hex.ZPoly.defaultFactorCoeffBound
            (Hex.ZPoly.toMonic core).monic ≤ B := by
      simpa only [core, B] using
        (Hex.defaultFactorCoeffBound_toMonic_squareFreeCore_le_latticePrecisionCap
          f)
    rw [hp_eq, hk_eq]
    omega
  have hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core := by
    apply liftedFactorSubsetPartition_of_toMonicModP
      core B primeData hval hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hB_ne
    rw [← hk_eq, ← hp_eq]
    exact hprecision_monic
  have hmonic_i :
      ∀ i : LiftedFactorIndex d,
        Hex.DensePoly.Monic (liftedFactor d i) := by
    exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos hval hprec_pos
  have hrows :
      1 ≤
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          d.p d.k d.liftedFactors).factorCount +
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
          d.p d.k d.liftedFactors).coeffWidth := by
    change 1 ≤ d.liftedFactors.size +
      (Hex.ZPoly.toMonic core).monic.degree?.getD 0
    rw [Hex.ZPoly.toMonic_monic_degree_getD]
    omega
  have hprecision_bhks :
      2 * Hex.bhksBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k := by
    rw [hp_eq]
    simpa only [core, B, d] using
      (Hex.two_mul_bhksBound_toMonic_squareFreeCore_lt_pow_cap
        f primeData hp2)
  have hspan :
      BHKS.projectedRowSpanInt
          (Hex.bhksProjectedRows
            (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
              d.p d.k d.liftedFactors) hrows) =
        BHKS.trueSupportSpanInt (liftedTrueSupports core d) := by
    exact bhksProjectedSpan_eq_trueSupportSpan
      core B primeData (by simpa only [core] using hselected)
      hcore_lc_pos hcore_pos hcore_prim hcore_sqfree hB_floor hB_ne
      hprecision_bhks hrows
  let classes :=
    BHKS.supportPartitionByMinColumn (liftedTrueSupports core d)
  have hclasses_pos : 0 < classes.length := by
    have hlen :=
      BHKS.supportPartitionByMinColumn_length_eq_normalizedFactors_card
        hpartition hcore_ne hcore_prim hcore_lc_pos hprecision_core
    have hpoly_ne : HexPolyZMathlib.toPolynomial core ≠ 0 := by
      intro hzero
      apply hcore_ne
      apply HexPolyZMathlib.equiv.injective
      simpa using hzero
    have hpoly_degree :
        0 < (HexPolyZMathlib.toPolynomial core).natDegree := by
      rw [HexPolyMathlib.natDegree_toPolynomial]
      exact hcore_pos
    have hnonunit :
        ¬IsUnit (HexPolyZMathlib.toPolynomial core) :=
      not_isUnit_of_natDegree_pos_of_isReduced _ hpoly_degree
    have hfactor_pos :
        0 < (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card := by
      exact Multiset.card_pos.mpr
        ((UniqueFactorizationMonoid.normalizedFactors_pos _ hpoly_ne).mpr
          hnonunit).ne'
    dsimp only [classes]
    rw [hlen]
    exact hfactor_pos
  rw [Hex.latticeCoreFactorsWithBound]
  by_cases hsmall : primeData.factorsModP.size ≤ 1
  · rw [if_pos hsmall]
    simp
  · rw [if_neg hsmall]
    cases hlattice :
        Hex.latticeCoreWithBound core B primeData
          (Hex.initialHenselPrecision B)
          (Hex.ZPoly.quadraticDoublingSteps B + 2) with
    | some factors =>
        simp
    | none =>
        by_cases hsingle : classes.length = 1
        · have hallones :
              Hex.bhksSingleAllOnesPartition core d = true :=
            BHKS.bhksSingleAllOnesPartition_eq_true_of_span_eq
              hcore_ne hcore_prim hcore_lc_pos hprecision_core
              hpartition hrows hspan
              (by simpa only [classes] using hsingle)
          rw [Hex.bhksRecoveryFloorGate_eq, if_pos hB_floor]
          rw [show Hex.ZPoly.toMonicLiftData core B primeData = d by rfl,
            if_pos hallones]
          simp
        · have hclasses_two : 2 ≤ classes.length := by omega
          have hrecover :
              Hex.bhksRecover? core d =
                some (BHKS.recoveredClassFactors core d
                  (liftedTrueSupports core d)) :=
            BHKS.bhksRecover_eq_some_of_span_eq
              hcore_ne hcore_pos hcore_prim hcore_lc_pos hmonic_i
              hprecision_core hprecision_monic hpartition hrows hspan
              (by simpa only [classes] using hclasses_two)
          have hloop_ne :
              Hex.latticeCoreWithBound core B primeData
                  (Hex.initialHenselPrecision B)
                  (Hex.ZPoly.quadraticDoublingSteps B + 2) ≠ none :=
            Hex.latticeCoreWithBound_ne_none_of_recovery_on_schedule
              core B primeData hB_floor
              (Hex.cap_mem_henselPrecisionSchedule B)
              (by simpa only [d] using hrecover)
          exact absurd hlattice hloop_ne

/-!
# Top-down attack on the deep BHKS content

The two remaining obligations of
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks`
are stated below as explicit lemmas and then supplied to give the
**unconditional** lattice-tier irreducibility theorem
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`.

Both lemmas are the deep van Hoeij / CLD content, proved on the **proven** LLL
short-vector path through the `W ⊆ L'` assembly above: the count lower bound
`normalizedFactors_card_le_bhksEquivalenceClassIndicators_size` supplies the
arm-2 `≥` half (the `≤` half is the proven UFD partition bound) and, combined
with reducibility, the arm-3 `≥ 2`-classes contradiction.
-/

/--
**Arm-2 deep obligation (BHKS CLD count-equality).**  When the CLD recovery
`bhksRecoveryCoreWithBound` splits `core`, the number of emitted factors equals the
number of irreducible factors of `core` over `ℤ` — the count-equality that turns
the fast-core coverage into per-factor irreducibility.

The `≤` half is the proven UFD partition bound
(`bhksRecoveryCoreWithBound_some_factor_count_le`); the `≥` half is the van Hoeij
`W ⊆ L'` adequacy: the acceptance gate guarantees the witness precision clears
the fast-core floor, so every true-factor support survives the LLL/Gram-Schmidt
cut as a distinct equivalence class, and one verified candidate is emitted per
class (`bhksIndicatorCandidates?_size_eq`).
-/
theorem bhksRecoveryCoreWithBound_some_factor_count_eq
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hfast : Hex.bhksRecoveryCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        = some coreFactors) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore)).card := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_prim : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core) :=
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf_ne
  -- the ≤ half: the emitted factors are nonunit divisors with product `core`
  have hle := bhksRecoveryCoreWithBound_some_factor_count_le hcore_ne hfast
  -- the ≥ half through the recovery-data extractor at the gated witness precision
  obtain ⟨k', hrows, hcand, _hdegen, _hprod, hfloor⟩ :=
    Hex.bhksRecoveryCoreWithBound_some_indicatorCandidates hfast
  have hk_ne : k' ≠ 0 := by
    have hpos := Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
    have hfl := Hex.defaultFactorCoeffBound_le_bhksRecoveryFloor core
    omega
  have hsize := Hex.bhksIndicatorCandidates?_size_eq hcand
  have hge := normalizedFactors_card_le_bhksEquivalenceClassIndicators_size
    core k' primeData hselected hcore_lc_pos (Nat.pos_of_ne_zero hdeg_ne)
    hcore_prim hcore_sqfree hfloor hk_ne rfl hrows
  rw [List.length_map, Array.length_toList] at hle ⊢
  omega

/--
**Arm-3 deep obligation (van Hoeij single-all-ones adequacy).**  At adequate
precision (`hB_floor`: the coefficient bound clears the fast-core acceptance
floor, hence the CLD column separation and both Mignotte recovery bounds), a
single all-ones equivalence class of the CLD knapsack lattice certifies that
`core` lands on exactly the minimal subsets (`L = W` with `W = ⟨(1,…,1)⟩`),
hence `core` is irreducible.  This is the deep adequacy theorem (Klüners
Thm 3), proved on the proven LLL short-vector path: were `core` reducible, its
≥ 2 true-factor supports would survive the cut as ≥ 2 distinct equivalence
classes, contradicting the single class.

The precision hypothesis is essential, not incidental: at precision below the
separation threshold the lattice may not have separated the modular factors,
so `bhksSingleAllOnesPartition` could report `true` on a *reducible* core.
The `factorLattice` call site supplies adequate precision via
`latticePrecisionCap`, which contains the floor by construction.
-/
theorem squareFreeCore_irreducible_of_bhksSingleAllOnes
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_floor : Hex.bhksRecoveryFloor (Hex.normalizeForFactor f).squareFreeCore ≤ B)
    (hB_ne : B ≠ 0)
    (hbhks : Hex.bhksSingleAllOnesPartition (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore B primeData)
        = true) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_prim : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core) :=
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf_ne
  rw [Hex.ZPoly.Irreducible_iff_polynomialIrreducible]
  -- The van Hoeij adequacy collapses to a factor count: at precision above the
  -- BHKS separation threshold, a single all-ones equivalence class means `core`
  -- has exactly one irreducible factor over ℤ.  This is the deep arm-3 heart
  -- (the L1–L9 chain of `progress/PLAN-arm3-dag.md`); expanded next.
  have hcard : (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card = 1 := by
    -- `core` is a nonzero non-unit, so it has at least one irreducible factor.
    -- Easy `UniqueFactorizationMonoid` bookkeeping; deferred per hardest-first.
    have hge : 1 ≤ (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
      have hpos : 0 < (HexPolyZMathlib.toPolynomial core).natDegree := by
        rw [HexPolyMathlib.natDegree_toPolynomial core]; exact Nat.pos_of_ne_zero hdeg_ne
      have hne : HexPolyZMathlib.toPolynomial core ≠ 0 := by
        intro h; rw [h, Polynomial.natDegree_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      have hnu : ¬ IsUnit (HexPolyZMathlib.toPolynomial core) :=
        not_isUnit_of_natDegree_pos_of_isReduced _ hpos
      exact Multiset.card_pos.mpr
        ((UniqueFactorizationMonoid.normalizedFactors_pos _ hne).mpr hnu).ne'
    -- The deep van Hoeij adequacy: `core` has AT MOST one irreducible factor.
    -- Contrapositive: if `core` had ≥ 2 irreducible factors it would factor as a
    -- proper product, yielding a proper nonempty true-factor support, hence a
    -- short lattice vector, hence rank ≥ 2 in the LLL-reduced cut, contradicting
    -- the single all-ones equivalence class `hbhks`.  This is the L5–L10 chain.
    have hle : (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card := Nat.lt_of_not_le hgt
      -- The concrete lattice adequacy (the L5–L10 heart): if `core` has ≥ 2
      -- irreducible factors then a proper factor's support gives a short lattice
      -- vector making the LLL-reduced cut rank ≥ 2, so the equivalence-class
      -- computation does NOT collapse to a single all-ones class.
      have hfalse : Hex.bhksSingleAllOnesPartition core
          (Hex.ZPoly.toMonicLiftData core B primeData) = false := by
        set d := Hex.ZPoly.toMonicLiftData core B primeData with hd
        rw [Hex.bhksSingleAllOnesPartition]
        set L := Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic d.p d.k d.liftedFactors
          with hL
        by_cases hrows : 1 ≤ L.factorCount + L.coeffWidth
        · rw [dif_pos hrows]
          -- **Adequacy (the van Hoeij heart, #8417):** the CLD lattice never
          -- under-separates — a `core` with ≥ 2 irreducible factors yields ≥ 2
          -- equivalence classes (each true-factor support is a short lattice
          -- vector captured in the LLL-reduced Gram-Schmidt cut, giving a
          -- distinct class).  Proved on the proven LLL short-vector path.
          have hclasses : 2 ≤ (Hex.bhksEquivalenceClassIndicators
              (Hex.bhksProjectedRows L hrows)).size := by
            have hL' : L = Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
                (Hex.ZPoly.toMonicLiftData core B primeData).p
                (Hex.ZPoly.toMonicLiftData core B primeData).k
                (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors := by
              rw [hL, hd]
            have hge := normalizedFactors_card_le_bhksEquivalenceClassIndicators_size
              core B primeData hselected hcore_lc_pos (Nat.pos_of_ne_zero hdeg_ne)
              hcore_prim hcore_sqfree hB_floor hB_ne hL' hrows
            omega
          -- With ≥ 2 classes the `indicators.size == 1` conjunct is false, so the
          -- whole all-ones Bool is false.
          have hne1 : ((Hex.bhksEquivalenceClassIndicators
              (Hex.bhksProjectedRows L hrows)).size == 1) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega
          simp only [hne1, Bool.and_false, Bool.false_and]
        · rw [dif_neg hrows]
      rw [hfalse] at hbhks
      exact absurd hbhks (by simp)
    omega
  -- Exactly one normalized factor means `core` is associated to an irreducible,
  -- hence irreducible.
  obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hcard
  have hne : HexPolyZMathlib.toPolynomial core ≠ 0 := by
    have hpos : 0 < (HexPolyZMathlib.toPolynomial core).natDegree := by
      rw [HexPolyMathlib.natDegree_toPolynomial core]; exact Nat.pos_of_ne_zero hdeg_ne
    intro h; rw [h, Polynomial.natDegree_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  have hp_irr : Irreducible p :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p
      (by rw [hp]; exact Multiset.mem_singleton_self p)
  have hassoc : Associated p (HexPolyZMathlib.toPolynomial core) := by
    have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hne
    rwa [hp, Multiset.prod_singleton] at hprod
  exact hassoc.irreducible_iff.mp hp_irr

/-- Every factor the
van Hoeij CLD lattice tier `latticeCoreFactorsWithBound` returns for the
square-free core of `normalizeForFactor f` is irreducible over `ℤ`, provided the
precision clears the fast-core acceptance floor (`hB_floor`).  Arm 1 (small-mod
singleton) is proved directly; arms 2/3 are the deep CLD obligations
`bhksRecoveryCoreWithBound_some_factor_count_eq` /
`squareFreeCore_irreducible_of_bhksSingleAllOnes`.  The
`factorLattice` call site supplies `hB_floor` via `latticePrecisionCap`.
-/
theorem latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_floor : Hex.bhksRecoveryFloor (Hex.normalizeForFactor f).squareFreeCore ≤ B)
    (hB_ne : B ≠ 0)
    {cf : Array Hex.ZPoly}
    (hlattice : Hex.latticeCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore B primeData = some cf) :
    ∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g :=
  latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks
    f hf_ne B primeData hselected hdeg_ne hB_floor hB_ne hlattice
    (bhksRecoveryCoreWithBound_some_factor_count_eq
      f hf_ne B primeData hselected hdeg_ne)
    (fun B' hB'_floor hB'_ne hbhks =>
      squareFreeCore_irreducible_of_bhksSingleAllOnes
        f hf_ne B' primeData hselected hdeg_ne
        hB'_floor hB'_ne hbhks)
/-!
# Lattice-branch assembly

The raw lattice-factor irreducibility theorem lives here because it consumes
the LLL-backed `LatticeTier` core lemma. Its hybrid assembly is in the same
module, and `FactorSoundness` consumes that assembly for the public
factorization theorem.
-/

/-- **Lattice-core reassembly completeness.** When the lattice tier
returns core factors for the square-free core of `normalizeForFactor f` at
adequate precision, the reassembly is expansion-complete.  The lattice analog of
`reassemblyExpansionComplete_classicalCore_of_ne_zero`: it composes the
`LatticeTier` core irreducibility lemma
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`, the
polyProduct / normalizeFactorSign / degree-positivity structural companions
`Hex.latticeCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`,
and the sign-normalized expansion-complete surface
`reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm`.
Consumed by the lattice residual arm of
`factorLatticeFactorsWithBound_factor_irreducible`.

The core irreducibility input is supplied by
`bhksRecoveryCoreWithBound_some_factor_count_eq` and
`squareFreeCore_irreducible_of_bhksSingleAllOnes`; the reassembly side introduces no
additional assumption. -/
theorem reassemblyExpansionComplete_latticeCore_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hB_floor : Hex.bhksRecoveryFloor (Hex.normalizeForFactor f).squareFreeCore ≤ B)
    (hB_ne : B ≠ 0)
    {cf : Array Hex.ZPoly}
    (hlattice : Hex.latticeCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore B primeData = some cf) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) cf := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_deg : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
    Nat.pos_of_ne_zero hdeg_ne
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
    f hf cf
    (latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
      f hf B primeData hselected hdeg_ne hB_floor hB_ne hlattice)
    (Hex.latticeCoreFactorsWithBound_polyProduct _ _ _ hlattice)
    (Hex.latticeCoreFactorsWithBound_normalizeFactorSign _ _ _ hcore_pos hlattice)
    (Hex.latticeCoreFactorsWithBound_degree_pos _ _ _ hcore_deg hlattice)

/-- **Lattice-branch raw-factor irreducibility.** Every raw factor of the
CLD lattice tier's output that passes the recorded-factor filter is irreducible.
Reduces through the reassembly bridge to the `LatticeTier` core lemma. -/
theorem factorLatticeFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {cf : Array Hex.ZPoly}
    (hcf : Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) = some cf)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ cf.toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim := IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  rw [Hex.factorLatticeFactorsWithBound] at hcf
  by_cases hdeg0 : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · -- Constant square-free core: X-power factors are irreducible; the core is the
    -- unit `1` (excluded by the recorded-factor filter `hrec`).
    rw [if_pos hdeg0] at hcf
    obtain rfl := Option.some.inj hcf
    have hcomplete := Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg0
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core : raw = (Hex.normalizeForFactor f).squareFreeCore := by simpa using hcore
        rw [hraw_core, Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg0]
      rw [hraw_one, Hex.normalizeFactorSign_one, Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg0] at hcf
    by_cases hB0 : Hex.latticePrecisionCap f = 0
    · rw [if_pos hB0] at hcf; exact absurd hcf.symm (Option.some_ne_none cf)
    · rw [if_neg hB0] at hcf
      cases hquad : Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
        -- Quadratic integer-root split: the roots are linear factors, irreducible.
        simp only [hquad] at hcf
        obtain rfl := Option.some.inj hcf
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
        · intro factor hfmem
          exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
            hcore_pos hcore_prim hquad hfmem
      | none =>
        rw [hquad] at hcf
        cases hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore with
        | none => rw [hselected] at hcf; exact absurd hcf.symm (Option.some_ne_none cf)
        | some primeData =>
          rw [hselected] at hcf
          rw [Option.map_eq_some_iff] at hcf
          obtain ⟨coreFactors, hcore_lattice, rfl⟩ := hcf
          refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
            (Hex.normalizeForFactor f) coreFactors ?_ ?_ hmem
          · exact reassemblyExpansionComplete_latticeCore_of_ne_zero
              f hf (Hex.latticePrecisionCap f) primeData hselected hdeg0
              (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f) hB0
              hcore_lattice
          · exact latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
              f hf (Hex.latticePrecisionCap f) primeData hselected hdeg0
              (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f) hB0
              hcore_lattice

/-- **Hybrid raw-factor irreducibility assembly.**  Every raw factor of
`factorFactors f` passing the recorded-factor filter is irreducible,
dispatched over the classical / lattice / trial tiers. -/
theorem factorFactors_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorFactors f).toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  rcases Hex.factorFactors_mem_source f hmem with
    ⟨cf, hcf, hraw⟩ | ⟨cf, hcf, hraw⟩ | htrial
  · exact factorClassicalFactorsWithBound_factor_irreducible f hf hcf hraw hrec
  · exact factorLatticeFactorsWithBound_factor_irreducible f hf hcf hraw hrec
  · exact factorTrialFactorsWithBound_factor_irreducible f hf htrial hrec

end

end HexBerlekampZassenhausMathlib
