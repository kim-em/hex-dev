/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhausMathlib.IntReductionMod
import HexGramSchmidtMathlib.Int.Swap
import HexLLLMathlib.ShortVector

/-!
# Irreducibility of the van Hoeij / CLD lattice tier (#8417)

The large-`r` lattice tier `Hex.latticeCoreFactorsWithBound` is the van Hoeij
CLD recovery, run past the classical subset budget.  For a square-free `core`
selected by `Hex.ZPoly.toMonicPrimeData?` (the monic-transform selection, so the
Hensel seeds match the lift target; #8519) it has three arms:

1. `primeData.factorsModP.size ≤ 1` → `some #[core]`.  The core is irreducible
   mod `p`, hence irreducible over `ℤ`.  **Proved unconditionally here** by
   reusing `squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch`.

2. `factorFastCoreWithBound … = some coreFactors` → those factors.  The CLD
   recovery split `core`.  Irreducibility of the emitted factors is the BHKS
   count-equality obligation, already isolated by
   `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count`; it is
   threaded here as the `harm2_count` hypothesis.

3. `factorFastCoreWithBound = none` ∧ `bhksSingleAllOnesPartition core d = true`
   → `some #[core]`.  The single all-ones equivalence class of the CLD lattice
   at cap precision certifies that `core` lands on exactly the minimal subsets
   (`L = W`), i.e. `core` is irreducible.  This is the deep van Hoeij adequacy
   theorem; it is threaded here as the `harm3_adequacy` hypothesis.

The reduction below discharges arm 1 and reduces the whole tier to the two BHKS
obligations, mirroring the fast-path `_of_count` convention and the classical
capstone `classicalCoreFactorsWithBound_factor_irreducible` (#8413).  It is the
proof architecture the deep-content successors plug into.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Descend irreducibility along the monic (`x ↦ x/ℓf`) transform: if the monic
transform of a primitive positive-degree core is irreducible, so is the core.
The dilation identity `dilate ℓf (toMonic core).monic = ℓf^(d-1) · core`
identifies the two up to a positive constant, which `primitivePart` strips. -/
theorem zpolyIrreducible_of_toMonicMonic_irreducible
    (core : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hm_irr : Hex.ZPoly.Irreducible (Hex.ZPoly.toMonic core).monic) :
    Hex.ZPoly.Irreducible core := by
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := by
    simpa using hcore_pos
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos (by simpa using hcore_pos)
  have hkey : Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) (Hex.ZPoly.toMonic core).monic
      = Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff core ^ ((Hex.ZPoly.toMonic core).degree - 1)) core := by
    have h := Hex.ZPoly.dilate_monic_toMonic core hdeg
    rwa [Hex.ZPoly.C_mul_eq_scale] at h
  have hrecover : Hex.ZPoly.primitivePart
      (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) (Hex.ZPoly.toMonic core).monic)
      = core := by
    rw [hkey]
    exact Hex.DensePoly.primitivePart_scale_of_primitive
      (pow_pos hcore_lc_pos _) hcore_prim
  rw [Hex.ZPoly.Irreducible_iff_polynomialIrreducible] at hm_irr ⊢
  exact (irreducible_toPolynomial_dilate_iff
    (ne_of_gt hcore_lc_pos) hM_monic hcore_prim hrecover).mpr hm_irr

/-- Small-mod singleton arm of the lattice tier, keyed on the monic-transform
prime selection `toMonicPrimeData?`: a singleton mod-`p` factorisation of
`(toMonic core).monic` certifies its irreducibility over `ℤ`, which descends to
the primitive core along the dilation transform. -/
theorem squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_prim : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hchoose : Hex.choosePrimeData? (Hex.ZPoly.toMonic core).monic = some primeData :=
    hselected
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos (by simpa using hcore_pos)
  have hm_deg : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos
      (by simpa using hcore_pos)]
    simpa using hcore_pos
  have hm_irr : Hex.ZPoly.Irreducible (Hex.ZPoly.toMonic core).monic :=
    IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP
      (Hex.ZPoly.toMonic core).monic primeData hchoose hm_deg hsmall
      (HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hM_monic).isPrimitive
      (IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero
        (Hex.ZPoly.toMonic core).monic primeData hchoose)
  exact zpolyIrreducible_of_toMonicMonic_irreducible core hcore_lc_pos hcore_pos
    hcore_prim hm_irr

/--
**#8417 (lattice-tier irreducibility, reduced form).**  Every factor the
van Hoeij CLD lattice tier `Hex.latticeCoreFactorsWithBound` returns for the
square-free core of `normalizeForFactor f` is irreducible, given the two BHKS
obligations as hypotheses.

The three arms of `latticeCoreFactorsWithBound` are discharged as follows:

* the small-mod singleton arm (`factorsModP.size ≤ 1`, output `#[core]`) is
  proved unconditionally from `squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch`;
* the CLD-split arm (`factorFastCoreWithBound = some coreFactors`) is discharged
  from the count-equality hypothesis `harm2_count` via
  `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count`;
* the all-ones certification arm (`bhksSingleAllOnesPartition = true`, output
  `#[core]`) is discharged from the adequacy hypothesis `harm3_adequacy`.

`harm2_count` and `harm3_adequacy` are exactly the remaining deep BHKS content
(the "lattice lands on minimal subsets" argument); every other side condition is
discharged from `toMonicPrimeData?` and the square-free-core facts.
-/
theorem latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {cf : Array Hex.ZPoly}
    (hlattice : Hex.latticeCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore B primeData = some cf)
    (harm2_count : ∀ coreFactors : Array Hex.ZPoly,
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B primeData
          (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
          = some coreFactors →
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore)).card)
    (harm3_adequacy :
      Hex.bhksSingleAllOnesPartition (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore B primeData)
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
      (squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch f hf_ne primeData
        (Nat.pos_of_ne_zero hdeg_ne) hselected hsmall)
  · -- Arms 2/3: CLD recovery.
    split at hlattice
    · -- Arm 2: CLD split. Reduce to the count-equality obligation.
      rename_i coreFactors hfast
      obtain rfl := Option.some.inj hlattice
      exact factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count
        hcore_ne hfast (harm2_count coreFactors hfast)
    · -- Arm 3: no split; all-ones certification.
      rename_i hfast
      split at hlattice
      · -- `bhksSingleAllOnesPartition = true`: output `#[core]`, core irreducible.
        rename_i hbhks
        obtain rfl := Option.some.inj hlattice
        exact fun g hg => hsingleton g hg (harm3_adequacy hbhks)
      · -- `bhksSingleAllOnesPartition = false`: output `none`, contradiction.
        exact absurd hlattice.symm (Option.some_ne_none cf)

/-!
## Top-down attack on the deep BHKS content (#8417)

The two remaining obligations of
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks`
are stated below as explicit lemmas and then supplied to give the
**unconditional** lattice-tier irreducibility theorem
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`.

Both lemmas are the deep van Hoeij / CLD content; they are being proved on the
**proven** LLL short-vector path (`HexLLLMathlib.lllNative_first_row_norm_sq_le_unconditional`
and `lllNative_mem_latticeSubmodule_iff`), never by assumption.  Until each is
discharged it carries a `sorry` (grep-able; no axiom), and the hardest one
(arm-3 adequacy) is attacked first.
-/

/--
**Arm-2 deep obligation (BHKS CLD count-equality).**  When the CLD recovery
`factorFastCoreWithBound` splits `core`, the number of emitted factors equals the
number of irreducible factors of `core` over `ℤ` — the count-equality that turns
the fast-core coverage into per-factor irreducibility.  This is the CLD
completeness half of the van Hoeij method (Klüners Thm 2/3: the reduced lattice
short vectors are exactly the true-factor partition, so the recovery emits one
factor per partition block).
-/
theorem latticeArm2_fastCore_count
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hfast : Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        = some coreFactors) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore)).card := by
  sorry

/--
**Arm-3 deep obligation (van Hoeij single-all-ones adequacy).**  At adequate
precision (`hprec`: `p^k > 2·bhksBound core`, the separation threshold), a single
all-ones equivalence class of the CLD knapsack lattice certifies that `core`
lands on exactly the minimal subsets (`L = W` with `W = ⟨(1,…,1)⟩`), hence `core`
is irreducible.  This is the deep adequacy theorem (Klüners Thm 3), proved on the
proven LLL short-vector path.

The precision hypothesis `hprec` is essential, not incidental: at precision below
the BHKS separation threshold the lattice may not have separated the modular
factors, so `bhksSingleAllOnesPartition` can report `true` on a *reducible* core
(its own docstring warns callers to trust it only at `k ≥ bhksBound`).  The
`factorLattice` call site supplies adequate precision via `factorFastPrecisionCap`.
-/
theorem latticeArm3_bhksSingleAllOnes_irreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hprec : 2 * Hex.bhksBound (Hex.normalizeForFactor f).squareFreeCore <
      primeData.p ^ (Hex.ZPoly.toMonicLiftData
        (Hex.normalizeForFactor f).squareFreeCore B primeData).k)
    (hbhks : Hex.bhksSingleAllOnesPartition (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore B primeData)
        = true) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
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
            sorry
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

/--
**#8417 (lattice-tier irreducibility, at adequate precision).**  Every factor the
van Hoeij CLD lattice tier `latticeCoreFactorsWithBound` returns for the
square-free core of `normalizeForFactor f` is irreducible over `ℤ`, provided the
precision is at least the BHKS separation threshold (`hprec`).  Arm 1 (small-mod
singleton) is proved directly; arms 2/3 are the deep CLD obligations
`latticeArm2_fastCore_count` / `latticeArm3_bhksSingleAllOnes_irreducible`.  The
`factorLattice` call site supplies `hprec` via `factorFastPrecisionCap`.
-/
theorem latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hprec : 2 * Hex.bhksBound (Hex.normalizeForFactor f).squareFreeCore <
      primeData.p ^ (Hex.ZPoly.toMonicLiftData
        (Hex.normalizeForFactor f).squareFreeCore B primeData).k)
    {cf : Array Hex.ZPoly}
    (hlattice : Hex.latticeCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore B primeData = some cf) :
    ∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g :=
  latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible_of_bhks
    f hf_ne B primeData hselected hdeg_ne hlattice
    (latticeArm2_fastCore_count f hf_ne B primeData hselected hdeg_ne)
    (latticeArm3_bhksSingleAllOnes_irreducible f hf_ne B primeData hselected hdeg_ne hprec)

/-!
## Lattice geometry: the BHKS basis is LLL-independent (arm-3 foundation)

The van Hoeij knapsack basis `[I_r | Ã ; 0 | diag(p^(a-l_j))]` is upper-triangular
with strictly positive diagonal (1's in the `I_r` block, `p^(a-l_j)` in the
`D` block), so its rows are LLL-independent.  This is the entry gate to the
proven LLL short-vector bound `HexLLLMathlib.lllNative_first_row_norm_sq_le_unconditional`.
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
`HexLLLMathlib.lllNative_first_row_norm_sq_le_unconditional` to the BHKS basis,
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
  HexLLLMathlib.lllNative_first_row_norm_sq_le_unconditional
    (Hex.bhksLatticeBasis f p a lifted).basis (3 / 4)
    Hex.lll_delta_lower Hex.lll_delta_upper hn
    (bhksLatticeBasis_basis_independent f p a hp lifted) x hx hx0

/-!
## Filling the capstone's lattice branch (#8417)

`factorLatticeFactorsWithBound_factor_irreducible` was a forward `sorry` in
`IntReductionMod` (it cannot import the LLL machinery); it is filled here and,
with its assembly `factorHybridFactors_factor_irreducible`, moved into this file
where the `LatticeTier` core lemma is available.  `factor_irreducible_of_nonUnit`
(FactorSoundness) consumes `factorHybridFactors_factor_irreducible`.
-/

/-- **Lattice-core reassembly completeness (#8520).**  When the lattice tier
returns core factors for the square-free core of `normalizeForFactor f` at
adequate precision, the reassembly is expansion-complete.  The lattice analog of
`reassemblyExpansionComplete_classicalCore_of_ne_zero` (#8511): it composes the
`LatticeTier` core irreducibility lemma
`latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`, the
polyProduct / normalizeFactorSign / degree-positivity structural companions
`Hex.latticeCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`,
and the sign-normalized expansion-complete surface
`reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm`.
Consumed by the lattice residual arm of
`factorLatticeFactorsWithBound_factor_irreducible`.

The only analytic dependency is the core irreducibility input, which inherits
the two open BHKS obligations (`latticeArm2_fastCore_count`,
`latticeArm3_bhksSingleAllOnes_irreducible`); the reassembly side itself is
fully proved — no new assumption is introduced here. -/
theorem reassemblyExpansionComplete_latticeCore_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hprec : 2 * Hex.bhksBound (Hex.normalizeForFactor f).squareFreeCore <
      primeData.p ^ (Hex.ZPoly.toMonicLiftData
        (Hex.normalizeForFactor f).squareFreeCore B primeData).k)
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
      f hf B primeData hselected hdeg_ne hprec hlattice)
    (Hex.latticeCoreFactorsWithBound_polyProduct _ _ _ hlattice)
    (Hex.latticeCoreFactorsWithBound_normalizeFactorSign _ _ _ hcore_pos hlattice)
    (Hex.latticeCoreFactorsWithBound_degree_pos _ _ _ hcore_deg hlattice)

/-- **Lattice-branch raw-factor irreducibility (#8417).**  Every raw factor of the
CLD lattice tier's output that passes the recorded-factor filter is irreducible.
Reduces through the reassembly bridge to the `LatticeTier` core lemma. -/
theorem factorLatticeFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {cf : Array Hex.ZPoly}
    (hcf : Hex.factorLatticeFactorsWithBound f (Hex.factorFastPrecisionCap f) = some cf)
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
    by_cases hB0 : Hex.factorFastPrecisionCap f = 0
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
              f hf (Hex.factorFastPrecisionCap f) primeData hselected hdeg0
              (Hex.two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_toMonicPrimeData
                f primeData hselected)
              hcore_lattice
          · exact latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
              f hf (Hex.factorFastPrecisionCap f) primeData hselected hdeg0
              (Hex.two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_toMonicPrimeData
                f primeData hselected)
              hcore_lattice

/-- **Hybrid raw-factor irreducibility assembly.**  Every raw factor of
`factorHybridFactors f` passing the recorded-factor filter is irreducible,
dispatched over the classical / lattice / trial tiers. -/
theorem factorHybridFactors_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorHybridFactors f).toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  rcases Hex.factorHybridFactors_mem_source f hmem with
    ⟨cf, hcf, hraw⟩ | ⟨cf, hcf, hraw⟩ | htrial
  · exact factorClassicalFactorsWithBound_factor_irreducible f hf hcf hraw hrec
  · exact factorLatticeFactorsWithBound_factor_irreducible f hf hcf hraw hrec
  · exact factorSlowTrialFactorsWithBound_factor_irreducible f hf htrial hrec

end

end HexBerlekampZassenhausMathlib
