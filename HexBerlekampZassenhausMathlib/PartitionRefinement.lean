import HexBerlekampZassenhausMathlib.Recovery
import HexBerlekampZassenhausMathlib.Basic

/-!
BHKS B8 partition-refinement step.

The fast-core success branch certified by
`factorFastCoreWithBound_some_factor_count_ge_of_irreducible` consumes an
irreducibility witness for every emitted factor. This module derives that
witness from the BHKS recovery side data: the support-driven canonical
indicator array `BHKS.expectedIndicatorArrayOfSupports trueSupports` has one
row per support-equivalence class, and
`BHKS.ForwardRecoveryInputs.ExpectedTrueFactors` transports that class count
to the polynomial-side factor list length. Under the B8 partition-refinement
hypothesis (the class count matches `normalizedFactors.card`), the existing
UFD partition argument upgrades the count equality to factor irreducibility.

The B8 partition-refinement hypothesis itself is the deeper BHKS Lemma 3.4
obligation discharged elsewhere; this module supplies the count and
irreducibility derivation that consumes it.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

/-- The expected indicator array has one row per support-equivalence class. -/
theorem expectedIndicatorArrayOfSupports_size {r : Nat}
    (trueSupports : Set (Set (Fin r))) :
    (expectedIndicatorArrayOfSupports trueSupports).size =
      (supportPartitionByMinColumn trueSupports).length := by
  simp [expectedIndicatorArrayOfSupports]

namespace ForwardRecoveryInputs

/-- Under an `ExpectedTrueFactors` package whose indicators are the
support-driven canonical indicator array, the expected factor count equals
the support-equivalence partition length. -/
theorem ExpectedTrueFactors.size_eq_supportPartitionByMinColumn_length
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors) :
    expectedFactors.size =
      (supportPartitionByMinColumn trueSupports).length := by
  rw [htrue.size_eq, expectedIndicatorArrayOfSupports_size]

/-- The polynomial-transported expected factor list has length equal to the
support-equivalence partition length. -/
theorem ExpectedTrueFactors.polynomial_length_eq_supportPartitionByMinColumn_length
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors) :
    (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (supportPartitionByMinColumn trueSupports).length := by
  rw [List.length_map, Array.length_toList,
    ExpectedTrueFactors.size_eq_supportPartitionByMinColumn_length trueSupports htrue]

/-- Under the B8 partition-refinement hypothesis (the support-equivalence
partition has the same length as `normalizedFactors`), the polynomial-
transported expected factor list has length `normalizedFactors.card`. -/
theorem ExpectedTrueFactors.polynomial_length_eq_normalizedFactors_card
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hpartition :
      (supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial f)).card) :
    (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial f)).card := by
  rw [ExpectedTrueFactors.polynomial_length_eq_supportPartitionByMinColumn_length
    trueSupports htrue, hpartition]

/-- Under the B8 partition-refinement hypothesis, every polynomial-transported
expected factor is irreducible. This is the B8 partition-refinement output
the downstream fast-core irreducibility argument consumes. -/
theorem ExpectedTrueFactors.irreducible_of_partition_count
    {f : Hex.ZPoly} {r : Nat} (trueSupports : Set (Set (Fin r)))
    {expectedFactors : Array Hex.ZPoly}
    (htrue : ExpectedTrueFactors f
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hf_ne : f ≠ 0)
    (hpartition :
      (supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial f)).card) :
    ∀ g ∈ expectedFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial g) := by
  set fpoly := HexPolyZMathlib.toPolynomial f with hf_def
  have hfpoly_ne : fpoly ≠ 0 := by
    intro hzero
    apply hf_ne
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  set gs : List (Polynomial ℤ) :=
    expectedFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hpos_factor : ∀ g ∈ expectedFactors,
      0 < (HexPolyZMathlib.toPolynomial g).natDegree := by
    intro g hg
    obtain ⟨i, hi_lt, hget⟩ := Array.mem_iff_getElem.mp hg
    have hi_lt' : i < (expectedIndicatorArrayOfSupports trueSupports).size := by
      rw [← htrue.size_eq]; exact hi_lt
    have hdeg := htrue.positive_degree i hi_lt'
    have hgetD : expectedFactors.getD i 0 = g := by
      have := Array.getElem_eq_getD (xs := expectedFactors) (i := i) (h := hi_lt) 0
      rw [← this]; exact hget
    rw [HexPolyMathlib.natDegree_toPolynomial, ← hgetD]
    exact hdeg
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [Array.mem_toList_iff] at hfactor_mem
    rw [← hg_eq]
    exact Polynomial.ne_zero_of_natDegree_gt (hpos_factor factor hfactor_mem)
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [Array.mem_toList_iff] at hfactor_mem
    rw [← hg_eq]
    exact Polynomial.not_isUnit_of_natDegree_pos _ (hpos_factor factor hfactor_mem)
  have hprod : Associated gs.prod fpoly := by
    have hp_factor : Array.polyProduct expectedFactors = f := htrue.product_eq
    have hp_poly :
        (expectedFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial f := by
      rw [← polyProduct_toPolynomial, hp_factor]
    rw [hgs_def, hp_poly, hf_def]
  have hcount :
      gs.length =
        (UniqueFactorizationMonoid.normalizedFactors fpoly).card := by
    rw [hgs_def, hf_def]
    exact ExpectedTrueFactors.polynomial_length_eq_normalizedFactors_card
      trueSupports htrue hpartition
  intro g hg
  have hg_arr : g ∈ expectedFactors := Array.mem_toList_iff.mp hg
  have hgmem : HexPolyZMathlib.toPolynomial g ∈ gs := by
    rw [hgs_def, List.mem_map]
    exact ⟨g, hg, rfl⟩
  exact UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card
    hfpoly_ne gs hne_all hnonunit_all hprod hcount _ hgmem

end ForwardRecoveryInputs

end BHKS

/-- Lower cardinality bound for a successful BHKS fast-core branch whose
emitted candidates have been certified through the B8 partition-refinement
package: the recovery side data provides an `ExpectedTrueFactors` witness
matching the support-driven indicator array, and the partition cardinality
matches the integer-factor count. Together these supply the irreducibility
hypothesis required by `factorFastCoreWithBound_some_factor_count_ge_of_irreducible`. -/
theorem factorFastCoreWithBound_some_factor_count_ge
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length :=
  factorFastCoreWithBound_some_factor_count_ge_of_irreducible h
    (BHKS.ForwardRecoveryInputs.ExpectedTrueFactors.irreducible_of_partition_count
      trueSupports htrue hcore_ne hpartition)

/-- Cardinality equality for a successful BHKS fast-core branch under the B8
partition-refinement package.  Pairs `factorFastCoreWithBound_some_factor_count_le`
with `factorFastCoreWithBound_some_factor_count_ge`, exposing the count
equality requested by #4030 / #4055 in a form directly usable as the `hcount`
hypothesis of `factorFastCoreWithBound_some_factor_irreducible_of_count` and
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count`. -/
theorem factorFastCoreWithBound_some_factor_count_eq
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact factorFastCoreWithBound_some_factor_count_le hcore_ne h
  · exact factorFastCoreWithBound_some_factor_count_ge trueSupports hcore_ne h
      htrue hpartition

/-- Irreducibility for every factor emitted by a successful BHKS fast-core
branch under the partition-refinement package.

This packages the count equality from
`factorFastCoreWithBound_some_factor_count_eq` into the older
`factorFastCoreWithBound_some_factor_irreducible_of_count` scaffold, giving
downstream factorization assembly a branch theorem that no longer has to
thread the count equality manually. -/
theorem factorFastCoreWithBound_some_factor_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) :=
  factorFastCoreWithBound_some_factor_irreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq trueSupports hcore_ne h
      htrue hpartition)

/-- `Hex.ZPoly`-predicate form of
`factorFastCoreWithBound_some_factor_irreducible`. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (htrue : BHKS.ForwardRecoveryInputs.ExpectedTrueFactors core
      (BHKS.expectedIndicatorArrayOfSupports trueSupports) coreFactors)
    (hpartition :
      (BHKS.supportPartitionByMinColumn trueSupports).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor :=
  factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count hcore_ne h
    (factorFastCoreWithBound_some_factor_count_eq trueSupports hcore_ne h
      htrue hpartition)

end HexBerlekampZassenhausMathlib
