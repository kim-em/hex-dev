import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampZassenhausMathlib.Lattice

/-!
Bridge from recovery-side lifted-factor subsets to BHKS true-factor packages.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/--
Transport a recovery-side lifted-factor subset to the BHKS support type.

This relies on the executable `bhksLatticeBasis` computing `factorCount`
definitionally as `d.liftedFactors.size`, so the two `Fin` index types coincide.
-/
def supportOfSubset (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d) :
    LiftedFactorSupport (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors) :=
  (T : Set (LiftedFactorIndex d))

@[simp] theorem mem_supportOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d)
    (i : Fin (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount) :
    i ∈ supportOfSubset f d T ↔ i ∈ T := by
  rfl

private theorem finRange_filter_set_perm
    {n : Nat} (T : Finset (Fin n)) :
    ((List.finRange n).filter
      (fun i => @decide (i ∈ (T : Set (Fin n)))
        (Classical.propDecidable _))).Perm T.toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_finRange n).filter _
  · exact T.nodup_toList
  · ext i
    simp [List.toFinset_filter, List.toFinset_finRange, Finset.toList_toFinset]

/-- The BHKS support product agrees with the recovery-side selected product. -/
theorem supportProduct_supportOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d) :
    supportProduct (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
        (supportOfSubset f d T) =
      liftedFactorProduct d T := by
  classical
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply]
  unfold supportProduct supportOfSubset
  simp only [Hex.bhksLatticeBasis]
  rw [polyProduct_toPolynomial, toPolynomial_liftedFactorProduct]
  simp only [List.map_map, Function.comp_def, liftedFactor]
  trans ∏ i ∈ T, HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1)
  ·
    rw [← Finset.prod_map_toList T
      (fun i => HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1))]
    exact List.Perm.prod_eq (List.Perm.map _
      (finRange_filter_set_perm T))
  · refine Finset.prod_congr rfl ?_
    intro i _hi
    simp

/-- The lifted-factor product over one selected index is that lifted factor. -/
theorem liftedFactorProduct_singleton
    (d : Hex.LiftData) (i : LiftedFactorIndex d) :
    liftedFactorProduct d ({i} : LiftedFactorSubset d) = liftedFactor d i := by
  unfold liftedFactorProduct
  simp

/--
Build a BHKS true-factor package from concrete lift data plus a recovery-side
subset product witness.  The caller supplies the named `factor` because
recovery-side evidence is usually stated against an externally represented
integer factor, not just the raw selected lifted product.
-/
def trueFactorLiftOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d)
    (factor cofactor : Hex.ZPoly)
    (hfactor : factor * cofactor = f)
    (hproduct : liftedFactorProduct d T = factor) :
    TrueFactorLift (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
      (supportOfSubset f d T) where
  f := f
  p := d.p
  a := d.k
  liftedFactors := d.liftedFactors
  basis_eq := rfl
  factor := factor
  cofactor := cofactor
  factor_mul := hfactor
  support_product_eq := by
    rw [supportProduct_supportOfSubset, hproduct]

/--
Derive the semantic BHKS true-factor package for a support drawn from monic
`toMonicLiftData` evidence.

The represented factor's monicity remains an explicit input: the structural
`TrueFactorLift` package only stores the selected product and does not make an
arbitrary recovered integer factor monic.
-/
def trueFactorLiftSemanticsOfToMonicSubset
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (T : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hfactor_monic : Hex.DensePoly.Monic factor)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hproduct :
      liftedFactorProduct (Hex.ZPoly.toMonicLiftData core B primeData) T = factor) :
    TrueFactorLiftSemantics
      (trueFactorLiftOfSubset (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) T
        factor cofactor hfactor hproduct) := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by
    have := hp_prime.two_le
    omega
  have hmonicCore_monic :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hform : Hex.factorsModPBerlekampForm (Hex.ZPoly.toMonic core).monic primeData :=
    Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime (Hex.ZPoly.toMonic core).monic primeData.p = true :=
    Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        (Hex.ZPoly.toMonic core).monic primeData.p :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hmonicCore_monic hform hgood
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm
      (Hex.ZPoly.toMonic core).monic primeData hform
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
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  refine
    { factor_monic := hfactor_monic
      selected_monic := ?_
      selected_pos_degree := ?_
      selectedCofactor := ?_
      selected_congr := ?_ }
  · intro i _hi
    simp [trueFactorLiftOfSubset]
    rw [Array.getElem?_eq_getElem i.isLt]
    simp
    exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
        core B primeData hcore_lc_pos hcore_pos hselected hprecision i
  · intro i _hi
    have hnat :
        0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree :=
      Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
        core B primeData hcore_lc_pos hcore_pos hselected hprecision i
    rw [show HexPolyZMathlib.toPolynomial (liftedFactor d i) =
        HexPolyMathlib.toPolynomial (liftedFactor d i) from rfl,
      HexPolyMathlib.natDegree_toPolynomial] at hnat
    simp [trueFactorLiftOfSubset]
    rw [Array.getElem?_eq_getElem i.isLt]
    simp
    exact hnat
  · intro i _hi
    exact liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d))
  · intro i _hi
    have hcongr :
        Hex.ZPoly.congr
          (liftedFactorProduct d ({i} : LiftedFactorSubset d) *
            liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
          (Hex.ZPoly.toMonic core).monic (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) := by
      simpa [d, Hex.ZPoly.toMonicLiftData] using
        henselLiftData_liftedFactorProduct_subset_complement_congr_core
          (Hex.ZPoly.toMonic core).monic (Hex.precisionForCoeffBound B primeData.p)
          primeData hinv hp hprecision ({i} :
            LiftedFactorSubset
              (Hex.henselLiftData (Hex.ZPoly.toMonic core).monic
                (Hex.precisionForCoeffBound B primeData.p) primeData))
    have hcongr' :
        Hex.ZPoly.congr
          ((liftedFactor d i) *
            liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
          (Hex.ZPoly.toMonic core).monic (d.p ^ d.k) := by
      have hsingle := liftedFactorProduct_singleton d i
      change Hex.ZPoly.congr
        (liftedFactorProduct d ({i} : LiftedFactorSubset d) *
          liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
        (Hex.ZPoly.toMonic core).monic
        (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) at hcongr
      have hleft :
          liftedFactorProduct d ({i} : LiftedFactorSubset d) *
          liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)) =
            liftedFactor d i *
              liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)) := by
        exact congrArg
          (fun x => x * liftedFactorProduct d
            (Finset.univ \ ({i} : LiftedFactorSubset d))) hsingle
      have hleft_congr :
          Hex.ZPoly.congr
            (liftedFactor d i *
              liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
            (liftedFactorProduct d ({i} : LiftedFactorSubset d) *
              liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
            (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) := by
        rw [hleft]
        exact Hex.ZPoly.congr_refl _ _
      exact Hex.ZPoly.congr_trans _ _ _ _
        hleft_congr (by simpa [d, Hex.ZPoly.toMonicLiftData] using hcongr)
    simp [trueFactorLiftOfSubset]
    rw [Array.getElem?_eq_getElem i.isLt]
    simp [d]
    exact Hex.ZPoly.congr_symm _ _ _ hcongr'

end BHKS

end

end HexBerlekampZassenhausMathlib
