import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.Recovery

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

@[simp, grind =] theorem mem_supportOfSubset
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
Build a recovered BHKS true-factor package from concrete lift data plus the
centered/dilated recovery equality produced by the executable recovery path.

Unlike `trueFactorLiftOfSubset`, this constructor does not require the raw
integer equality `liftedFactorProduct d T = factor`; it records exactly the
recovered product shape exposed by the BHKS candidate/recovery lemmas.
-/
def recoveredLiftOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d)
    (factor cofactor : Hex.ZPoly)
    (hfactor : factor * cofactor = f)
    (hrecovered :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
          (Hex.centeredLiftPoly (liftedFactorProduct d T) (d.p ^ d.k)) =
        factor) :
    RecoveredLift (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
      (supportOfSubset f d T) where
  f := f
  p := d.p
  a := d.k
  liftedFactors := d.liftedFactors
  basis_eq := rfl
  factor := factor
  cofactor := cofactor
  factor_mul := hfactor
  recovered_eq := by
    rw [supportProduct_supportOfSubset, hrecovered]

/--
Build a recovered BHKS true-factor package directly from a monic-core
`RepresentsIntegerFactorAtLift` witness emitted by the fast-core extractor.

This is the producer half of the recovery contract: the centered/dilated
recovery equality that `recoveredLiftOfSubset` consumes is discharged from the
witness by `dilate_centeredLift_eq_factor_of_represents_monic`, so the caller
only supplies the cofactor identity and the Mignotte precision bound.  The monic
hypothesis is the regime the fast-core extractor operates in (`Monic core`),
where the leading-coefficient dilation collapses and the represented
monic-coordinate witness is itself primitive.
-/
def recoveredLiftOfRepresents
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (factor cofactor : Hex.ZPoly)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hfactor : factor * cofactor = core)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    RecoveredLift (Hex.bhksLatticeBasis core d.p d.k d.liftedFactors)
      (supportOfSubset core d S) :=
  recoveredLiftOfSubset core d S factor cofactor hfactor
    (dilate_centeredLift_eq_factor_of_represents_monic hcore_monic hrep hprecision)

/--
Build a recovered BHKS true-factor package for the monic coordinate used by
`toMonicLiftData`.

The executable non-monic fast path selects prime and lift data from the original
`core`, but the Hensel factors live over `(toMonic core).monic`.  This adapter
packages a representation witness for that monic coordinate as a `RecoveredLift`
over the `bhksLatticeBasis` built from the same `toMonicLiftData`.
-/
def recoveredLiftOfToMonicRepresents
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S) :
    RecoveredLift
      (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData).p
        (Hex.ZPoly.toMonicLiftData core B primeData).k
        (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors)
      (supportOfSubset (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) S) := by
  let M := (Hex.ZPoly.toMonic core).monic
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  have hM_monic : Hex.DensePoly.Monic M :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hM_toMonic : (Hex.ZPoly.toMonic M).monic = M :=
    Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one M hM_monic
  have hprecisionM :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic M).monic <
        d.p ^ d.k := by
    simpa [M, d, hM_toMonic] using hprecision
  exact recoveredLiftOfRepresents M d S factor cofactor hM_monic hfactor
    hprecisionM hrep

@[simp] theorem recoveredLiftOfToMonicRepresents_f
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S) :
    (recoveredLiftOfToMonicRepresents core B primeData S factor cofactor
      hcore_lc_pos hcore_pos hfactor hprecision hrep).f = (Hex.ZPoly.toMonic core).monic := by
  simp [recoveredLiftOfToMonicRepresents, recoveredLiftOfRepresents, recoveredLiftOfSubset]

@[simp] theorem recoveredLiftOfToMonicRepresents_p
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S) :
    (recoveredLiftOfToMonicRepresents core B primeData S factor cofactor
      hcore_lc_pos hcore_pos hfactor hprecision hrep).p =
        (Hex.ZPoly.toMonicLiftData core B primeData).p := by
  simp [recoveredLiftOfToMonicRepresents, recoveredLiftOfRepresents, recoveredLiftOfSubset]

@[simp] theorem recoveredLiftOfToMonicRepresents_a
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S) :
    (recoveredLiftOfToMonicRepresents core B primeData S factor cofactor
      hcore_lc_pos hcore_pos hfactor hprecision hrep).a =
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
  simp [recoveredLiftOfToMonicRepresents, recoveredLiftOfRepresents, recoveredLiftOfSubset]

@[simp] theorem recoveredLiftOfToMonicRepresents_factor
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (factor cofactor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hfactor : factor * cofactor = (Hex.ZPoly.toMonic core).monic)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S) :
    (recoveredLiftOfToMonicRepresents core B primeData S factor cofactor
      hcore_lc_pos hcore_pos hfactor hprecision hrep).factor = factor := by
  simp [recoveredLiftOfToMonicRepresents, recoveredLiftOfRepresents, recoveredLiftOfSubset]

/--
Transport a represented monic-coordinate factor through `toMonic` and recover
the original non-monic factor as the primitive-part carrier.

This is the sound non-monic replacement for asking for a raw
`RecoveredLift (bhksLatticeBasis core ...)`: the selected lifted product lives
over `(toMonic core).monic`, and returning to `core` requires
`primitivePart (dilate (leadingCoeff core) ·)`.
-/
noncomputable def recoveredAtLiftOfToMonic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (monicFactor factor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) monicFactor S)
    (hrecover :
      Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
        factor) :
    RecoveredAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) factor S := by
  let M := (Hex.ZPoly.toMonic core).monic
  have hM_monic : Hex.DensePoly.Monic M :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  exact Classical.choice
    (representsIntegerFactorAtLift_of_monicCorrespondent
      (core := core) (M := M) (factor := factor) (g := monicFactor)
      (d := Hex.ZPoly.toMonicLiftData core B primeData) (S := S)
      rfl hM_monic hrep hrecover)

/-- Predicate form of `recoveredAtLiftOfToMonic`. -/
theorem representsOfToMonic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (monicFactor factor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) monicFactor S)
    (hrecover :
      Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
        factor) :
    RepresentsIntegerFactorAtLift core
      (Hex.ZPoly.toMonicLiftData core B primeData) factor S :=
  RepresentsIntegerFactorAtLift.ofRecovered
    (recoveredAtLiftOfToMonic core B primeData S monicFactor factor
      hcore_lc_pos hcore_pos hrep hrecover)

/--
Recovered-candidate equality for the original non-monic core, after transporting
a monic-coordinate representation through `toMonic`.
-/
theorem recoveryCandidate_eq_of_toMonic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData))
    (monicFactor factor : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    (hfactor_sign : Hex.normalizeFactorSign factor = factor)
    (hrep :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) monicFactor S)
    (hrecover :
      Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) monicFactor) =
        factor) :
    liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = factor :=
  toMonicLiftData_liftedRecoveryCandidate_eq core B primeData
    hcore_lc_pos hcore_pos hselected hbound hfactor_sign
    (representsOfToMonic core B primeData S monicFactor factor
      hcore_lc_pos hcore_pos hrep hrecover)

/--
Every raw true-factor lift also gives a recovered-lift certificate when the
caller supplies the corresponding centered/dilated recovery equality.  This is a
thin adapter for proof paths that already carry `TrueFactorLift` data but need
to enter the recovered-product API.
-/
def recoveredLiftOfTrueFactorLift
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : TrueFactorLift L S)
    (hrecovered :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff D.f)
          (Hex.centeredLiftPoly (supportProduct L S) (D.p ^ D.a)) =
        D.factor) :
    RecoveredLift L S where
  f := D.f
  p := D.p
  a := D.a
  liftedFactors := D.liftedFactors
  basis_eq := D.basis_eq
  factor := D.factor
  cofactor := D.cofactor
  factor_mul := D.factor_mul
  recovered_eq := hrecovered

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

/-- The prime selected by `toMonicPrimeData?` is at least two, so the lift
modulus base `(toMonicLiftData core B primeData).p` is at least two.  This is the
`hp` side condition of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`. -/
theorem toMonicLiftData_two_le_p
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData) :
    2 ≤ (Hex.ZPoly.toMonicLiftData core B primeData).p := by
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  rw [hp_eq]
  exact (Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected).two_le

/-- The lift modulus `(toMonicLiftData core B primeData).p ^ k` exceeds one
whenever the precision is positive.  This is the `hk` side condition of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`. -/
theorem toMonicLiftData_one_lt_modulus
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p) :
    1 < (Hex.ZPoly.toMonicLiftData core B primeData).p ^
        (Hex.ZPoly.toMonicLiftData core B primeData).k := by
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  rw [hp_eq, hk_eq]
  have hp : 2 ≤ primeData.p :=
    (Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected).two_le
  calc 1 < primeData.p ^ 1 := by simpa using hp
    _ ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
        Nat.pow_le_pow_right (by omega) hprecision

/--
**Per-index Hensel semantics for the monic `toMonicLiftData` coordinate**
(deliverable of #7924, capstone #6672).

For every lifted-factor index `i` of `toMonicLiftData core B primeData`, the
lifted factor is monic, has positive degree, and divides the monic transform
`(toMonic core).monic` modulo `p ^ k` with an explicit complement (the product
of the other lifted factors).  These are exactly the per-index `hfac` side
conditions of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`, derived
from the `toMonicPrimeData?` selection witness rather than re-bundled as caller
hypotheses.

This factors out the `selected_*` fields of
`trueFactorLiftSemanticsOfToMonicSubset` without requiring the raw
`TrueFactorLift` support-product equality: the congruence is the per-index
specialisation of `henselLiftData_liftedFactorProduct_subset_complement_congr_core`,
with the complement taken over `Finset.univ \ {i}`.
-/
theorem toMonicLiftData_liftedFactor_hensel_semantics
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size) :
    ∃ g : Hex.ZPoly,
      Hex.DensePoly.Monic
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) ∧
        0 < (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i).degree?.getD 0 ∧
        Hex.ZPoly.congr (Hex.ZPoly.toMonic core).monic
          (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i * g)
          ((Hex.ZPoly.toMonicLiftData core B primeData).p ^
            (Hex.ZPoly.toMonicLiftData core B primeData).k) := by
  classical
  let d := Hex.ZPoly.toMonicLiftData core B primeData
  -- Monicity and positive degree from the existing per-index producers.
  have hmonic := Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
    core B primeData hcore_lc_pos hcore_pos hselected hprecision i
  have hnat := Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
    core B primeData hcore_lc_pos hcore_pos hselected hprecision i
  rw [show HexPolyZMathlib.toPolynomial (liftedFactor d i) =
      HexPolyMathlib.toPolynomial (liftedFactor d i) from rfl,
    HexPolyMathlib.natDegree_toPolynomial] at hnat
  refine ⟨liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)),
    hmonic, hnat, ?_⟩
  -- Rebuild the Hensel lift invariant for the monic transform from the
  -- `toMonicPrimeData?` selection witness.
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by have := hp_prime.two_le; omega
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
  -- The subset/complement congruence at the singleton `{i}`.
  have hcongr :
      Hex.ZPoly.congr
        (liftedFactorProduct d ({i} : LiftedFactorSubset d) *
          liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
        (Hex.ZPoly.toMonic core).monic
        (primeData.p ^ Hex.precisionForCoeffBound B primeData.p) := by
    simpa [d, Hex.ZPoly.toMonicLiftData] using
      henselLiftData_liftedFactorProduct_subset_complement_congr_core
        (Hex.ZPoly.toMonic core).monic (Hex.precisionForCoeffBound B primeData.p)
        primeData hinv hp hprecision ({i} :
          LiftedFactorSubset
            (Hex.henselLiftData (Hex.ZPoly.toMonic core).monic
              (Hex.precisionForCoeffBound B primeData.p) primeData))
  -- Replace the singleton product by the lifted factor itself.
  rw [show liftedFactorProduct d ({i} : LiftedFactorSubset d) = liftedFactor d i from
    liftedFactorProduct_singleton d i] at hcongr
  exact Hex.ZPoly.congr_symm _ _ _ hcongr

/-- A constant rescaling pulls through one factor of a product:
`scale c (a * b) = a * scale c b`.  Proved by transport to `Polynomial ℤ`. -/
private theorem scale_mul_right_zpoly (c : Int) (a b : Hex.ZPoly) :
    Hex.DensePoly.scale c (a * b) = a * Hex.DensePoly.scale c b := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial (Hex.DensePoly.scale c (a * b))
      = HexPolyZMathlib.toPolynomial (a * Hex.DensePoly.scale c b)
  simp only [← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
    HexPolyZMathlib.toPolynomial_C]
  ring

/--
**M1 (`monicTarget`-coordinate) Hensel lift semantics.**  The `coreLiftData`
analogue of `toMonicLiftData_liftedFactor_hensel_semantics`: each lifted factor
`gᵢ` of `coreLiftData core B primeData` is monic, of positive degree, and divides
`core` directly modulo `p^a` (the complement is the `ℓf`-scaled product of the
other lifted factors).  This is the per-factor `hfac` the core forward cut
(#8290) consumes, landed against `core` itself rather than against the lift
target.

The Hensel lift invariant for the `monicTarget` is rebuilt from `core`'s own
`choosePrimeData?` selection witness: over `ℤ/p` the `monicTarget` is the unit
rescaling `ℓf⁻¹·core` (`monicModularImage_modP_eq_modP_monicTarget`), so the
`factorsModP` boundary facts transfer verbatim
(`factorsModP_polyProduct_congr_monicTarget`).  The translation back to `core`'s
coordinate is the BHKS mod-bridge `leadingCoeff_scale_monicTarget_congr_core`. -/
theorem coreLiftData_liftedFactor_hensel_semantics
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (primeData.p ^ Hex.precisionForCoeffBound B primeData.p)) = 1)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (i : Fin (Hex.ZPoly.coreLiftData core B primeData).liftedFactors.size) :
    ∃ h : Hex.ZPoly,
      Hex.DensePoly.Monic (liftedFactor (Hex.ZPoly.coreLiftData core B primeData) i) ∧
        0 < (liftedFactor (Hex.ZPoly.coreLiftData core B primeData) i).degree?.getD 0 ∧
        Hex.ZPoly.congr core
          (liftedFactor (Hex.ZPoly.coreLiftData core B primeData) i * h)
          ((Hex.ZPoly.coreLiftData core B primeData).p ^
            (Hex.ZPoly.coreLiftData core B primeData).k) := by
  classical
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  set prec := Hex.precisionForCoeffBound B primeData.p with hprec
  set target := Hex.ZPoly.monicTarget core primeData.p prec with htarget
  set d := Hex.henselLiftData target prec primeData with hd
  -- Prime / selection boundary facts about `core`.
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by have := hp_prime.two_le; omega
  have hpk : 1 < primeData.p ^ prec :=
    Nat.one_lt_pow (by omega) hp
  obtain ⟨hzeroP, heqP⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
  have hform : Hex.factorsModPBerlekampForm core primeData := ⟨hp_prime, hzeroP, heqP⟩
  have hgood : Hex.isGoodPrime core primeData.p = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  -- `monicTarget` is monic.
  have hcore_size : 0 < core.size := by
    rcases Nat.eq_zero_or_pos core.size with hz | hpos
    · exfalso
      have : core.degree?.getD 0 = 0 := by simp [Hex.DensePoly.degree?, hz]
      omega
    · exact hpos
  have hmonic_target : Hex.DensePoly.Monic target :=
    Hex.ZPoly.monicTarget_monic core primeData.p prec hpk hgcd hcore_size
  -- The four `QuadraticMultifactorLiftInvariant` boundary hypotheses.
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm core primeData hform
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        target primeData.p :=
    factorsModP_polyProduct_congr_monicTarget core prec primeData hpk
      (by omega) hgcd hform hgood
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm core primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm core primeData hform
  have hfactors_natDegree :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree :=
    factorsModP_natDegree_pos_of_factorsModPBerlekampForm core primeData hform hgood hcore_pos
  -- Monicity and positive degree of the lifted factor, from the `choosePrimeData`
  -- umbrellas applied at the `monicTarget`.
  have hmonic :=
    henselLiftData_liftedFactor_monic_of_choosePrimeData target prec primeData
      hmonic_target hp_prime hp hprecision hfactors_monic hproduct_mod_p hcoprime hnonempty i
  have hnat :=
    henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData target prec primeData
      hmonic_target hp_prime hp hprecision hfactors_monic hproduct_mod_p hcoprime hnonempty
      hfactors_natDegree i
  rw [show HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.henselLiftData target prec primeData) i) =
      HexPolyMathlib.toPolynomial
        (liftedFactor (Hex.henselLiftData target prec primeData) i) from rfl,
    HexPolyMathlib.natDegree_toPolynomial] at hnat
  -- The Hensel lift invariant for the `monicTarget`.
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant primeData.p prec target
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData target prec primeData
      hp_prime hp hprecision hmonic_target hfactors_monic hproduct_mod_p hcoprime hnonempty
  -- The subset/complement congruence at the singleton `{i}`, against the `monicTarget`.
  have hcongr :
      Hex.ZPoly.congr
        (liftedFactorProduct d ({i} : LiftedFactorSubset d) *
          liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d)))
        target (primeData.p ^ prec) := by
    exact
      henselLiftData_liftedFactorProduct_subset_complement_congr_core
        target prec primeData hinv hp hprecision ({i} : LiftedFactorSubset d)
  rw [show liftedFactorProduct d ({i} : LiftedFactorSubset d) = liftedFactor d i from
    liftedFactorProduct_singleton d i] at hcongr
  -- Translate from the `monicTarget` coordinate back to `core` by scaling by `ℓf`.
  refine ⟨Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
      (liftedFactorProduct d (Finset.univ \ ({i} : LiftedFactorSubset d))),
    hmonic, hnat, ?_⟩
  have hscaled :=
    scale_congr_of_congr (Hex.DensePoly.leadingCoeff core) _ _ _ hcongr
  have hmt_core :=
    leadingCoeff_scale_monicTarget_congr_core core primeData.p prec hpk hgcd
  have hchain := Hex.ZPoly.congr_trans _ _ _ _ hscaled hmt_core
  rw [scale_mul_right_zpoly] at hchain
  exact Hex.ZPoly.congr_symm _ _ _ hchain

namespace ForwardRecoveryInputs

/--
**Monic-lattice `RecoveredLift` family from fast-core indicator-candidate
success** (prerequisite (A) of #7894, capstone #6672).

From a successful indicator-candidate fold over the *non-monic* fast-path core
(`bhksIndicatorCandidates? core d … = some coreFactors`), build, for every
emitted support, a `RecoveredLift` over the **monic** lattice
`bhksLatticeBasis (toMonic core).monic …`.  The recovered factor of each support
is the centred lift of the selected lifted product, which is exactly the monic
correspondent of the emitted recombination candidate
(`centeredLift_dvd_toMonic`): the executable exact-division witness
`candidate ∣ core` transports to `cl ∣ (toMonic core).monic`, and the
leading-coefficient dilation in `recovered_eq` collapses because the monic
transform has leading coefficient `1`.

This is the monic-core regime where `recoveredLiftOfSubset` applies; a
non-monic-core `RecoveredLift` is provably impossible (its `recovered_eq` would
need `content (dilate (lc core) monicFactor) = 1`, false for non-unit
`leadingCoeff core`).  The family feeds the period-adjusted column bound
`supportShortVectorData_of_recoveredLift` (`CLDColumnBound.lean`).

This is a `def` because `RecoveredLift` is a data-carrying certificate, not a
`Prop`. -/
def recoveredLift_family_of_indicatorCandidates
    {core : Hex.ZPoly} {d : Hex.LiftData} {coreFactors : Array Hex.ZPoly}
    (rows_pos : HasPositiveDimension core d)
    (trueSupports :
       Set (Set (Fin (projectedRowsOfLiftData core d rows_pos).factorCount)))
    (hindicators :
       equivalenceClassIndicatorsOfLiftData core d rows_pos =
         expectedIndicatorArrayOfSupports trueSupports)
    (hcandidates :
       Hex.bhksIndicatorCandidates? core d
           (equivalenceClassIndicatorsOfLiftData core d rows_pos) = some coreFactors)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hliftedFactor_monic : ∀ i : LiftedFactorIndex d, Hex.DensePoly.Monic (liftedFactor d i))
    (hp_two_le : 2 ≤ d.p ^ d.k) :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      RecoveredLift
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic d.p d.k d.liftedFactors)
        (supportOfSubset (Hex.ZPoly.toMonic core).monic d
          ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅)) := by
  classical
  intro i hi
  have hi_expected : i < (equivalenceClassIndicatorsOfLiftData core d rows_pos).size := by
    rw [hindicators]; exact hi
  -- the emitted candidate and its selected lifted-factor product (extract the
  -- quotient witness via `choose`, as the goal is data-valued)
  have hcand_ex := Hex.bhksIndicatorCandidates?_getD_candidate hcandidates i hi_expected
  rw [hindicators] at hcand_ex
  have hcandidate0 := hcand_ex.choose_spec
  have hselected :=
    bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports d trueSupports
      (supportPartitionByMinColumn_class_nonempty trueSupports)
      (supportPartitionByMinColumn_class_lt trueSupports) i hi
  set selected := (selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]
    with hsel_def
  set candidate := coreFactors.getD i 0 with hcand_def
  set T := (liftedFactorSubsetsOfSupports d trueSupports).getD i ∅ with hT_def
  set cl := Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k) with hcl_def
  -- the selected product equals the lifted-factor product over `T`, which is
  -- monic (product of monic lifted factors), so its centred lift `cl` is monic
  have hpp_eq : Array.polyProduct selected = liftedFactorProduct d T :=
    selectedFactorArraysOfSupports_polyProduct d trueSupports i hi
  have hprod_monic : Hex.DensePoly.Monic (Array.polyProduct selected) := by
    rw [hpp_eq]; exact liftedFactorProduct_monic d T (fun j _ => hliftedFactor_monic j)
  have hcl_monic : Hex.DensePoly.Monic cl :=
    monic_centeredLiftPoly_of_monic hprod_monic hp_two_le
  -- the candidate is the primitive part of the leading-coefficient dilation of `cl`
  have hcand_recover :
      Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl) = candidate :=
    primitivePart_dilate_centeredLift_eq_candidate hcandidate0 hselected hcore_lc_pos hcl_monic
  have hcand_dvd : candidate ∣ core := Hex.bhksIndicatorCandidate?_dvd hcandidate0
  have hcand_prim : Hex.ZPoly.Primitive candidate := Hex.bhksIndicatorCandidate?_primitive hcandidate0
  -- the candidate has positive leading coefficient, so it is sign-normalized
  have hcand_sign : Hex.normalizeFactorSign candidate = candidate := by
    have hpos : 0 < Hex.DensePoly.leadingCoeff candidate := by
      rw [← hcand_recover]; exact leadingCoeff_primitivePart_dilate_pos hcore_lc_pos hcl_monic
    unfold Hex.normalizeFactorSign
    rw [if_neg (not_lt.mpr (le_of_lt hpos))]
  have hcand_deg : 1 ≤ candidate.degree?.getD 0 := by
    have hsize_eq : coreFactors.size = (equivalenceClassIndicatorsOfLiftData core d rows_pos).size :=
      Hex.bhksIndicatorCandidates?_size_eq hcandidates
    have hi_cf : i < coreFactors.size := by rw [hsize_eq]; exact hi_expected
    have hmem : candidate ∈ coreFactors.toList := by
      have h1 : coreFactors.getD i 0 = coreFactors[i] := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi_cf]
      rw [hcand_def, h1]
      exact Array.getElem_mem_toList hi_cf
    exact Hex.bhksIndicatorCandidates?_positive_degree hcandidates candidate hmem
  -- the centred lift divides the monic transform
  have hcl_dvd : cl ∣ (Hex.ZPoly.toMonic core).monic :=
    centeredLift_dvd_toMonic hcore_lc_pos hcore_pos hcl_monic hcand_deg hcand_recover
      hcand_dvd hcand_prim hcand_sign
  have hcof : (Hex.ZPoly.toMonic core).monic = cl * hcl_dvd.choose := hcl_dvd.choose_spec
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hrecovered :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic)
          (Hex.centeredLiftPoly (liftedFactorProduct d T) (d.p ^ d.k)) = cl := by
    rw [← hpp_eq, show Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 from hM_monic,
      Hex.ZPoly.dilate_one]
  exact recoveredLiftOfSubset (Hex.ZPoly.toMonic core).monic d T cl hcl_dvd.choose
    hcof.symm hrecovered

/--
**Emitted/canonical support set** for the indicator partition of `trueSupports`.

These are exactly the lifted-factor supports reached by the array indices of
`recoveredLift_family_of_indicatorCandidates`: the image, over the canonical
indicator partition, of `supportOfSubset M d` applied to the partition's
lifted-factor subsets.  Defining the support set as this image is what makes the
index/surjectivity fact (#7923) hold *by construction* — every member is,
definitionally, reached by one of the array indices — rather than requiring a
disjointness or partition hypothesis on a free `trueSupports` (which is unsound:
overlapping supports collapse under `supportPartitionByMinColumn`). -/
noncomputable def emittedSupports
    (M : Hex.ZPoly) (d : Hex.LiftData)
    {r : Nat} (trueSupports : Set (Set (Fin r))) :
    Set (LiftedFactorSupport (Hex.bhksLatticeBasis M d.p d.k d.liftedFactors)) :=
  {S | ∃ i, i < (expectedIndicatorArrayOfSupports trueSupports).size ∧
    supportOfSubset M d ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅) = S}

/--
**Subtype-indexed recovered-lift family** (#7923).

Repackage the array-indexed family `recoveredLift_family_of_indicatorCandidates`
as a family indexed by the canonical emitted-support subtype `emittedSupports`.
The index/surjectivity fact is discharged from the definition of
`emittedSupports`: each `S : emittedSupports …` carries a witnessing array index
`i`, at which the array-indexed family already produces the certificate, and
transporting along the support equality lands it at `S.1`.

This is the shape consumed by the line-714 endpoint
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift` as its
`lift : ∀ S : trueSupports, RecoveredLift L S.1` argument, with `trueSupports`
instantiated to `emittedSupports (toMonic core).monic d …`.

This is a `def` because `RecoveredLift` is a data-carrying certificate. -/
def recoveredLift_subtypeFamily_of_indicatorCandidates
    {core : Hex.ZPoly} {d : Hex.LiftData} {coreFactors : Array Hex.ZPoly}
    (rows_pos : HasPositiveDimension core d)
    (trueSupports :
       Set (Set (Fin (projectedRowsOfLiftData core d rows_pos).factorCount)))
    (hindicators :
       equivalenceClassIndicatorsOfLiftData core d rows_pos =
         expectedIndicatorArrayOfSupports trueSupports)
    (hcandidates :
       Hex.bhksIndicatorCandidates? core d
           (equivalenceClassIndicatorsOfLiftData core d rows_pos) = some coreFactors)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hliftedFactor_monic : ∀ i : LiftedFactorIndex d, Hex.DensePoly.Monic (liftedFactor d i))
    (hp_two_le : 2 ≤ d.p ^ d.k) :
    ∀ S : emittedSupports (Hex.ZPoly.toMonic core).monic d trueSupports,
      RecoveredLift
        (Hex.bhksLatticeBasis (Hex.ZPoly.toMonic core).monic d.p d.k d.liftedFactors)
        S.1 := by
  classical
  intro S
  -- `S.2 : ∃ i, i < size ∧ supportOfSubset … = S.1` is a `Prop`, so it cannot be
  -- pattern-matched into the data-valued `RecoveredLift` goal; extract the
  -- witnessing index with `choose` and transport along the support equality.
  have hmem := S.2
  exact hmem.choose_spec.2 ▸
    recoveredLift_family_of_indicatorCandidates rows_pos trueSupports
      hindicators hcandidates hcore_lc_pos hcore_pos hliftedFactor_monic hp_two_le
      hmem.choose hmem.choose_spec.1

/-- Transport along a support equality leaves the `RecoveredLift.p` field
unchanged: the field does not depend on the support index. -/
@[simp] theorem RecoveredLift.p_eqRec {L : Hex.BhksLatticeBasis}
    {a b : LiftedFactorSupport L} (h : a = b) (x : RecoveredLift L a) :
    (h ▸ x).p = x.p := by subst h; rfl

/-- Transport along a support equality leaves the `RecoveredLift.a` field
unchanged: the field does not depend on the support index. -/
@[simp] theorem RecoveredLift.a_eqRec {L : Hex.BhksLatticeBasis}
    {a b : LiftedFactorSupport L} (h : a = b) (x : RecoveredLift L a) :
    (h ▸ x).a = x.a := by subst h; rfl

/-- Transport along a support equality leaves the `RecoveredLift.f` field
unchanged: the field does not depend on the support index. -/
@[simp] theorem RecoveredLift.f_eqRec {L : Hex.BhksLatticeBasis}
    {a b : LiftedFactorSupport L} (h : a = b) (x : RecoveredLift L a) :
    (h ▸ x).f = x.f := by subst h; rfl

/-- Transport along a support equality leaves the `RecoveredLift.factor` field
unchanged: the field does not depend on the support index. -/
@[simp] theorem RecoveredLift.factor_eqRec {L : Hex.BhksLatticeBasis}
    {a b : LiftedFactorSupport L} (h : a = b) (x : RecoveredLift L a) :
    (h ▸ x).factor = x.factor := by subst h; rfl

/-- The lift modulus base `p` of every member of the subtype-indexed
recovered-lift family is the underlying lift data's prime base `d.p`. -/
theorem recoveredLift_subtypeFamily_of_indicatorCandidates_p
    {core : Hex.ZPoly} {d : Hex.LiftData} {coreFactors : Array Hex.ZPoly}
    (rows_pos : HasPositiveDimension core d)
    (trueSupports :
       Set (Set (Fin (projectedRowsOfLiftData core d rows_pos).factorCount)))
    (hindicators :
       equivalenceClassIndicatorsOfLiftData core d rows_pos =
         expectedIndicatorArrayOfSupports trueSupports)
    (hcandidates :
       Hex.bhksIndicatorCandidates? core d
           (equivalenceClassIndicatorsOfLiftData core d rows_pos) = some coreFactors)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hliftedFactor_monic : ∀ i : LiftedFactorIndex d, Hex.DensePoly.Monic (liftedFactor d i))
    (hp_two_le : 2 ≤ d.p ^ d.k)
    (S : emittedSupports (Hex.ZPoly.toMonic core).monic d trueSupports) :
    (recoveredLift_subtypeFamily_of_indicatorCandidates rows_pos trueSupports hindicators
      hcandidates hcore_lc_pos hcore_pos hliftedFactor_monic hp_two_le S).p = d.p := by
  unfold recoveredLift_subtypeFamily_of_indicatorCandidates
  rw [RecoveredLift.p_eqRec]
  rfl

/-- The lift precision `a` of every member of the subtype-indexed
recovered-lift family is the underlying lift data's precision `d.k`. -/
theorem recoveredLift_subtypeFamily_of_indicatorCandidates_a
    {core : Hex.ZPoly} {d : Hex.LiftData} {coreFactors : Array Hex.ZPoly}
    (rows_pos : HasPositiveDimension core d)
    (trueSupports :
       Set (Set (Fin (projectedRowsOfLiftData core d rows_pos).factorCount)))
    (hindicators :
       equivalenceClassIndicatorsOfLiftData core d rows_pos =
         expectedIndicatorArrayOfSupports trueSupports)
    (hcandidates :
       Hex.bhksIndicatorCandidates? core d
           (equivalenceClassIndicatorsOfLiftData core d rows_pos) = some coreFactors)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hliftedFactor_monic : ∀ i : LiftedFactorIndex d, Hex.DensePoly.Monic (liftedFactor d i))
    (hp_two_le : 2 ≤ d.p ^ d.k)
    (S : emittedSupports (Hex.ZPoly.toMonic core).monic d trueSupports) :
    (recoveredLift_subtypeFamily_of_indicatorCandidates rows_pos trueSupports hindicators
      hcandidates hcore_lc_pos hcore_pos hliftedFactor_monic hp_two_le S).a = d.k := by
  unfold recoveredLift_subtypeFamily_of_indicatorCandidates
  rw [RecoveredLift.a_eqRec]
  rfl

end ForwardRecoveryInputs

end BHKS

end

end HexBerlekampZassenhausMathlib
