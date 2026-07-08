/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.PrimitivityProofs
public meta import HexBerlekampZassenhaus.PrimitivityProofs
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.QuadraticRootProofs
import all HexBerlekampZassenhaus.PrimitivityProofs

public section
set_option backward.proofsInPublic true

/-!
This module collects `factorTrial_product`, `factorize_product`, and the `checkIrreducibleCert_*` proofs.
-/
namespace Hex

/-- **#4585 HO-1 support lemma — fast-path constant arm `reassemblyExpansionComplete`
discharger.** When the recorded square-free core has degree zero (and `f ≠ 0`),
the singleton-core reassembly is automatically expansion-complete: the
square-free core collapses to `1` via
`squareFreeCore_eq_one_of_constant_of_ne_zero`, the singleton-`1` expansion is
the identity via `expandRepeatedPartFactorArray_singleton_one`, and the residual
`(normalizeForFactor f).repeatedPart` is forced to `1` by
`normalizeForFactor_repeatedPart_eq_one_of_constant` (the constant-branch
specialisation of
`ZPoly.primitiveSquareFreeDecomposition_repeatedPart_eq_one_of_squareFreeCore_degree_zero`).
Used by the fast-path constant arm public wrapper
`factor_constant_branch_entry_irreducible_of_choosePrimeData` (#4565) so it can
drop its explicit `hcomplete` hypothesis. The small-mod singleton (#4564),
slow-quadratic (#4575), and fast-quadratic (#4571) `hcomplete` dischargers are
siblings tracked separately. -/
theorem reassemblyExpansionComplete_constant_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    reassemblyExpansionComplete (normalizeForFactor f)
      #[(normalizeForFactor f).squareFreeCore] := by
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg
  have hrep_one := normalizeForFactor_repeatedPart_eq_one_of_constant f hf hdeg
  unfold reassemblyExpansionComplete
  rw [hcore_one, expandRepeatedPartFactorArray_singleton_one]
  exact hrep_one

/-- The normalized square-free core has positive leading coefficient
(`squareFreeCore_leadingCoeff_pos_of_ne_zero`), so its sign-normalisation
is the identity. Exposed publicly for HO-1 support-lemma callers in the
Mathlib-side layer (notably the small-mod singleton arm specialisation of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`,
which discharges its `hnorm` precondition with this lemma). -/
theorem squareFreeCore_normalizeFactorSign_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    normalizeFactorSign (normalizeForFactor f).squareFreeCore =
      (normalizeForFactor f).squareFreeCore := by
  apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
  have hpos := squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  omega

private theorem squareFreeCore_shouldRecord_of_degree_pos
    (f : ZPoly) (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0) :
    shouldRecordPolynomialFactor (normalizeForFactor f).squareFreeCore = true := by
  have hne_zero : (normalizeForFactor f).squareFreeCore ≠ 0 :=
    squareFreeCore_ne_zero_of_ne_zero f hf
  have hne_one : (normalizeForFactor f).squareFreeCore ≠ 1 := by
    intro hone
    apply hdeg
    rw [hone]
    change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
    exact DensePoly.degree?_C_getD 1
  have hne_neg_one : (normalizeForFactor f).squareFreeCore ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    apply hdeg
    rw [hneg]
    exact DensePoly.degree?_C_getD (-1)
  unfold shouldRecordPolynomialFactor
  simp [hne_zero, hne_one, hne_neg_one]

private theorem filteredNormalizedFactors_append_one_of_all_recorded_normalized
    (factors : List ZPoly)
    (hnormalized :
      ∀ factor ∈ factors, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true) :
    filteredNormalizedFactors (factors ++ [1]) = factors := by
  induction factors with
  | nil =>
      rw [List.nil_append, filteredNormalizedFactors_cons_drop]
      · rfl
      · rw [normalizeFactorSign_one]
        exact shouldRecordPolynomialFactor_one
  | cons factor factors ih =>
      have hfactor_normalized :
          normalizeFactorSign factor = factor :=
        hnormalized factor (by simp)
      have hfactor_recorded :
          shouldRecordPolynomialFactor factor = true :=
        hrecorded factor (by simp)
      have hkeep :
          shouldRecordPolynomialFactor (normalizeFactorSign factor) = true := by
        rw [hfactor_normalized]
        exact hfactor_recorded
      rw [List.cons_append, filteredNormalizedFactors_cons_keep _ hkeep, hfactor_normalized]
      rw [ih
        (fun factor hmem => hnormalized factor (by simp [hmem]))
        (fun factor hmem => hrecorded factor (by simp [hmem]))]

private theorem polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized
    (factors : Array ZPoly)
    (hnormalized :
      ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true) :
    Array.polyProduct (filteredNormalizedFactors (factors ++ #[1]).toList).toArray =
      Array.polyProduct factors := by
  rw [Array.toList_append]
  change Array.polyProduct
      (filteredNormalizedFactors (factors.toList ++ [1])).toArray =
    Array.polyProduct factors
  rw [filteredNormalizedFactors_append_one_of_all_recorded_normalized
    factors.toList hnormalized hrecorded]

theorem factorTrialFactorsWithBound_polyProduct
    (f : ZPoly) (B : Nat) :
    DensePoly.C (signedContentScalar f) *
      Array.polyProduct (factorTrialFactorsWithBound f B) = f := by
  unfold factorTrialFactorsWithBound
  by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · simp only [hdeg, if_true]
    exact reassemblePolynomialFactors_product_eq_input f
      #[(normalizeForFactor f).squareFreeCore] (by simp [Array.polyProduct])
  · simp only [hdeg, if_false]
    cases hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        exact reassemblePolynomialFactors_product_eq_input f coreFactors
          (quadraticIntegerRootFactors?_product hquad)
    | none =>
        exact reassemblePolynomialFactors_product_eq_input f
          (exhaustiveIntegerTrialCoreFactorsWithBound
            (normalizeForFactor f).squareFreeCore B)
          (exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct
            (normalizeForFactor f).squareFreeCore B)

/-- Every member of a primitive ordered array product is itself primitive: each
member divides the product (`dvd_polyProduct_toArray_of_mem`), and a left
divisor of a primitive `ZPoly` is primitive (`ZPoly_primitive_left_of_mul`). -/
private theorem polyProduct_mem_primitive_of_primitive
    (factors : Array ZPoly)
    (h : ZPoly.Primitive (Array.polyProduct factors)) :
    ∀ g ∈ factors.toList, ZPoly.Primitive g := by
  intro g hg
  obtain ⟨c, hc⟩ := dvd_polyProduct_toArray_of_mem factors.toList hg
  rw [show factors.toList.toArray = factors from by simp] at hc
  rw [hc] at h
  exact ZPoly_primitive_left_of_mul g c h

/-- A product reconstructing a nonzero `f` from its signed content scalar is
primitive. Content is multiplicative, so `content f = content f * content P`
(the scalar constant has content `content f`); `content f ≠ 0` then forces
`content P = 1`. -/
private theorem primitive_of_signedContentScalar_mul_eq
    (f P : ZPoly) (hf : f ≠ 0)
    (h : DensePoly.C (signedContentScalar f) * P = f) :
    ZPoly.Primitive P := by
  have hnonneg : (0 : Int) ≤ ZPoly.content f := by
    show 0 ≤ DensePoly.content f
    rw [DensePoly.content]
    exact Int.natCast_nonneg _
  have hcontent_ne : ZPoly.content f ≠ 0 := by
    intro hc
    apply hf
    have hr := ZPoly.content_mul_primitivePart f
    rw [hc, DensePoly.scale_zero_left_semiring] at hr
    exact hr.symm
  have hCc : ZPoly.content (DensePoly.C (signedContentScalar f)) = ZPoly.content f := by
    have h1 : ZPoly.content (DensePoly.C (signedContentScalar f))
        = Int.ofNat (signedContentScalar f).natAbs := DensePoly.content_C _
    rw [h1]
    have hnat : (signedContentScalar f).natAbs = (ZPoly.content f).natAbs := by
      unfold signedContentScalar
      rw [if_neg hf]
      by_cases hl : DensePoly.leadingCoeff f < 0
      · rw [if_pos hl, Int.natAbs_neg]
      · rw [if_neg hl]
    rw [hnat]
    exact Int.natAbs_of_nonneg hnonneg
  have key : ZPoly.content f = ZPoly.content f * ZPoly.content P := by
    have step : ZPoly.content (DensePoly.C (signedContentScalar f) * P)
        = ZPoly.content f * ZPoly.content P := by
      rw [ZPoly.content_mul, hCc]
    rw [h] at step
    exact step
  have hzero : ZPoly.content f * (ZPoly.content P - 1) = 0 := by
    rw [Int.mul_sub, Int.mul_one, ← key, Int.sub_self]
  rcases Int.mul_eq_zero.mp hzero with hc | hc
  · exact absurd hc hcontent_ne
  · show ZPoly.content P = 1
    omega

private theorem factorTrialWithBound_product_of_all_recorded_normalized
    (f : ZPoly) (B : Nat)
    (hnormalized :
      ∀ factor ∈ (factorTrialFactorsWithBound f B).toList,
        normalizeFactorSign factor = factor)
    (hrecorded :
      ∀ factor ∈ (factorTrialFactorsWithBound f B).toList,
        shouldRecordPolynomialFactor factor = true) :
    Factorization.product (factorTrialWithBound f B) = f := by
  unfold factorTrialWithBound
  exact
    factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
      f (factorTrialFactorsWithBound f B)
      (factorTrialFactorsWithBound_polyProduct f B) hnormalized hrecorded

private theorem factorTrialWithBound_product_of_constant_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hbranch : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0) :
    Factorization.product (factorTrialWithBound f B) = f := by
  unfold factorTrialWithBound factorTrialFactorsWithBound
  rw [if_pos hbranch]
  have hcore_one := squareFreeCore_eq_one_of_constant_of_ne_zero f hf hbranch
  rw [hcore_one]
  apply factorizationOfFactors_product_of_filtered_product
  · exact reassemblePolynomialFactors_product_eq_input f #[1] (by
      rw [ZPoly.polyProduct_singleton]
      exact hcore_one.symm)
  · rw [reassemblePolynomialFactors_singleton_one_eq]
    rw [polyProduct_filteredNormalizedFactors_append_one_of_all_recorded_normalized,
      ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
    exact (DensePoly.mul_one_right_poly (S := Int) _).symm
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_normalizeFactorSign_of_ne_zero
        f hf factor hmem
    · intro factor hmem
      exact polynomialNormalizationPrefixFactors_shouldRecord_of_ne_zero
        f hf factor hmem

private theorem factorTrialWithBound_product_of_quadratic_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (coreFactors : Array ZPoly)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore =
      some coreFactors) :
    Factorization.product (factorTrialWithBound f B) = f := by
  apply factorTrialWithBound_product_of_all_recorded_normalized
  · unfold factorTrialFactorsWithBound
    rw [if_neg hdeg, hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_normalizeFactorSign
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc
  · unfold factorTrialFactorsWithBound
    rw [if_neg hdeg, hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      coreFactors ?_ factor hmem
    intro c hc
    exact quadraticIntegerRootFactors?_shouldRecord
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) hquad c hc

private theorem factorTrialWithBound_product_of_trial_branch
    (f : ZPoly) (B : Nat)
    (hf : f ≠ 0)
    (hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hquad : quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore = none) :
    Factorization.product (factorTrialWithBound f B) = f := by
  apply factorTrialWithBound_product_of_all_recorded_normalized
  · unfold factorTrialFactorsWithBound
    rw [if_neg hdeg, hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero f hf
      (exhaustiveIntegerTrialCoreFactorsWithBound
        (normalizeForFactor f).squareFreeCore B)
      ?_ factor hmem
    intro c hc
    exact exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign
      (normalizeForFactor f).squareFreeCore B
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) c hc
  · unfold factorTrialFactorsWithBound
    rw [if_neg hdeg, hquad]
    intro factor hmem
    refine reassemblePolynomialFactors_shouldRecord_of_ne_zero f hf
      (exhaustiveIntegerTrialCoreFactorsWithBound
        (normalizeForFactor f).squareFreeCore B)
      ?_ factor hmem
    intro c hc
    exact exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord
      (normalizeForFactor f).squareFreeCore B
      (squareFreeCore_leadingCoeff_pos_of_ne_zero f hf) c hc

theorem factorTrialWithBound_product (f : ZPoly) (B : Nat) :
    Factorization.product (factorTrialWithBound f B) = f := by
  by_cases hf : f = 0
  · subst f
    unfold factorTrialWithBound
    exact factorizationOfFactors_product_of_zero (factorTrialFactorsWithBound 0 B)
  · by_cases hdeg : (normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · exact factorTrialWithBound_product_of_constant_branch f B hf hdeg
    · cases hquad :
        quadraticIntegerRootFactors? (normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          exact factorTrialWithBound_product_of_quadratic_branch
            f B hf hdeg coreFactors hquad
      | none =>
          exact factorTrialWithBound_product_of_trial_branch
            f B hf hdeg hquad

/-- Product contract for the public trial-division slow-path entry point. -/
theorem factorTrial_product (f : ZPoly) :
    Factorization.product (factorTrial f) = f := by
  exact factorTrialWithBound_product f (ZPoly.defaultFactorCoeffBound f)

/-- Product contract for the public total factorization entry point. Holds
unconditionally: each non-backstop tier's result is accepted only when it
reconstructs `f` (the self-certifying guard in `factorTraced`), and every
fallback is the proven `factorTrial` backstop. Established without proving the
classical recombination loop reconstructs (that, with per-factor irreducibility,
is the still-blocked re-proof capstone #8384). -/
theorem factorize_product (f : ZPoly) :
    Factorization.product (ZPoly.factorize f) = f := by
  unfold ZPoly.factorize factorTraced
  rcases hcl : factorClassicalTraced f with ⟨cres, trace⟩
  cases cres with
  | some φ =>
      by_cases hp : Factorization.product φ = f
      · simp [hp]
      · simp only [hp, if_false]; exact factorTrial_product f
  | none =>
      cases hl : factorLattice f with
      | some φ =>
          by_cases hp : Factorization.product φ = f
          · simp [hp]
          · simp only [hp, if_false]; exact factorTrial_product f
      | none => exact factorTrial_product f

/-- Every recorded entry of the default factorization of a nonzero `f` is
primitive, with no raw-source hypothesis. The hybrid's `factorizationOfFactors`
packing certifies the *filtered* product reconstructs `f`
(`factorize_product` + `factorizationOfFactors_product`), so that product is
primitive and hence so is every recorded (filtered) entry. -/
theorem factorize_entries_primitive_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    ∀ entry ∈ (ZPoly.factorize f).factors, ZPoly.Primitive entry.1 := by
  intro entry hentry
  have hmem : entry ∈ (ZPoly.factorize f).factors.toList := Array.mem_toList_iff.mpr hentry
  -- The filtered product reconstructs `f`, hence is primitive.
  have hfiltered_prod :
      DensePoly.C (signedContentScalar f) *
        Array.polyProduct
          (filteredNormalizedFactors (factorFactors f).toList).toArray = f := by
    have hp := factorize_product f
    rw [factorize_eq_factorizationOfFactors, factorizationOfFactors_product] at hp
    exact hp
  have hprim :
      ZPoly.Primitive
        (Array.polyProduct
          (filteredNormalizedFactors (factorFactors f).toList).toArray) :=
    primitive_of_signedContentScalar_mul_eq f _ hf hfiltered_prod
  have hmem_filtered :
      ∀ g ∈ (filteredNormalizedFactors (factorFactors f).toList).toArray.toList,
        ZPoly.Primitive g :=
    polyProduct_mem_primitive_of_primitive _ hprim
  -- The entry lies in the filtered list (it equals a sign-normalized raw factor
  -- and passes the recording filter).
  obtain ⟨raw, hraw_mem, hentry_eq⟩ := factorize_entry_mem_raw_source f entry hmem
  have hrecord : shouldRecordPolynomialFactor (normalizeFactorSign raw) = true := by
    have := factorize_entry_shouldRecord f entry hmem
    rwa [hentry_eq] at this
  have hentry_in :
      entry.1 ∈ (filteredNormalizedFactors (factorFactors f).toList).toArray.toList := by
    rw [List.toList_toArray, hentry_eq]
    unfold filteredNormalizedFactors
    rw [List.mem_filterMap]
    exact ⟨raw, hraw_mem, by simp only [hrecord, if_true]⟩
  exact hmem_filtered entry.1 hentry_in

/--
A successful integer certificate exposes the per-prime polynomial check fact:
every recorded `PrimeFactorData` block satisfies `checkForPolynomial f` —
admissible prime, positive recorded factor degrees, modular degree-sum and
factor-product alignment, and aligned nested Rabin certificates. Callers
extract individual conjuncts via the dedicated helpers below.
-/
theorem checkIrreducibleCert_prime_data
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkForPolynomial f = true := by
  simp [checkIrreducibleCert] at hcert
  intro primeData hmem
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hget⟩
  have hiArray : i < cert.perPrime.size := by
    simpa using hi
  have hgetArray : cert.perPrime[i] = primeData := by
    simpa [Array.getElem_toList] using hget
  simpa [hgetArray] using hcert.1 i hiArray

/--
A successful integer certificate exposes the per-prime good-prime fact: every
recorded `PrimeFactorData` uses an admissible prime for `f` (size, leading
coefficient, and modular square-freeness all satisfied).
-/
theorem checkIrreducibleCert_isGoodPrime
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      isGoodPrime f primeData.p = true := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.1.1

/--
A successful integer certificate exposes positivity of every recorded modular
factor degree: each per-prime block's `factorDegrees` array contains only
positive entries.
-/
theorem checkIrreducibleCert_factorDegrees_positive
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      ∀ (i : Nat) (hi : i < primeData.factorDegrees.size),
        0 < primeData.factorDegrees[i] := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.1.2

/--
A successful integer certificate exposes the per-prime modular degree-sum
alignment: each block's recorded `degreeSum` equals the degree of the
polynomial's modular image.
-/
theorem checkIrreducibleCert_degreeSum_eq
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      primeData.degreeSum = (ZPoly.modP primeData.p f).degree?.getD 0 := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.1.2

/--
A successful integer certificate exposes the per-prime modular factor product
alignment: each block's recorded `factorProduct` equals the polynomial's
modular image.
-/
theorem checkIrreducibleCert_factorProduct_eq
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      letI := primeData.bounds
      primeData.factorProduct = ZPoly.modP primeData.p f := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.1.2

/--
A successful integer certificate exposes the per-prime nested Rabin checks:
`checkFactorCerts` validates the concrete modular factor array, the recorded
degrees, and the upstream `Berlekamp.checkIrreducibilityCertificate` result for
each aligned entry.
-/
theorem checkIrreducibleCert_certificate_alignment
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkFactorCerts = true := by
  intro primeData hmem
  have hcheck := checkIrreducibleCert_prime_data f cert hcert primeData hmem
  simp [PrimeFactorData.checkForPolynomial] at hcheck
  exact hcheck.2

/--
A successful integer certificate satisfies the top-level degree-obstruction
check: every recorded `DegreeObstruction` is valid for the certificate, and
every nontrivial candidate factor degree of `f` has at least one obstruction.
-/
theorem checkIrreducibleCert_degree_obstructions
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    cert.checkDegreeObstructions f = true := by
  simp [checkIrreducibleCert] at hcert
  exact hcert.2

/--
A successful integer certificate provides a valid obstruction for every
nontrivial candidate factor degree of `f` (the degrees `1, …, (deg f) / 2`),
ruling out an integer factorization at any of those degrees.
-/
theorem checkIrreducibleCert_obstructs_candidate_degrees
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f,
      cert.hasObstructionFor f targetDegree = true := by
  intro targetDegree hmem
  have hobs := checkIrreducibleCert_degree_obstructions f cert hcert
  simp [ZPolyIrreducibilityCertificate.checkDegreeObstructions] at hobs
  exact hobs.2 targetDegree hmem

/--
A valid `DegreeObstruction` exposes the underlying no-subset-sum fact: the
referenced per-prime block has no subset of its modular factor degrees summing
to the obstruction's `targetDegree`.
-/
theorem degreeObstruction_no_subset_degree
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) (primeData : PrimeFactorData)
    (hobs : obs.checkForCertificate f cert = true)
    (hprime : cert.primeDataAt? obs.primeIndex = some primeData) :
    primeData.hasSubsetDegree obs.targetDegree = false := by
  simp [DegreeObstruction.checkForCertificate, hprime] at hobs
  exact hobs.2

end Hex
