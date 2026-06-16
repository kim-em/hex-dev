import HexBerlekampZassenhausMathlib.IntReductionMod

/-!
Public factorization soundness surface that needs the post-`IntReductionMod`
branch umbrellas.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
Every polynomial factor emitted by the default executable factorization is
irreducible in the executable `Hex.ZPoly` sense.
-/
theorem factor_irreducible_of_nonUnit (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors, Hex.ZPoly.Irreducible entry.1 := by
  sorry

/--
Every polynomial factor emitted by the default executable factorization is
irreducible after transport to `Polynomial ℤ`.
-/
theorem factor_polynomialIrreducible_of_nonUnit (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors,
      Irreducible (HexPolyZMathlib.toPolynomial entry.1) := by
  intro entry hentry
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible entry.1).mp
      (factor_irreducible_of_nonUnit f entry hentry)

/--
Bundled public contract currently available for the default executable
factorization surface.

This packages the clauses that are already exposed by the Mathlib-free and
Mathlib bridge layers: product preservation, Mathlib irreducibility of each
recorded polynomial factor, positive multiplicities, syntactic absence of
duplicate polynomial keys, and the signed-content scalar convention. The
remaining HO-1 headline strengthening is to replace the syntactic distinct-key
clause with non-association and to add the primitive-factor clause.
-/
theorem factor_headline_contract_core (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.factor f) = f ∧
      (∀ entry ∈ (Hex.factor f).factors,
        Irreducible (HexPolyZMathlib.toPolynomial entry.1)) ∧
      (∀ entry ∈ (Hex.factor f).factors, 0 < entry.2) ∧
      List.Pairwise (fun a b : Hex.ZPoly × Nat => a.1 ≠ b.1)
        (Hex.factor f).factors.toList ∧
      (Hex.factor f).scalar =
        if f = 0 then
          0
        else if Hex.DensePoly.leadingCoeff f < 0 then
          -Hex.ZPoly.content f
        else
          Hex.ZPoly.content f := by
  refine ⟨factor_product f, ?_, ?_, Hex.factor_pairwise_first f, Hex.factor_scalar f⟩
  · intro entry hentry
    exact factor_polynomialIrreducible_of_nonUnit f entry hentry
  · intro entry hentry
    exact Hex.factor_entry_multiplicity_pos f entry (Array.mem_toList_iff.mpr hentry)

/--
Primitive-strengthened sibling of `factor_headline_contract_core`.

This is the same default public factorization contract, but packages the
headline primitive-irreducibility clause as a single per-entry conjunction under
the raw-branch primitive hypothesis supplied by the executable layer.
-/
theorem factor_headline_contract_core_with_primitive
    (f : Hex.ZPoly)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f) = some rawFactors) ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowTrialFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Primitive raw) :
    Hex.Factorization.product (Hex.factor f) = f ∧
      (∀ entry ∈ (Hex.factor f).factors,
        Hex.ZPoly.Primitive entry.1 ∧
          Irreducible (HexPolyZMathlib.toPolynomial entry.1)) ∧
      (∀ entry ∈ (Hex.factor f).factors, 0 < entry.2) ∧
      List.Pairwise (fun a b : Hex.ZPoly × Nat => a.1 ≠ b.1)
        (Hex.factor f).factors.toList ∧
      (Hex.factor f).scalar =
        if f = 0 then
          0
        else if Hex.DensePoly.leadingCoeff f < 0 then
          -Hex.ZPoly.content f
        else
          Hex.ZPoly.content f := by
  refine ⟨factor_product f, ?_, ?_, Hex.factor_pairwise_first f, Hex.factor_scalar f⟩
  · intro entry hentry
    exact
      ⟨factor_entries_primitive_of_chosen_raw_primitive f h_raw entry hentry,
        factor_polynomialIrreducible_of_nonUnit f entry hentry⟩
  · intro entry hentry
    exact Hex.factor_entry_multiplicity_pos f entry (Array.mem_toList_iff.mpr hentry)

/--
The sign-normalization side condition for the default executable factorization:
every recorded polynomial factor is fixed by `normalizeFactorSign`. This is the
`hψ_norm` clause that uniqueness/checker callers would otherwise reconstruct from
the executable `Hex.factor_entry_normalizeFactorSign_id`.
-/
theorem factor_entries_normalizeFactorSign (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors,
      Hex.normalizeFactorSign entry.1 = entry.1 := by
  intro entry hentry
  exact Hex.factor_entry_normalizeFactorSign_id f entry (Array.mem_toList_iff.mpr hentry)

/--
The nonconstant side condition for the default executable factorization: every
recorded polynomial factor has positive degree. This is the `hψ_nonconst` clause
uniqueness/checker callers would otherwise reconstruct.

Positive degree is *not* derivable from `shouldRecordPolynomialFactor` alone — a
constant like `Hex.DensePoly.C 2` passes the recording filter, has positive
leading coefficient, and is sign-normalized. The constant case is excluded by
*primitivity* (content `1` forces a constant to be `±1`), so this carries the
same raw-source primitivity hypothesis `h_raw` as `Hex.factor_entries_primitive`
and `factor_headline_contract_core_with_primitive`. The constant-exclusion
argument itself is `Hex.degree_pos_of_primitive_norm_record`.
-/
theorem factor_entries_degree_pos
    (f : Hex.ZPoly)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f) = some rawFactors) ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowTrialFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Primitive raw) :
    ∀ entry ∈ (Hex.factor f).factors, 0 < entry.1.degree?.getD 0 := by
  intro entry hentry
  have hmem := Array.mem_toList_iff.mpr hentry
  exact Hex.degree_pos_of_primitive_norm_record entry.1
    (Hex.factor_entries_primitive f h_raw entry hentry)
    (Hex.factor_entry_normalizeFactorSign_id f entry hmem)
    (Hex.factor_entry_shouldRecord f entry hmem)

/--
Uniqueness specialised against the default executable factorization, so callers
only provide the competing product, irreducibility, sign-normalization, and
nonconstant-factor facts, plus that the input is nonzero. The default
factorization's own well-formedness is supplied by
`factor_irreducible_of_nonUnit` and forthcoming sibling lemmas.
-/
theorem factor_unique_of_product
    (f : Hex.ZPoly) (φ : Hex.Factorization) (hf_ne : f ≠ 0)
    (hproduct : Hex.Factorization.product φ = f)
    (hφ_norm : ∀ entry ∈ φ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hψ_norm : ∀ entry ∈ (Hex.factor f).factors,
      Hex.normalizeFactorSign entry.1 = entry.1)
    (hφ_nonconst : ∀ entry ∈ φ.factors, 0 < entry.1.degree?.getD 0)
    (hψ_nonconst : ∀ entry ∈ (Hex.factor f).factors,
      0 < entry.1.degree?.getD 0)
    (hirr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1) :
    φ.scalar = (Hex.factor f).scalar ∧
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum =
        ((Hex.factor f).factors.toList.map
          (fun e => Multiset.replicate e.2 e.1)).sum :=
  factor_unique φ (Hex.factor f) hφ_norm hψ_norm hφ_nonconst hψ_nonconst hirr
    (factor_irreducible_of_nonUnit f)
    (by rw [hproduct]; exact hf_ne)
    (by rw [hproduct, factor_product f])

/--
Default-specialised sibling of `factor_unique_of_product` that discharges the
default factorization's own sign-normalization and nonconstant side conditions
internally, so callers no longer supply `hψ_norm` or `hψ_nonconst`. The
nonconstant clause needs the raw-source primitivity hypothesis `h_raw` (the same
hypothesis `factor_entries_degree_pos` and `Hex.factor_entries_primitive`
require); `hψ_norm` is discharged unconditionally.
-/
theorem factor_unique_of_product_default
    (f : Hex.ZPoly) (φ : Hex.Factorization) (hf_ne : f ≠ 0)
    (hproduct : Hex.Factorization.product φ = f)
    (hφ_norm : ∀ entry ∈ φ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hφ_nonconst : ∀ entry ∈ φ.factors, 0 < entry.1.degree?.getD 0)
    (hirr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f) = some rawFactors) ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            Hex.factorSlowModularWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowTrialFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Primitive raw) :
    φ.scalar = (Hex.factor f).scalar ∧
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum =
        ((Hex.factor f).factors.toList.map
          (fun e => Multiset.replicate e.2 e.1)).sum :=
  factor_unique_of_product f φ hf_ne hproduct hφ_norm
    (factor_entries_normalizeFactorSign f) hφ_nonconst
    (factor_entries_degree_pos f h_raw) hirr

end

end HexBerlekampZassenhausMathlib
