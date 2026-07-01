/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

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
  intro entry hentry
  by_cases hf : f = 0
  · subst hf
    rw [Hex.factor_zero_factors] at hentry
    simp at hentry
  · have hmem : entry ∈ (Hex.factor f).factors.toList := Array.mem_toList_iff.mpr hentry
    obtain ⟨raw, hraw_mem, hentry_eq⟩ := Hex.factor_entry_mem_raw_source f entry hmem
    have hrec := Hex.factor_entry_shouldRecord f entry hmem
    rw [hentry_eq] at hrec ⊢
    exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
      (factorHybridFactors_factor_irreducible f hf hraw_mem hrec)

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
Every polynomial factor emitted by the default executable factorization has
positive leading coefficient.
-/
theorem factor_entries_leadingCoeff_pos (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors,
      0 < Hex.DensePoly.leadingCoeff entry.1 := by
  intro entry hentry
  exact Hex.factor_entry_leadingCoeff_pos f entry (Array.mem_toList_iff.mpr hentry)

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
Positive-leading-coefficient sibling of `factor_headline_contract_core`.

This keeps the existing default public factorization clauses and additionally
packages the canonical positive-leading convention for every recorded
polynomial factor.
-/
theorem factor_headline_contract_core_with_posLeading (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.factor f) = f ∧
      (∀ entry ∈ (Hex.factor f).factors,
        Irreducible (HexPolyZMathlib.toPolynomial entry.1)) ∧
      (∀ entry ∈ (Hex.factor f).factors,
        0 < Hex.DensePoly.leadingCoeff entry.1) ∧
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
  rcases factor_headline_contract_core f with
    ⟨hproduct, hirreducible, hmultiplicity, hpairwise, hscalar⟩
  exact
    ⟨hproduct, hirreducible, factor_entries_leadingCoeff_pos f, hmultiplicity,
      hpairwise, hscalar⟩

/--
Primitive-strengthened sibling of `factor_headline_contract_core`.

This is the same default public factorization contract, but packages the
headline primitive-irreducibility clause as a single per-entry conjunction under
the raw-branch primitive hypothesis supplied by the executable layer.
-/
theorem factor_headline_contract_core_with_primitive
    (f : Hex.ZPoly) (hf : f ≠ 0) :
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
      ⟨factor_entries_primitive_of_chosen_raw_primitive f hf entry hentry,
        factor_polynomialIrreducible_of_nonUnit f entry hentry⟩
  · intro entry hentry
    exact Hex.factor_entry_multiplicity_pos f entry (Array.mem_toList_iff.mpr hentry)

/--
Closed primitive-strengthened headline for the default executable factorization
of a nonzero input.

This is the same bundle as `factor_headline_contract_core_with_primitive` but
with the raw-source primitivity hypothesis `h_raw` discharged internally via
`Hex.factor_chosen_raw_primitive_of_ne_zero`, so callers no longer supply it:
product preservation, primitive plus Mathlib irreducibility per recorded factor,
positive multiplicities, the syntactic distinct-key clause, and the
signed-content scalar convention.

The `f ≠ 0` side condition is essential rather than incidental. For `f = 0` the
square-free core is `0` (content `0`, hence not primitive), so the raw-source
primitivity statement quantified over the dispatch is literally false; the
factorization of `0` is itself degenerate (`scalar = 0`, product `0`).
-/
theorem factor_headline_primitive (f : Hex.ZPoly) (hf : f ≠ 0) :
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
          Hex.ZPoly.content f :=
  factor_headline_contract_core_with_primitive f hf

/--
The HO-1 headline contract for the default executable factorization of a nonzero
input.

This is the strengthened public surface required by directive #2564: it is the
same bundle as `factor_headline_primitive` but replaces the syntactic
distinct-key clause `a.1 ≠ b.1` with genuine pairwise non-association after
transport to `Polynomial ℤ`. The clauses are product preservation, primitive
plus Mathlib irreducibility per recorded factor, positive multiplicities,
pairwise non-association of the recorded polynomial factors, and the
signed-content scalar convention.

Non-association is the headline strengthening: distinct `ZPoly` keys could in
principle be associated in `Polynomial ℤ` (differ by a unit); this rules that
out, so the recorded factors are genuinely distinct irreducibles up to
association. The clause is discharged via `factor_entries_not_associated` with
the raw-source primitivity hypothesis supplied internally by
`Hex.factor_chosen_raw_primitive_of_ne_zero`, which is why `f ≠ 0` is required
(see `factor_headline_primitive` for why the `f = 0` case is degenerate).
-/
theorem factor_headline (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.Factorization.product (Hex.factor f) = f ∧
      (∀ entry ∈ (Hex.factor f).factors,
        Hex.ZPoly.Primitive entry.1 ∧
          Irreducible (HexPolyZMathlib.toPolynomial entry.1)) ∧
      (∀ entry ∈ (Hex.factor f).factors, 0 < entry.2) ∧
      List.Pairwise
        (fun a b : Hex.ZPoly × Nat =>
          ¬ Associated (HexPolyZMathlib.toPolynomial a.1)
            (HexPolyZMathlib.toPolynomial b.1))
        (Hex.factor f).factors.toList ∧
      (Hex.factor f).scalar =
        if f = 0 then
          0
        else if Hex.DensePoly.leadingCoeff f < 0 then
          -Hex.ZPoly.content f
        else
          Hex.ZPoly.content f := by
  rcases factor_headline_primitive f hf with
    ⟨hproduct, hentries, hmultiplicity, _, hscalar⟩
  exact
    ⟨hproduct, hentries, hmultiplicity,
      factor_entries_not_associated f hf,
      hscalar⟩

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
`f ≠ 0` side condition that `Hex.factor_entries_primitive_of_ne_zero` needs
(the self-certifying hybrid, #8383). The constant-exclusion argument itself is
`Hex.degree_pos_of_primitive_norm_record`.
-/
theorem factor_entries_degree_pos
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ entry ∈ (Hex.factor f).factors, 0 < entry.1.degree?.getD 0 := by
  intro entry hentry
  have hmem := Array.mem_toList_iff.mpr hentry
  exact Hex.degree_pos_of_primitive_norm_record entry.1
    (Hex.factor_entries_primitive_of_ne_zero f hf entry hentry)
    (Hex.factor_entry_normalizeFactorSign_id f entry hmem)
    (Hex.factor_entry_shouldRecord f entry hmem)

/--
Uniqueness specialised against the default executable factorization, so callers
only provide the competing product, irreducibility, sign-normalization, and
nonconstant-factor facts, plus that the input is nonzero. The default
factorization's own well-formedness is supplied by
`factor_irreducible_of_nonUnit` and its sibling lemmas.
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
nonconstant clause needs only `f ≠ 0` (the same `hf_ne` already supplied), via
`factor_entries_degree_pos`; `hψ_norm` is discharged unconditionally.
-/
theorem factor_unique_of_product_default
    (f : Hex.ZPoly) (φ : Hex.Factorization) (hf_ne : f ≠ 0)
    (hproduct : Hex.Factorization.product φ = f)
    (hφ_norm : ∀ entry ∈ φ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hφ_nonconst : ∀ entry ∈ φ.factors, 0 < entry.1.degree?.getD 0)
    (hirr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1) :
    φ.scalar = (Hex.factor f).scalar ∧
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum =
        ((Hex.factor f).factors.toList.map
          (fun e => Multiset.replicate e.2 e.1)).sum :=
  factor_unique_of_product f φ hf_ne hproduct hφ_norm
    (factor_entries_normalizeFactorSign f) hφ_nonconst
    (factor_entries_degree_pos f hf_ne) hirr


end

end HexBerlekampZassenhausMathlib
