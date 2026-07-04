/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhausMathlib.IntReductionMod
import HexBerlekampZassenhausMathlib.LatticeTier

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
      (factorFactors_factor_irreducible f hf hraw_mem hrec)

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

set_option maxHeartbeats 1000000 in
/--
The executable irreducibility checker `Hex.ZPoly.isIrreducible` agrees with the
`Hex.ZPoly.Irreducible` class.

`isIrreducible` runs `factor` and checks the result is a single primitive factor
of multiplicity 1 (with a `±1` scalar), so this is exactly the statement that the
default factorization is a correct irreducible factorization.  The degree-0
(constant) arm is the elementary-primality characterisation
(`irreducible_C_of_isNatPrime` / `isNatPrime_natAbs_of_irreducible_C`); the
positive-degree arm composes `factor_irreducible_of_nonUnit` (forward) with
`factor_unique_of_product_default` (backward, which pins the factor count to the
`normalizedFactors` cardinality).  It therefore inherits the lattice-tier `sorry`
of `factor_irreducible_of_nonUnit` (#8417) and nothing else.
-/
theorem Hex.ZPoly.isIrreducible_iff (f : Hex.ZPoly) :
    Hex.ZPoly.isIrreducible f = true ↔ Hex.ZPoly.Irreducible f := by
  rw [Hex.ZPoly.isIrreducible]
  by_cases hf0 : f = 0
  · subst hf0
    rw [if_pos rfl]
    exact ⟨fun h => absurd h (by decide), fun h => absurd rfl h.not_zero⟩
  · rw [if_neg hf0]
    by_cases hdeg : f.degree?.getD 0 = 0
    · -- constant arm
      rw [if_pos hdeg]
      have hsize_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero f hf0
      have hsize1 : f.size = 1 := by
        have hdeg_eq : f.degree?.getD 0 = f.size - 1 := by
          unfold Hex.DensePoly.degree?
          simp [Nat.ne_of_gt hsize_pos]
        omega
      have hfC : f = Hex.DensePoly.C (f.coeff 0) := Hex.ZPoly.eq_C_of_size_eq_one f hsize1
      have hk_ne : f.coeff 0 ≠ 0 := by
        intro h0
        apply hf0
        rw [hfC, h0]; rfl
      constructor
      · intro h
        rw [hfC]
        exact Hex.ZPoly.irreducible_C_of_isNatPrime h
      · intro h
        rw [hfC] at h
        exact Hex.ZPoly.isNatPrime_natAbs_of_irreducible_C hk_ne h
    · -- positive-degree arm
      rw [if_neg hdeg]
      set φ := Hex.factor f with hφ_def
      have hprod : Hex.Factorization.product φ = f := Hex.factor_product f
      have hfp1 : ∀ q : Hex.ZPoly, Hex.Factorization.factorPower q 1 = q := fun q => by
        rw [show (1 : Nat) = 0 + 1 from rfl, Hex.Factorization.factorPower_succ,
          Hex.Factorization.factorPower_zero, Hex.ZPoly.one_mul_zpoly]
      rw [Hex.ZPoly.Irreducible_iff_polynomialIrreducible]
      constructor
      · -- forward: single factor + capstone irreducibility → Irreducible (toPolynomial f)
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨hscalar, hsize⟩, hmatch⟩ := h
        obtain ⟨entry, hentry_list⟩ :=
          List.length_eq_one_iff.mp (by rw [Array.length_toList]; exact hsize)
        have hentry_mem : entry ∈ φ.factors := by
          rw [← Array.mem_toList_iff, hentry_list]; exact List.mem_singleton.mpr rfl
        rw [hentry_list] at hmatch
        have hmult1 : entry.2 = 1 := by simpa using hmatch
        have hirr_entry : Hex.ZPoly.Irreducible entry.1 :=
          factor_irreducible_of_nonUnit f entry hentry_mem
        have hirr_P : Irreducible (HexPolyZMathlib.toPolynomial entry.1) :=
          (Hex.ZPoly.Irreducible_iff_polynomialIrreducible entry.1).mp hirr_entry
        -- product of a single (g, 1) entry is `C scalar * g`
        have hfoldl : φ.product = Hex.DensePoly.C φ.scalar * entry.1 := by
          rw [Hex.Factorization.product_eq_foldl_factorPower, ← Array.foldl_toList, hentry_list]
          simp only [List.foldl_cons, List.foldl_nil, hmult1, hfp1]
        have hf_eq : f = Hex.DensePoly.C φ.scalar * entry.1 := by rw [← hprod, hfoldl]
        -- transport to `Polynomial ℤ`; the `±1` scalar is a unit
        have hunit : IsUnit (Polynomial.C φ.scalar) := by
          have : φ.scalar = 1 ∨ φ.scalar = -1 := by
            rcases Int.natAbs_eq φ.scalar with he | he <;> omega
          rcases this with h1 | h1 <;> rw [h1] <;> simp
        have hPf : HexPolyZMathlib.toPolynomial f =
            Polynomial.C φ.scalar * HexPolyZMathlib.toPolynomial entry.1 := by
          rw [hf_eq, HexPolyZMathlib.toPolynomial_mul, HexPolyZMathlib.toPolynomial_C]
        rw [hPf]
        exact (irreducible_isUnit_mul hunit).mpr hirr_P
      · -- backward: uniqueness pins the factor to a single one of multiplicity 1
        intro hIrr
        have hIrr_f : Hex.ZPoly.Irreducible f :=
          (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mpr hIrr
        set g := Hex.normalizeFactorSign f with hg_def
        set s : Int := if Hex.DensePoly.leadingCoeff f < 0 then -1 else 1 with hs_def
        have hg_norm : Hex.normalizeFactorSign g = g := Hex.normalizeFactorSign_idem f
        have hg_irr : Hex.ZPoly.Irreducible g :=
          zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hIrr_f
        have hCs_g : Hex.DensePoly.C s * g = f := by
          rw [hg_def, hs_def, Hex.normalizeFactorSign]
          by_cases hlc : Hex.DensePoly.leadingCoeff f < 0
          · rw [if_pos hlc, if_pos hlc, Hex.ZPoly.C_mul_eq_scale, Hex.scale_neg_one_neg_one]
          · rw [if_neg hlc, if_neg hlc, Hex.ZPoly.C_mul_eq_scale, Hex.densePoly_int_scale_one]
        have hg_deg : 0 < g.degree?.getD 0 := by
          have : g.size = f.size := by
            rw [hg_def, Hex.normalizeFactorSign]
            by_cases hlc : Hex.DensePoly.leadingCoeff f < 0
            · rw [if_pos hlc]; exact Hex.ZPoly.scale_size_of_nonzero (-1) f (by norm_num)
            · rw [if_neg hlc]
          have hfsz : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero f hf0
          have hgeq : g.degree?.getD 0 = g.size - 1 := by
            unfold Hex.DensePoly.degree?; simp [Nat.ne_of_gt (this ▸ hfsz)]
          have hfeq : f.degree?.getD 0 = f.size - 1 := by
            unfold Hex.DensePoly.degree?; simp [Nat.ne_of_gt hfsz]
          omega
        set ψ : Hex.Factorization := { scalar := s, factors := #[(g, 1)] } with hψ_def
        have hψ_prod : Hex.Factorization.product ψ = f := by
          have hlist : ψ.factors.toList = [(g, 1)] := by simp [hψ_def]
          rw [Hex.Factorization.product_eq_foldl_factorPower, ← Array.foldl_toList, hlist]
          simp only [hψ_def, List.foldl_cons, List.foldl_nil, hfp1]
          exact hCs_g
        have hψ_norm : ∀ entry ∈ ψ.factors, Hex.normalizeFactorSign entry.1 = entry.1 := by
          intro entry hmem
          simp only [hψ_def, Array.mem_singleton] at hmem
          rw [hmem]; exact hg_norm
        have hψ_nonconst : ∀ entry ∈ ψ.factors, 0 < entry.1.degree?.getD 0 := by
          intro entry hmem
          simp only [hψ_def, Array.mem_singleton] at hmem
          rw [hmem]; exact hg_deg
        have hψ_irr : ∀ entry ∈ ψ.factors, Hex.ZPoly.Irreducible entry.1 := by
          intro entry hmem
          simp only [hψ_def, Array.mem_singleton] at hmem
          rw [hmem]; exact hg_irr
        obtain ⟨hscalar_eq, hmulti_eq⟩ :=
          factor_unique_of_product_default f ψ hf0 hψ_prod hψ_norm hψ_nonconst hψ_irr
        -- the ψ multiset is the singleton {g}; take cardinalities
        have hψ_card : Multiset.card
            (ψ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum = 1 := by
          simp [hψ_def]
        rw [hmulti_eq] at hψ_card
        -- `card` of a sum of replicates is the sum of the multiplicities
        have hcard_eq : ∀ L : List (Hex.ZPoly × Nat),
            Multiset.card (L.map (fun e => Multiset.replicate e.2 e.1)).sum =
              (L.map (fun e => e.2)).sum := by
          intro L
          induction L with
          | nil => simp
          | cons hd tl ih =>
              simp only [List.map_cons, List.sum_cons, Multiset.card_add,
                Multiset.card_replicate, ih]
        have hcard_sum : (φ.factors.toList.map (fun e => e.2)).sum = 1 := by
          rw [← hcard_eq φ.factors.toList]; exact hψ_card
        -- every recorded multiplicity is positive
        have hmult_pos : ∀ x ∈ φ.factors.toList.map (fun e => e.2), 1 ≤ x := by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨e, he_mem, he_eq⟩ := hx
          rw [← he_eq]
          exact Hex.factor_entry_multiplicity_pos f e he_mem
        -- a list of positive naturals summing to `1` has length `1`
        have list_length_le_sum : ∀ (L : List Nat), (∀ x ∈ L, 1 ≤ x) → L.length ≤ L.sum := by
          intro L
          induction L with
          | nil => intro _; simp
          | cons hd tl ih =>
              intro hL
              simp only [List.length_cons, List.sum_cons]
              have h1 : 1 ≤ hd := hL hd (List.mem_cons.mpr (Or.inl rfl))
              have h2 := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
              omega
        have hlen1 : φ.factors.toList.length = 1 := by
          have hle : (φ.factors.toList.map (fun e => e.2)).length ≤ 1 := by
            rw [← hcard_sum]; exact list_length_le_sum _ hmult_pos
          rw [List.length_map] at hle
          have hge : 1 ≤ φ.factors.toList.length := by
            rcases Nat.eq_zero_or_pos φ.factors.toList.length with h0 | hpos
            · exfalso
              have hnil : φ.factors.toList = [] := List.eq_nil_of_length_eq_zero h0
              rw [hnil] at hcard_sum; simp at hcard_sum
            · exact hpos
          omega
        obtain ⟨entry, hentry_list⟩ := List.length_eq_one_iff.mp hlen1
        have hmult1 : entry.2 = 1 := by
          rw [hentry_list] at hcard_sum; simpa using hcard_sum
        have hsize1 : φ.factors.size = 1 := by rw [← Array.length_toList, hlen1]
        have hs_val : s = 1 ∨ s = -1 := by rw [hs_def]; split_ifs <;> simp
        have hscalar1 : φ.scalar.natAbs = 1 := by
          have hφs : φ.scalar = s := by rw [← hscalar_eq, hψ_def]
          rw [hφs]
          rcases hs_val with h | h <;> simp [h]
        -- assemble the Boolean check
        simp only [hentry_list, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨hscalar1, hsize1⟩, by simpa using hmult1⟩

instance Hex.ZPoly.instDecidableIrreducible (f : Hex.ZPoly) :
    Decidable (Hex.ZPoly.Irreducible f) :=
  decidable_of_iff _ (Hex.ZPoly.isIrreducible_iff f)

/--
The executable factorization predicate agrees with Mathlib irreducibility over
`Polynomial ℤ`.
-/
@[simp, grind =]
theorem irreducibleByFactorization_iff (f : Polynomial ℤ) :
    irreducibleByFactorization f = true ↔ Irreducible f := by
  rw [irreducibleByFactorization]
  constructor
  · intro h
    have hhex :
        Hex.ZPoly.Irreducible (HexPolyZMathlib.ofPolynomial f) :=
      (Hex.ZPoly.isIrreducible_iff _).mp h
    simpa [HexPolyZMathlib.toPolynomial_ofPolynomial] using
      (Hex.ZPoly.Irreducible_iff_polynomialIrreducible
        (HexPolyZMathlib.ofPolynomial f)).mp hhex
  · intro h
    exact (Hex.ZPoly.isIrreducible_iff _).mpr <|
      (Hex.ZPoly.Irreducible_iff_polynomialIrreducible
        (HexPolyZMathlib.ofPolynomial f)).mpr <| by
          simpa [HexPolyZMathlib.toPolynomial_ofPolynomial] using h

/--
Mathlib irreducibility over `Polynomial ℤ` is decidable through the executable
Berlekamp-Zassenhaus factorization surface.
-/
instance irreducibleDecidablePred :
    DecidablePred (fun f : Polynomial ℤ => Irreducible f) :=
  fun f =>
    if h : irreducibleByFactorization f = true then
      isTrue ((irreducibleByFactorization_iff f).mp h)
    else
      isFalse (fun hf => h ((irreducibleByFactorization_iff f).mpr hf))


end

end HexBerlekampZassenhausMathlib
