module

public import HexBerlekampZassenhausMathlib.IntReductionMod

public section

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
  factor_headline_contract_core_with_primitive f
    (Hex.factor_chosen_raw_primitive_of_ne_zero f hf)

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
      factor_entries_not_associated f
        (Hex.factor_chosen_raw_primitive_of_ne_zero f hf),
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

/-!
### HO-1 capstone assembly: `factor_irreducible_of_nonUnit` reduced to the fast-core arm

The default-factor irreducibility capstone `factor_irreducible_of_nonUnit`
reduces, via `factor_entries_irreducible`, to the guarded raw-source
irreducibility hypothesis `h_raw` over the three-way fast/slow dispatch.  Every
branch of `h_raw` is discharged by an existing per-branch producer **except the
fast BHKS core-success arm**, whose only routes
(`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut` and friends in
`PartitionRefinement.lean`) require a `BHKS.CutProjectionHypotheses` /
`RecoveredAtLiftM1` recovery certificate that no theorem produces from the bare
loop success `factorFastCoreWithBound … = some coreFactors` (see the issue
diagnosis).

`factor_irreducible_of_nonUnit_of_fastCore` below isolates exactly that arm: it
takes the single hypothesis "fast-core loop success implies every emitted core
factor is irreducible" and discharges *all* other branches (constant, small-mod
singleton, quadratic, slow-modular, slow-trial) from the landed producers.  This
pins the remaining capstone obligation to one clean, recovery-witness-free,
basis-free statement.

The cut-free completeness helper `fastCoreReassemblyComplete_of_coreIrreducible`
lives in `IntReductionMod.lean` (it needs that file's private `factorPower`/`foldl`
divisibility helpers). -/

/--
Guarded raw-factor irreducibility for the fast BHKS core-success branch from the
emitted-factor irreducibility `hcore_irr`.

The dispatcher returns `reassemblePolynomialFactors (normalizeForFactor f)
coreFactors` (`factorFastFactorsWithBound_eq_some_of_core_success`); the
reassembly is expansion-complete by `fastCoreReassemblyComplete_of_coreIrreducible`,
so every raw factor is irreducible by the Mathlib-free reassembly lift.  The
`shouldRecord` guard is therefore not even consumed.
-/
theorem fastCoreRawGuarded_of_coreIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (hB_pos : 1 ≤ B)
    (primeData : Hex.PrimeChoiceData)
    (hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hnotsingleton : ¬ primeData.factorsModP.size ≤ 1)
    (hquadratic :
      B = 1 ∨
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore = none)
    {coreFactors : Array Hex.ZPoly}
    (hcore :
      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) = some coreFactors)
    (hcore_irr : ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor)
    {rawFactors : Array Hex.ZPoly}
    (hfast : Hex.factorFastFactorsWithBound f B = some rawFactors) :
    ∀ raw ∈ rawFactors.toList,
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true →
        Hex.ZPoly.Irreducible raw := by
  have hfast_eq :=
    Hex.factorFastFactorsWithBound_eq_some_of_core_success f B primeData
      coreFactors hB_pos hchoose hdeg hnotsingleton hquadratic hcore
  rw [hfast] at hfast_eq
  have hraw_eq := Option.some.inj hfast_eq
  have hcomplete :=
    fastCoreReassemblyComplete_of_coreIrreducible f hf_ne B primeData hcore hcore_irr
  intro raw hmem _hrecord
  rw [hraw_eq] at hmem
  exact
    Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      (Hex.normalizeForFactor f) coreFactors hcomplete hcore_irr hmem

/--
**HO-1 capstone reduced to the fast-core arm.**

Every polynomial factor emitted by the default executable factorization of a
nonzero input is irreducible, **given** the single hypothesis `h_fastcore`: if
the chosen prime selects `primeData` and the fast BHKS core loop succeeds, then
every emitted core factor is irreducible.

All other branches of the raw-source dispatch are discharged from landed
producers: the constant early-return
(`Hex.factorFastFactorsWithBound_raw_irreducible_of_constant`), the small-mod
singleton (`factorFastFactorsWithBound_raw_guardedIrreducible_of_smallModSingleton`),
the quadratic short-circuit (`factorFastFactorsWithBound_raw_irreducible_of_quadratic`),
the slow-modular fallback (`slowModularRaw_irreducible_of_fast_none`), and the
slow-trial fallback (`factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none`).

`h_fastcore` is precisely the conclusion of
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`
(`PartitionRefinement.lean`) — discharging it from bare loop success is the one
remaining capstone obligation (it needs a forward-cut / `RecoveredAtLiftM1`
recovery certificate that no producer currently supplies from
`factorFastCoreWithBound … = some coreFactors`).
-/
theorem factor_irreducible_of_nonUnit_of_fastCore
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (h_fastcore :
      ∀ (primeData : Hex.PrimeChoiceData) (coreFactors : Array Hex.ZPoly),
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
          some primeData →
        Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f) primeData
            (Hex.initialHenselPrecision (Hex.ZPoly.defaultFactorCoeffBound f))
            (Hex.ZPoly.quadraticDoublingSteps
              (Hex.ZPoly.defaultFactorCoeffBound f) + 2) =
          some coreFactors →
        ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor) :
    ∀ entry ∈ (Hex.factor f).factors, Hex.ZPoly.Irreducible entry.1 := by
  have hB_pos : 1 ≤ Hex.ZPoly.defaultFactorCoeffBound f :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf
  apply factor_entries_irreducible f
  intro rawFactors hsource raw hmem hrecord
  rcases hsource with hfast | ⟨hfastnone, hmod⟩ | ⟨hfastnone, _hmodnone, htrial⟩
  · -- Fast path: `factorFastFactorsWithBound = some rawFactors`.
    by_cases hdeg0 :
        (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · -- (a) constant early-return.
      exact Hex.factorFastFactorsWithBound_raw_irreducible_of_constant f hf
        (Hex.ZPoly.defaultFactorCoeffBound f) hdeg0 hfast raw hmem hrecord
    · by_cases hB1 : Hex.ZPoly.defaultFactorCoeffBound f = 1
      · -- B = 1: dispatch on `choosePrimeData?` and the singleton predicate.
        cases hchoose :
            Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore with
        | none =>
            exfalso
            have hnone : Hex.factorFastFactorsWithBound f
                (Hex.ZPoly.defaultFactorCoeffBound f) = none := by
              unfold Hex.factorFastFactorsWithBound
              rw [if_neg hdeg0,
                if_neg (by omega : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0),
                if_pos hB1]
              simp [hchoose]
            rw [hnone] at hfast
            simp at hfast
        | some primeData =>
            by_cases hsmall : primeData.factorsModP.size ≤ 1
            · -- (c) small-mod singleton.
              exact factorFastFactorsWithBound_raw_guardedIrreducible_of_smallModSingleton
                f hf (Hex.ZPoly.defaultFactorCoeffBound f) hB_pos primeData hdeg0
                hchoose hsmall (Or.inl hB1) hfast raw hmem hrecord
            · cases hcore :
                  Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore
                    (Hex.ZPoly.defaultFactorCoeffBound f) primeData
                    (Hex.initialHenselPrecision (Hex.ZPoly.defaultFactorCoeffBound f))
                    (Hex.ZPoly.quadraticDoublingSteps
                      (Hex.ZPoly.defaultFactorCoeffBound f) + 2) with
              | none =>
                  exfalso
                  have hnone : Hex.factorFastFactorsWithBound f
                      (Hex.ZPoly.defaultFactorCoeffBound f) = none := by
                    unfold Hex.factorFastFactorsWithBound
                    rw [if_neg hdeg0,
                      if_neg (by omega : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0),
                      if_pos hB1]
                    simp [hchoose, hsmall, hcore]
                  rw [hnone] at hfast
                  simp at hfast
              | some coreFactors =>
                  -- (d) fast-core success — the isolated arm.
                  exact fastCoreRawGuarded_of_coreIrreducible f hf
                    (Hex.ZPoly.defaultFactorCoeffBound f) hB_pos primeData hdeg0
                    hchoose hsmall (Or.inl hB1) hcore
                    (h_fastcore primeData coreFactors hchoose hcore) hfast raw hmem hrecord
      · -- B > 1.
        have hBgt : 1 < Hex.ZPoly.defaultFactorCoeffBound f := by omega
        cases hquad :
            Hex.quadraticIntegerRootFactors?
              (Hex.normalizeForFactor f).squareFreeCore with
        | some coreFactors =>
            -- (f) quadratic short-circuit.
            exact factorFastFactorsWithBound_raw_irreducible_of_quadratic f hf
              (Hex.ZPoly.defaultFactorCoeffBound f) hBgt hdeg0 hquad hfast raw hmem hrecord
        | none =>
            cases hchoose :
                Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore with
            | none =>
                exfalso
                have hnone : Hex.factorFastFactorsWithBound f
                    (Hex.ZPoly.defaultFactorCoeffBound f) = none := by
                  unfold Hex.factorFastFactorsWithBound
                  rw [if_neg hdeg0,
                    if_neg (by omega : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0),
                    if_neg hB1, hquad]
                  simp [hchoose]
                rw [hnone] at hfast
                simp at hfast
            | some primeData =>
                by_cases hsmall : primeData.factorsModP.size ≤ 1
                · -- (g) small-mod singleton.
                  exact factorFastFactorsWithBound_raw_guardedIrreducible_of_smallModSingleton
                    f hf (Hex.ZPoly.defaultFactorCoeffBound f) hB_pos primeData hdeg0
                    hchoose hsmall (Or.inr hquad) hfast raw hmem hrecord
                · cases hcore :
                      Hex.factorFastCoreWithBound (Hex.normalizeForFactor f).squareFreeCore
                        (Hex.ZPoly.defaultFactorCoeffBound f) primeData
                        (Hex.initialHenselPrecision (Hex.ZPoly.defaultFactorCoeffBound f))
                        (Hex.ZPoly.quadraticDoublingSteps
                          (Hex.ZPoly.defaultFactorCoeffBound f) + 2) with
                  | none =>
                      exfalso
                      have hnone : Hex.factorFastFactorsWithBound f
                          (Hex.ZPoly.defaultFactorCoeffBound f) = none := by
                        unfold Hex.factorFastFactorsWithBound
                        rw [if_neg hdeg0,
                          if_neg (by omega : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0),
                          if_neg hB1, hquad]
                        simp [hchoose, hsmall, hcore]
                      rw [hnone] at hfast
                      simp at hfast
                  | some coreFactors =>
                      -- (h) fast-core success — the isolated arm.
                      exact fastCoreRawGuarded_of_coreIrreducible f hf
                        (Hex.ZPoly.defaultFactorCoeffBound f) hB_pos primeData hdeg0
                        hchoose hsmall (Or.inr hquad) hcore
                        (h_fastcore primeData coreFactors hchoose hcore) hfast raw hmem hrecord
  · -- Slow-modular fallback (`fast = none`).
    exact slowModularRaw_irreducible_of_fast_none f hfastnone hmod raw hmem
  · -- Slow-trial fallback (`fast = none`).
    subst htrial
    exact factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none f hf
      hfastnone raw hmem

end

end HexBerlekampZassenhausMathlib
