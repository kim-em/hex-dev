# HexConway API Phase 6 Review

## Scope

Reviewed `HexConway/Basic.lean`, `HexConway.lean`, and the conformance
expectations in `HexConway/Conformance.lean`.

The downstream spot-check was `HexGFq/Basic.lean`, which consumes
`Conway.SupportedEntry`, `Conway.conwayPoly`,
`Conway.conwayPoly_nonconstant`, and
`Conway.conwayPoly_irreducible` to build the generic quotient-field
constructor.

The SPEC surface audited was `SPEC/Libraries/hex-conway.md`, especially
"Tier 1: imported database entries with irreducibility proofs" and the
requirement that the committed table remains ordinary Lean code with
Lean-checked irreducibility evidence. The Phase 6 criteria applied were
API design, characterising lemmas, automation annotations, namespace/import
hygiene, docstring coverage, and kernel-checked irreducibility evidence.

This is a Phase 6 API-quality review. It does not edit Lean source.

## Summary

HexConway has the right core Tier 1 shape for downstream `HexGFq` use.
`SupportedEntry` packages the selected polynomial, primality witness, and
lookup-hit proof. `conwayPoly_nonconstant`, `conwayPoly_irreducible`, and
`conwayPoly_monic` let `HexGFq` build finite fields without unfolding the
lookup table or the per-entry polynomial definitions.

I found three Phase 6 polish follow-ups. They are API and maintainability
issues, not soundness issues.

## Findings

### 1. Add predicate-level lookup characterisation for the committed table

`luebeckConwayPolynomial?` exposes `[simp]` hit lemmas for all 36 committed
entries and three representative miss lemmas. This is enough when callers
already know a concrete `(p, n)` pair. It is not enough for a caller that has
generic `p n` values and needs to reason that a lookup succeeds exactly on
the committed table, or fails outside it, without unfolding
`luebeckConwayPolynomial?` and `luebeckConwayCoeffs?`.

`HexGFq/Basic.lean` avoids this problem by accepting a
`Conway.SupportedEntry p n`, and then using `h.isSupported` through
`luebeckConwayPolynomial?_conwayPoly`. That downstream path is good. The gap
is the lookup API itself: the public table does not yet have an
`Option.isSome`/`some`/`none` characterisation theorem at the level a generic
caller or planner-generated conformance proof would naturally use.

Recommended follow-up issue:

`HexConway Phase 6: characterise Tier 1 lookup support`

Target declaration cluster:

- Add a public supported-pair predicate or theorem family for the current
  table, such as a boolean/table predicate for
  `(p, n) in {2, 3, 5, 7, 11, 13} x {1, ..., 6}`.
- Add theorems characterising `luebeckConwayPolynomial? p n = some f`,
  `Option.isSome (luebeckConwayPolynomial? p n)`, and the unsupported
  `none` cases in terms of that predicate.
- Keep the existing pointwise `_hit_p_n` lemmas as `[simp]` facts for
  concrete entries, but make the generic predicate-level theorem the
  encapsulated route for non-concrete callers.

### 2. Make the per-entry degree theorem surface uniform or remove the asymmetry

The per-entry `_degree_pos` theorem pattern exists only for the six binary
entries `luebeckConwayPolynomial_2_1` through
`luebeckConwayPolynomial_2_6`. The 30 entries for
`p in {3, 5, 7, 11, 13}` have matching per-entry definitions, `_monic`
theorems, lookup-hit lemmas, and `_irreducible` theorems, but no matching
per-entry `_degree_pos` theorem.

This is not a downstream blocker today. The generic
`luebeckConwayPolynomial?_degree_pos` theorem covers every successful
lookup, and `conwayPoly_nonconstant` is the theorem that `HexGFq` actually
uses. The asymmetry is still a Phase 6 uniformity issue because the
per-entry theorem clusters otherwise look generated and regular.

Recommended follow-up issue:

`HexConway Phase 6: regularise per-entry degree theorem names`

Target declaration cluster:

- Either add the missing
  `luebeckConwayPolynomial_{3,5,7,11,13}_{1,...,6}_degree_pos` theorems,
  deriving them from `luebeckConwayPolynomial?_degree_pos` and the existing
  hit lemmas, or deliberately replace the six binary-specific degree lemmas
  with documentation that directs users to the generic theorem.
- Keep `conwayPoly_nonconstant` as the preferred downstream API.
- Add conformance checks only if the chosen surface is meant to remain a
  generated per-entry theorem family.

### 3. Add docstring and automation polish for lookup and wrapper theorem clusters

Most public definitions and major theorem clusters are documented, including
the table, polynomial builder, per-entry polynomial definitions, per-entry
monicity and irreducibility facts, `SupportedEntry`, and the `conwayPoly_*`
wrappers. The public lookup equation lemmas are the main exception:
`luebeckConwayPolynomial?_hit_*`, the three miss lemmas, and
`luebeckConwayPolynomial?_conwayPoly` are public API facts but have no
docstrings. They are also `[simp]` only; there is no conservative `grind`
coverage for the lookup-to-wrapper route.

The private certificate check lemmas are obvious-by-name and sit immediately
under documented certificate data, so I do not recommend a separate
docstring pass for them. The follow-up should focus on the public lookup and
wrapper theorem surface that downstream users see.

Recommended follow-up issue:

`HexConway Phase 6: polish lookup theorem docs and automation`

Target declaration cluster:

- Add concise docstrings to the public `_hit_*`, `_miss_*`, and
  `luebeckConwayPolynomial?_conwayPoly` theorem families, or make the
  pointwise generated lemma policy explicit near the cluster.
- Try `[grind =]` on `luebeckConwayPolynomial?_conwayPoly`,
  `conwayPoly_nonconstant`, `conwayPoly_irreducible`, and `conwayPoly_monic`.
- Consider whether the pointwise hit/miss lemmas should remain `[simp]` only
  or also receive targeted `grind` annotations after checking that search
  does not expand the table unexpectedly.

## No Follow-Up Needed

No follow-up is needed for the core `HexGFq` consumption path. `GFq` receives
a `Conway.SupportedEntry p n` and uses the public wrapper theorems
`conwayPoly_nonconstant` and `conwayPoly_irreducible`; it is not forced to
unfold `luebeckConwayPolynomial?`, `luebeckConwayCoeffs?`, or any per-entry
polynomial definition.

No follow-up is needed for the Tier 1 irreducibility evidence shape. Each
public per-entry irreducibility theorem is derived from a
`Berlekamp.IrreducibilityCertificate`, a Lean boolean checker theorem such as
`checkIrreducibilityCertificateIncremental_rabinTest` or
`checkIrreducibilityCertificateLinear_rabinTest`, and
`Berlekamp.rabinTest_imp_irreducible`. I found no external-oracle trust point
in the exposed irreducibility theorem chain.

No follow-up is needed for namespace or import hygiene in the reviewed files.
`HexConway/Basic.lean` imports `HexBerlekamp.RabinSoundness` and
`HexGFqRing.Basic`, stays under `Hex.Conway`, and the top-level
`HexConway.lean` only re-exports `Basic` and `Conformance`.

No follow-up is needed for the separation between the Tier 1 table and later
Conway functionality. `luebeckConwayPolynomial?` returns `none` for
unsupported pairs rather than hiding search, and `conwayPoly` is explicitly
indexed by a `SupportedEntry`.

## Residual Risk

This review did not audit performance behavior or Phase 4 coverage; that is
covered by `reports/hex-conway-performance.md`.

This review did not check the committed coefficient data against an external
Luebeck source. It checked the API and theorem surface around the committed
data.

This review did not assess the command-level table rebuilding interface beyond
noting that the SPEC still calls for it as a separate metaprogram surface.

This review did not audit Tier 2 Conway compatibility proofs or Tier 3 search,
because the current reviewed module exposes the Tier 1 imported-table path.

## Verdict

HexConway should not be marked Phase 6 complete from this review alone. The
recommended follow-up issue titles are:

1. `HexConway Phase 6: characterise Tier 1 lookup support`
2. `HexConway Phase 6: regularise per-entry degree theorem names`
3. `HexConway Phase 6: polish lookup theorem docs and automation`
