# Shared canonical isolation during real-root enumeration

`RealAlgebraicPoly.roots` filters lazy roots through canonical exactification.
When two or more real entries share an irreducible enclosing polynomial, the
compiled filter now isolates that parent once and supplies its certified arrays
to the existing `AlgebraicRoot.exactIn?` selector. Singleton and reducible groups
keep independent exactification. Root representations and number-field
arithmetic are unchanged; the real-algebraic library remains independent of
the real-closure family.

`rootPicker_eq`, `rootSelectors_eq` and the compiler equality
`realRoots_eq_cached` prove equality of the complete result, including canonical
representatives, multiplicities, ordering and checked failures. The public
logical definitions and their Mathlib correspondence remain unchanged. The
cache is returned as a concrete pair through a non-inlined function, so its
construction precedes filtering rather than being repeated by compiler
uncurrying for each entry.

This shares canonicalization work between returned roots. It does not reuse
the original component producer's isolation arrays, which the existing lazy
root set does not retain. Proper factors retain their own canonical isolation.

## Actual API measurements

[Pairs](pairs/metadata.json) identify clean sources `0ca49ccef2` and
`b4b5021188`, frozen binary hashes and complete tracked local Lean/configuration
source inventories. The inventories differ only in `HexRealAlgebraic/Roots.lean`,
the companion axiom guard and the conformance checks. Benchmark inputs,
registered output fingerprints, toolchain and dependency pins are unchanged.
[Source snapshots](sources/) retain the selected files; the full commits are
archived on `evidence/issue-10577-root-cache-before`,
`evidence/issue-10577-root-cache-prototype` and
`evidence/issue-10577-root-cache-fixed`. Dependency pins are provenance, not a
claim that every dependency artifact was independently hashed.

Four fixed trial-major blocks alternate adjacent Before/After arms on an
automatically leased CPU. All 48 arms complete and match their expected ordered
minimal-polynomial/sign/multiplicity fingerprints. All observations are retained;
there is no load rejection or unchanged rerun. Preparation and separate child
warmup are excluded; actual solving, canonicalization, filtering, sorting and
fingerprinting are timed. The 50 ms batch floor and existing child caps are
operational settings. No fitted scaling law or portable budget is asserted.

| Polynomial | Degree | Before median ms | After median ms | Median adjacent Before/After ratio |
| --- | ---: | ---: | ---: | ---: |
| `X^n−2` | 2 | 2.078 | 1.632 | 1.277 |
| `X^n−2` | 4 | 10.561 | 7.217 | 1.462 |
| `X^n−2` | 8 | 144.811 | 93.304 | 1.561 |
| `X^n−√2` | 1 | 3.997 | 3.955 | 1.015 |
| `X^n−√2` | 2 | 13.399 | 9.733 | 1.368 |
| `X^n−√2` | 4 | 149.847 | 104.883 | 1.446 |

The degree-one fixture has only one real root and exercises the uncached path.
Even-degree fixtures have two real roots with the same irreducible parent.
Sharing removes one of their two canonical parent-isolation runs; component
root production still performs its own isolation. This explains the direction
and approximate size of the improvement without asserting a general speed bound.
Observed whole-child peak RSS medians are 67.2–68.0 MiB on these fixtures,
including preparation and warmup. They are not operation-only allocation or
space bounds. Individual RSS values and ratios remain in [analysis.json](plots/analysis.json).

[PNG](plots/roots-comparison.png), [SVG](plots/roots-comparison.svg) and
[PDF](plots/roots-comparison.pdf) show every native observation, medians and
observed min–max ranges. FLINT qqbar and Z3 RCF curves reuse the
[retained external collection](../real-algebraic-poly-roots-comparison-after/README.md);
they are historical references rather than contemporaneous paired arms.
The plot checks every external fingerprint against the native fixture.
External solving, sorting, exact annihilation, JSON and cleanup differ from
native canonical-representation checking. External minimal polynomials are
inferred by Eisenstein for these fixtures, not extracted from backend storage.

Reproduce pairs with `scripts/bench/fixed_conversion_paired.py --roots-only
--before <frozen-before> --after <frozen-after> --output <new-directory>`.
Reproduce plots with `scripts/plots/real-root-isolation-reuse.py --input
reports/bench-results/real-root-isolation-reuse/pairs --reference
reports/bench-results/real-algebraic-poly-roots-comparison-after --output
<new-directory>`. Use the configured oracle Python environment for the latter.
The executed collector and freezing script are retained beside the observations
and source snapshots. Exact binaries and raw profiles remain in the persistent
locations indexed by [persistent-retention.json](persistent-retention.json).

## Retained rejected design

[Prototype observations](prototype/metadata.json) retain all 48 completed arms
against `ce91530a2a`, with exact result agreement but approximately 2.9× worse
degree-eight rational elapsed time. The function-valued cache was compiled as
a two-argument `rootSelectors(roots, entry)`: its fold and isolation ran again
for each filtered entry. The corrected [generated C](code/fixed-Roots.c.gz)
returns the cache from a one-argument function called before filtering;
[prototype C](code/prototype-Roots.c.gz) retains the rejected expansion.

The [prototype profile](prototype/profile/rational-roots.manifest.json) retains
2,121 kernel-window samples, passing calibration and ±5 ms sensitivity checks.
Its [summary](prototype/profile/rational-roots.summary.json) attributes 95.43%
inclusive cost to isolation and 84.87% to the compiled real-root filter. These
shares overlap. It explains the prototype's added work, not the final binary's
cost distribution. The [prototype plot](prototype/plots/roots-comparison.svg)
and all raw points remain separate from the corrected measurements.

## Verification and concerns

[Verification logs](verification/) retain the successful computational and
ordinary-kernel companion builds, all 196 benchmark result checks under
`LEAN_ABORT_ON_PANIC=1`, conformance, unchanged emitted fixtures and all 83
exact FLINT oracle cases with no unavailable-component skips. The compiler-map
guard checks the production rewrite; a mixed-parent/nonreal check compares the
cached and independent selectors, preserving multiplicities. The axiom guard
admits only `propext`, `Classical.choice` and `Quot.sound`. Admission and
Mathlib-free checks pass. The initial verifier without the configured external
Python environment and the interrupted pre-cache proof build remain retained.
Timing children discard stderr; the separate guarded verifier supplies the
panic check. Required CI must pass on the final PR head.

The large external gap remains: the larger corrected fixtures still cost
roughly 900–3,000 times the historical external medians. These are observations
on the stated boundaries, not portable ratios. Isolation, larger degrees and
the remaining advertised operation/comparator coverage still need the #10577
audit. This change does not attest Phase 4 or implement the forward comparison
strategy extension excluded by the central SPEC.
