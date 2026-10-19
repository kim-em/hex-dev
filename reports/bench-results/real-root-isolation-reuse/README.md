# Shared canonical isolation during real-root enumeration

`RealAlgebraicPoly.roots` filters lazy roots through canonical exactification.
When two or more real entries share an irreducible enclosing polynomial, the
compiled filter now isolates that parent once and supplies its certified arrays
to the existing `AlgebraicRoot.exactIn?` selector. Reducible multi-entry groups
share the factor array, using the existing `exactFactor?` checks and isolation for
proper factors. Singletons keep independent exactification. Root representations and number-field
arithmetic are unchanged; the real-algebraic library remains independent of
the real-closure family.

`Internal.factorPicker_eq`, `Internal.rootPicker_eq`,
`Internal.rootSelectors_eq` and the compiler equality `realRoots_eq_impl` prove equality of the complete result, including canonical
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
`4ea36ac633`, frozen binary hashes and complete tracked local Lean/configuration
source inventories. The inventories differ only in `HexRealAlgebraic/Roots.lean`,
the companion axiom guard and the conformance checks. Benchmark inputs,
registered output fingerprints, toolchain and dependency pins are unchanged.
[Source snapshots](sources/) retain the selected files; the full commits are
archived on `evidence/issue-10577-root-cache-before`,
`evidence/issue-10577-root-cache-prototype` and
`evidence/issue-10577-root-cache-factor-fixed`. The earlier isolation-only
revision remains archived on `evidence/issue-10577-root-cache-fixed`. Dependency pins are provenance, not a
claim that every dependency artifact was independently hashed.

Four fixed trial-major blocks alternate adjacent Before/After arms on an
automatically leased CPU. All 48 arms complete and match their expected ordered
minimal-polynomial/sign/multiplicity fingerprints. All observations are retained;
there is no load rejection or unchanged rerun. Preparation and separate child
warmup are excluded; actual solving, canonicalization, filtering, sorting and
fingerprinting are timed. The 50 ms batch floor and existing child caps are
operational settings. No fitted scaling law or portable budget is asserted.

| Polynomial | Degree | Before median ms | After median ms | Median adjacent Before/After ratio | Individual paired min–max |
| --- | ---: | ---: | ---: | ---: | ---: |
| `X^n−2` | 2 | 2.101 | 1.658 | 1.271 | 1.261–1.964 |
| `X^n−2` | 4 | 10.379 | 7.550 | 1.402 | 1.327–1.460 |
| `X^n−2` | 8 | 147.106 | 93.632 | 1.563 | 1.522–2.583 |
| `X^n−√2` | 1 | 3.971 | 3.891 | 1.019 | 0.992–1.059 |
| `X^n−√2` | 2 | 12.824 | 9.607 | 1.332 | 0.799–1.417 |
| `X^n−√2` | 4 | 146.153 | 96.546 | 1.509 | 1.471–1.536 |

The degree-one fixture has only one real root and exercises the uncached path.
Even-degree fixtures have two real roots with the same irreducible parent.
Sharing removes one of their two canonical parent-isolation runs; component
root production still performs its own isolation. This explains the direction
and approximate size of the improvement without asserting a general speed bound.
Whole-child peak RSS observations are retained on these fixtures,
including preparation and warmup. They are not operation-only allocation or
space bounds. One quadratic degree-two pair regresses; the individual ranges
show variation that median ratios alone would hide. Individual RSS values and ratios remain in [analysis.json](plots/analysis.json).

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

## Reducible-parent control and earlier variants

The existing `runFilterRoots` prepares the lazy root set of `X^4−1`, then times
exactification, nonreal filtering and sorting. [Four adjacent pairs](filter-control/metadata.json)
observe 1.280 ms before and 1.232 ms after, with median paired ratio 1.037
and individual ratios 1.035–1.048. All eight arms complete with the same
fingerprint. This older registration has no predeclared expected hash;
the control establishes paired result agreement, not an independently pinned
result. The retained collector's generic boundary string incorrectly mentions
an expected fingerprint for this control; its exports correctly record
`expected_hash_check.status = "unset"`. Future control captures use the corrected
boundary string. A multi-entry reducible group now factors its parent once rather than
once per real entry, retaining the existing proper-factor selector.

The [earlier isolation-only variant](isolation-only/pairs/metadata.json)
retains all 48 root-enumeration arms and [eight reducible-control arms](isolation-only/filter-control/metadata.json).
Its up-front irreducibility check performed an additional parent factorization
for reducible groups. Control ratios varied from 0.718 to 1.274 and did not
establish a consistent improvement or regression. The revised implementation
removes that extra work by retaining and consuming the factor array. No
completed observation was removed or overwritten.

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
guard checks the production rewrite and its one-argument cache IR; a mixed-parent/nonreal check compares the
cached and independent selectors, preserving multiplicities. The axiom guard
admits only `propext`, `Classical.choice` and `Quot.sound`. Admission and
Mathlib-free checks pass. The initial verifier without the configured external
Python environment and the interrupted pre-cache proof build remain retained.
Timing children discard stderr; the separate guarded verifier supplies the
panic check. Required CI must pass on the final PR head.

The large external gap remains: the larger corrected fixtures still cost
roughly 800–2,700 times the historical external medians. These are observations
on the stated boundaries, not portable ratios. Isolation, larger degrees and
the remaining advertised operation/comparator coverage still need the #10577
audit. This change does not attest Phase 4 or implement the forward comparison
strategy extension excluded by the central SPEC.

For an irreducible group of `k` real entries, the implementation still performs
`2k+1` parent factorizations versus `2k` before: the preparatory factor array
decides whether to share isolation, while `exactIn?` and `exactParent?` retain
their existing per-entry checks. If factorization dominates isolation, that
extra work can matter. Folding the cached factors with `exactParent?` instead
of calling `exactIn?` is a possible follow-up; no general speedup is asserted.
The conformance check was extended after the measured source to compare cached
and independent selectors on a reducible parent with real and nonreal roots;
the timed computational library and benchmark bodies remain unchanged.
