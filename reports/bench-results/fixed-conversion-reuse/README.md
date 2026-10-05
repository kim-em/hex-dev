# Certified fixed-field conversion reuse

`PolyQuot.toAlgebraicNumber?` already isolates the output minimal polynomial
to select its root. It now passes that certified run to `ofNormalizedIn?`
instead of asking `ofNormalized?` to isolate the polynomial again. The
ordinary-kernel theorem `PolyQuot.toAlgebraicNumber?_eq` proves equality of the
complete `Option AlgebraicNumber`, including the stored canonical representative
and all checked failures. The existing Mathlib soundness and totality proofs
reuse this equality without changing their statements. No root representation,
number-field arithmetic, or comparison strategy is replaced.

## Paired observations

[metadata.json](metadata.json) identifies frozen clean baseline `8121fc663`
and changed source `e69775794`, exact executable hashes, computational snapshots,
automatically leased CPU and host activity. Four trial-major blocks alternate
adjacent Before/After and After/Before arms at each rung. All 48 arms complete
with matching expected result fingerprints. Every completed observation is
retained; no unchanged rerun, load rejection or quiet-core preflight was used.
The all-library build ran concurrently on the shared host. The recorded
1/5/15-minute load averages are 10.70/57.96/99.84 at the start and
76.75/113.99/113.20 at the end. These are context, not sample rejection criteria.

The timed boundary is the existing scalar operation and canonical
polynomial/sign guard. Operand preparation and separate warmup are excluded.
The benchmark source and operational caps are identical in both arms. Addition
uses lazy resultant arithmetic rather than this fixed conversion and is an
unchanged control; square root reaches fixed conversion through common-field
coordinate recovery. The study does not directly time conversion in isolation.

| Operation | Operand degree | Before median ms | After median ms | Median adjacent Before/After ratio |
| --- | ---: | ---: | ---: | ---: |
| Add control | 2 | 1.601 | 1.183 | 1.164 |
| Add control | 4 | 12.198 | 12.796 | 0.990 |
| Add control | 8 | 399.132 | 474.085 | 0.916 |
| Sqrt | 2 | 20.189 | 21.141 | 1.027 |
| Sqrt | 4 | 334.245 | 289.279 | 1.212 |
| Sqrt | 8 | 14089.120 | 13649.342 | 1.135 |

Individual adjacent square-root ratios range from 0.791 to 2.809. These data
are inconclusive about an end-to-end improvement. Ratios above one favor
the changed arm; the ratio column is the median of adjacent ratios, not the
ratio of aggregate medians. Absolute times are host-specific observations,
not portable budgets or Phase-4 admission.
The unchanged Add control's median adjacent ratios range from 0.916 to 1.164;
its individual pairs range from 0.584 to 1.477. This demonstrates substantial
variability in the retained observations rather than an effect of conversion
reuse. It is not a formal estimate of the uncertainty of the square-root ratios.

[PNG](plots/fixed-conversion-comparison.png),
[SVG](plots/fixed-conversion-comparison.svg) and
[PDF](plots/fixed-conversion-comparison.pdf) show every timing dot, median and
observed min–max range. FLINT qqbar and Z3 RCF curves reuse the earlier
[scalar capture](../real-algebraic-scalar-annihilation/README.md). They are
historical references, not contemporaneous paired measurements; their timed
annihilation/sign checks, JSON and cleanup differ from the native canonical
representation guard. The large scalar gap remains visible without fitting a
complexity model. The complete interpretation is in
[analysis.json](plots/analysis.json).

The separate [direct conversion capture](direct/metadata.json) uses the existing
`Hex.NumberFieldBench.runQAdjoinCanonical` fixed degree-two input and its
unchanged complete-result fingerprint. All eight adjacent AB/BA arms pass.
The median is 0.912 ms before and 0.480 ms after; the four adjacent ratios are
1.891, 1.921, 1.887 and 1.906 (median 1.899). This supports an improvement of
the direct conversion on this fixture, not a general degree-scaling claim or a
square-root speedup. The figure's third panel shows every direct observation.

Compiled-arm provenance comes from `metadata.json.sources.Before/After`,
the frozen executable hashes and snapshots. The lean-bench exporter observes
the collector checkout for both arms; its `env.git_commit` is not the compiled
baseline's source identity.
The measured changed source remains reachable through the pushed
`evidence/issue-10577-fixed-conversion-source` branch.
[source-equivalence.json](source-equivalence.json) verifies all twelve frozen
changed-arm source hashes after rebasing onto current main. The rebased full
Lake build also passes; measured timings remain attributed to their original
compiled source.

Reproduce collection with `scripts/bench/fixed_conversion_paired.py --before
<frozen-before> --after <frozen-after> --output <new-directory>`.
The direct capture adds `--conversion-only` and uses its own new directory.
Reproduce plots
with `scripts/plots/fixed-conversion-reuse.py --input
reports/bench-results/fixed-conversion-reuse --reference
reports/bench-results/real-algebraic-scalar-annihilation --direct
reports/bench-results/fixed-conversion-reuse/direct --output
<plot-directory>`. The executed collector is retained in [collector.py](collector.py).

## Square-root attribution

The [manifest](scalar-sqrt.manifest.json) profiles the changed degree-4
square-root operation on clean `e69775794`. Its 965 kernel-window samples
pass calibration (0.874 ms trimmed residual), confidence and ±5 ms sensitivity
checks. Leaf shares are allocation 37.31%, GMP 20.00%, Lean runtime 34.20%,
own code 4.15% and other 4.35%. The [summary](scalar-sqrt.summary.json) ranks
inclusive isolation at 95.85%, component refinement at 79.07%, Taylor work at
52.33%, common-field presentation at 49.53%, and exact-factor canonicalization
at 41.87%. Fixed-field conversion is only 1.76%. Inclusive shares overlap
and must not be added.

This explains why removing one conversion isolation does not resolve the
square-root bottleneck. Repeated canonical isolation and presentation power
construction remain concerns. The capture supplies attribution for this
representative, not complete coverage of every required input family.
If the direct fixture's 1.9-fold conversion factor applied to this profile,
and all other costs stayed constant, the 1.76% changed-arm share would imply
only about a 1.6% end-to-end improvement. This is a conditional attribution
estimate across different fixtures, not a measured gain or strict bound.
The larger observed scalar ratios cannot be attributed to the change from
these data; the unchanged controls reinforce the inconclusive interpretation.

Raw perf data, original/normalized/filtered samply profiles, sidecar,
symbols, diagnostics, commands and source snapshots remain under
`/home/kim/.local/state/hex/issue-10577-fixed-conversion/profile-raw`.
Frozen binaries remain in the sibling `before` and `after` directories.
[retention.json](retention.json) verifies every recorded raw artifact and
frozen executable hash. These paths persist outside `/tmp`.

## Local checks and remaining readiness

The full Lake build passes, including the manual. The ordinary-kernel axiom
guards for the new equality and the existing correspondence pass; the named
admission audit checks 330 roots and 1147 modules. Real-algebraic verification
passes all 196 registrations and NumberField verification all 92. Fresh
fixtures agree byte-for-byte with the committed streams; independent exact
oracles check 83 real-algebraic cases and 11 NumberField cases with no failures.

The initial NumberField comparator failure and oracle skip caused by missing
cypari2 are retained in `number-field-bench-verify.log` and
`number-field-oracle.log`. The corrected interpreter combines cypari2/PARI
2.17.3 and python-flint 0.9.0; `number-field-bench-verify-with-pari.log` and
`number-field-oracle-complete.log` record actual successful checks. Environment
setup and the rejected oracle command-line invocation are also retained.
`core-build.log` records an earlier proof iteration and is diagnostic only;
`full-build.log` and `rebased-full-build.log` verify the final proof. Both
capture directories contain their hash-identified source snapshots.

All four assigned libraries remain at Phase 3. Missing operation-specific
performance admission, remaining family attribution and the substantial
canonical isolation concern are not discharged by this partial change. The
implemented `realCompare` and `RealAlgebraicPoly.roots` surface remains in scope;
the forward comparison-strategy extension remains excluded. Already merged
correspondence theorems are available to #10377, #10378 and #10575 independently
of this remaining timing work.
