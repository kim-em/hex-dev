# Same-level graph kernel replay

The measurements below use the retained source snapshots. Current CI builds a
representative depth-three replay/semantic example and all retained same-level
correctness fixtures. The source archives retain the removed collection
drivers and their import-only timing baselines.

The correctness fixtures under `conformance/HexSignDetMathlib/Diagnostics`
cover accepted and stale-context graphs at depths 1, 3, 5 and 7. Their query arities are 2,
8, 32 and 128. The root head is X²−1 on (0,2), all queries are the constant
2, and each parent has one candidate sign word. Both child edges refer to
the preceding node. This gives depth+1 graph entries and twice-depth edges.
The rejection fixture changes only the final node's context, after a valid
prefix. The final node fails its context check before moment replay; this
is the cheapest local rejection after a valid prefix. Forged arithmetic,
altered domains, malformed bytes and nested coefficient rejection are separate
requirements.

These are schematic literal certificates: their compact expressions use
replication and arrays to express supplied rows, counts and witnesses.
They invoke no prepared-domain, query, sign-table or rank producer. Each
candidate module rewrites the proved cache-invariance identities and evaluates
their cache-free right-hand sides with `decide +kernel`. The theorem still
asserts the result of the actual `Dag.check`, but its kernel reduction has a
different schedule from compiled replay: shared domain validation is repeated
inside the moment checks. These measurements describe that proof strategy;
they do not measure the compiled checker’s cached schedule. It does not reuse an imported conformance
acceptance theorem. The kernel therefore checks the literal data and its
normalization. All eight replay theorem declarations have exactly
`propext`, `Classical.choice` and `Quot.sound` in their axiom inventories.
Each inventory is guarded in the archived source. The recorded build-only
target was included in the existing CI job; the representative examples now
retain the same admission guards. No scientific timing campaign runs in CI.

Each replay module is paired with a separate fresh module declaring the
identical certificate expression but no replay theorem. Accepted and rejected
fixtures each have their own matching literal reference. Imported inputs
and dependencies stay warm; only the measured module's artifacts are
removed before `lake build +<module>:olean`. The shared fresh-module runner
uses six rounds, rotating pair order and alternating adjacent arm order.
Every completed pair and signed candidate-minus-reference delta is retained,
together with source hashes, dirty-state checks, emitted artifact sizes,
compiler output and axiom inspection. An automatically leased CPU is used
without a host-idleness test. No null control or automatic rerun is required.

The paired difference includes reduction of the compact certificate expression,
proof elaboration, ordinary kernel checking, proof-term serialization, one
unguarded `#print axioms` and Lake/build scheduling overhead. Pairing does
not eliminate variable host or build overhead. It is not pure compiled
checker time and receives no LeanBench complexity verdict. Timeouts are
operational safeguards; this suite declares no absolute performance budget.
A runner `release_quality` flag establishes its provenance and complete
samples, not full Phase-4 coverage or semantic correctness.

This is one same-level graph family with constant coefficient/witness size
and support one. It does not replace proof evidence for nested coefficient
certificates, arbitrary root-sum soundness, increasing matrix/support or
witness sizes, descriptor operations, or the final semantic theorems. Those
remain separate requirements. The probes prove only Boolean acceptance/rejection. They do not depend on
`HexRealRootsMathlib.Tarski.check_rootSum`, proved in
`adapters/HexRealRootsMathlib/TarskiSoundness.lean`. Applications of that
semantic theorem have separate [proof-cost evidence](sturm-tarski-semantics.md).
Root-level correctness also requires the separately specified Tau Ceti Thom
injectivity/order and BKR foundations. Their actual delivery and use remain
requirements for [#10377](https://github.com/kim-em/hex-dev/issues/10377).

## Measurements at 45582256f

The source revision `45582256fc5dd9adbf53a8dfbb10f6c90b66d717` supplies
48 complete adjacent pairs (96 fresh-module builds), with six rotated rounds
and balanced arm orientations on `chungus2`, automatically leased CPU 47.
All completed samples are retained. Every candidate has exactly the three
standard axioms, and the runner reports no provenance exceptions. The source
archive reconstructs and verifies all 213 recorded local source hashes.

The theorem statements, proof bodies, checker and compiler match the probes
at `1d07a2fcf0afe9406ca9dd1ecc63df9c47ae16d3`. These measured modules precede the added
CI message guards; the timings cover the archived modules and do not include
those additional guard commands. No comparison with the older compiler's
timings is claimed.

| Depth | Outcome | Literal median (ms) | Replay median (ms) | Paired delta median (ms) | Delta range (ms) | Delta sample SD (ms) |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | accept | 2421.384 | 2925.886 | 499.540 | 495.607–1281.249 | 317.510 |
| 1 | reject | 2437.585 | 2921.962 | 485.266 | 471.369–558.081 | 32.266 |
| 3 | accept | 2474.323 | 3023.334 | 596.967 | 504.090–2456.333 | 756.997 |
| 3 | reject | 2479.327 | 3021.235 | 590.818 | 495.854–1104.812 | 219.328 |
| 5 | accept | 2420.095 | 3127.913 | 715.458 | 670.011–924.432 | 91.889 |
| 5 | reject | 2422.821 | 3116.437 | 690.714 | -0.166–699.721 | 281.984 |
| 7 | accept | 2436.244 | 3420.429 | 988.248 | 963.586–1627.387 | 263.669 |
| 7 | reject | 2424.305 | 3313.784 | 891.942 | 799.167–2790.595 | 783.532 |

The positive median paired overhead increases across this measured arity range, but
this is a fixed-support family and establishes no asymptotic bound. All
`no-comparable-control` classifications are retained. The
[raw sweep](data/sign-det-proofs/45582256f/sweep.json) includes compiler output,
wall time, peak compiler RSS, emitted module sizes and host activity. As above,
compiler RSS is not replay allocation and module size is not certificate size.
The [source archive](data/sign-det-proofs/45582256f/source-archive.json) preserves
the measured source independently of subsequent merges. The final round has elevated wall times across the pairs; several spreads are
large, and one depth-five rejection delta is slightly negative. Every sample
is retained; these observations do not identify a cause or exclude samples.

The wider families, nested coefficient proofs, descriptor operations, recorded
matrix dimensions, serialized certificate sizes, peak intermediate bits,
runtime allocation and representative attribution required by
[#10377](https://github.com/kim-em/hex-dev/issues/10377) remain separate obligations.

## Archived measurements at 06d77092b

The clean source revision `06d77092b1e5824191b7fd9716aeefa46dfe2db8`
produced all 48 adjacent pairs (96 fresh-module builds) on `chungus2`, using
automatically leased logical CPU 67. All six rounds and both arm orientations
were retained, with no rerun. Every candidate's inspected axiom inventory
contains exactly the three axioms listed above. The runner reports complete
measurements with no provenance exceptions.

The table gives wall-clock milliseconds. The delta is the median of the six
paired differences, not the difference between the two arm medians. The range
and sample standard deviation describe those same six signed differences.

| Depth | Outcome | Literal median | Replay median | Paired delta median | Delta range | Delta sample SD |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | accept | 2875.019 | 3529.115 | 646.696 | 115.728–869.264 | 272.722 |
| 1 | reject | 2953.218 | 3330.310 | 506.164 | 253.125–574.168 | 141.081 |
| 3 | accept | 2910.410 | 3620.341 | 723.968 | 508.464–882.887 | 139.429 |
| 3 | reject | 2935.934 | 3551.907 | 674.471 | 511.159–780.323 | 110.439 |
| 5 | accept | 2817.296 | 3716.300 | 985.638 | 673.789–1075.316 | 164.813 |
| 5 | reject | 2877.687 | 3720.243 | 838.207 | 768.606–918.529 | 63.101 |
| 7 | accept | 2862.839 | 4032.919 | 1196.948 | 1096.703–1303.096 | 76.639 |
| 7 | reject | 2857.459 | 3958.770 | 1115.630 | 805.619–1221.176 | 149.194 |

The observations show increasing median replay overhead over these four
depths, with substantial variation, especially at depth 1. They establish
neither an asymptotic complexity bound nor an absolute performance gate.
The runner's `no-comparable-control` classification is retained: this suite
does not provide a null-control resolution verdict. Host activity is recorded
context and did not exclude any completed sample.

The recorded timings apply only to the archived `06d77092b` sources and
toolchain. The checker and compiler at `45582256f` differ from that archive, so these
figures are not performance evidence for the current implementation. The
proof modules at `45582256f` use general cache-invariance identities to expose the
complete literal checks; they do not reuse an acceptance theorem.

The [raw sweep](data/sign-det-proofs/06d77092b/sweep.json) retains compiler
output, all timings, peak RSS, emitted artifact sizes and 197 source hashes.
RSS includes the complete compiler process and imported environment; it does
not measure replay allocation. Artifact sizes are module sizes, not serialized
certificate sizes. The [source archive](data/sign-det-proofs/06d77092b/source-archive.json)
identifies a committed patch against a merged base. Reconstruction in a
temporary Git index verified every recorded source hash, preserving the
measured source closure across subsequent rebases and squash merges.
