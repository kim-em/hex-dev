# Same-level graph kernel replay

The build-only probes under `bench/HexSignDetMathlib/ProofProbe` cover accepted
and stale-context graphs at depths 1, 3, 5 and 7. Their query arities are 2,
8, 32 and 128. The root head is X²−1 on (0,2), all queries are the constant
2, and each parent has one candidate sign word. Both child edges refer to
the preceding node. This gives depth+1 graph entries and twice-depth edges.
The rejection fixture changes only the final node's context, after a valid
prefix. It does not time a missing-root or empty-input shortcut.

These are schematic literal certificates: their compact expressions use
replication and arrays to express supplied rows, counts and witnesses.
They invoke no prepared-domain, query, sign-table or rank producer. Each
candidate module rewrites the proved cache-invariance identities, unfolds the
actual graph/local/query checkers and closes
its theorem with `decide +kernel`. It does not reuse an imported conformance
acceptance theorem. The kernel therefore checks the literal data and its
normalization. All eight accepted theorem declarations have exactly
`propext`, `Classical.choice` and `Quot.sound` in their axiom inventories.

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
proof elaboration and ordinary kernel checking. It is not pure compiled
checker time and receives no LeanBench complexity verdict. Timeouts are
operational safeguards; this suite declares no absolute performance budget.
A runner `release_quality` flag establishes its provenance and complete
samples, not full Phase-4 coverage or semantic correctness.

This is one same-level graph family with constant coefficient/witness size
and support one. It does not replace proof evidence for nested coefficient
certificates, arbitrary root-sum soundness, increasing matrix/support or
witness sizes, descriptor operations, or the final semantic theorems. Those
remain separate requirements. The shared semantic bridge in #10389 and the
separate Thom/BKR foundations are still needed for root-level conclusions.

## Recorded observations

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
toolchain. The current checker and compiler differ from that archive, so these
figures are not performance evidence for the current implementation. The
current proof modules use general cache-invariance identities to expose the
complete literal checks; they do not reuse an acceptance theorem.

The [raw sweep](data/sign-det-proofs/06d77092b/sweep.json) retains compiler
output, all timings, peak RSS, emitted artifact sizes and 197 source hashes.
RSS includes the complete compiler process and imported environment; it does
not measure replay allocation. Artifact sizes are module sizes, not serialized
certificate sizes. The [source archive](data/sign-det-proofs/06d77092b/source-archive.json)
identifies a committed patch against a merged base. Reconstruction in a
temporary Git index verified every recorded source hash, preserving the
measured source closure across subsequent rebases and squash merges.
