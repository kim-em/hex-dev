# Bounded matrix primitive validation

Commit `8033b52781065cd37044b4b9c9d0346cfa728ed9` passes all nine local
project checks: library/theory/conformance builds and axiom audits, independent
basis/normal-form oracles, both 1,134-case standalone drivers, all 43 benchmarks,
dependency DAG, phase registration, release manifest, copyright and line limits.

Eight Clang 23.1.3 / GCC 16.2 ASan/UBSan variants pass. Each records 486,188
validation calls and 29,892 zero-buffer calls before the F4 diagnostics. Runtime
traced elimination adds 14 admitted calls of each primitive. The native-disabled
route adds no calls. A separate complete F4 diagnostic adds 653 admitted
validation calls and 232 admitted zero-buffer calls, with zero declines. This
admission rate describes the diagnostic corpus, not the timing suites generally.

Resource limits vary independently, including mixed work/input-entry/byte
allowances. Comparisons check exact errors and charged prefixes, all untouched
counters, arbitrary Nat indices and limits, all coefficient widths, malformed
representations, detached immutable-input snapshots, admission boundaries and
allocation caps. Runtime-dependent noinline entry points ensure the integration
checks run after their counter snapshots. The capsule retains the earlier failed
fixed-input integration check: that pure computation ran at module initialization
before the snapshot. No native implementation change was needed for that test fix.
ASan coverage is limited by mimalloc and leak detection is disabled.

The 65,536-column validation cap bounds one uninterruptible call to at most
65,537 entries and 524,296 payload bytes. The allocation cap bounds one
uninterruptible zeroing call to one MiB. Larger inputs use the checked portable
models. Native implementations return exactly the admitted result, retain
borrowed inputs, preserve arbitrary Nat error indices and return fresh owned
results. Lean wrapper equations are kernel checked; these equations concern the
Lean models. Agreement of C with those models is the audited and tested native
obligation.

Fresh source fingerprint `d16e17592b4a` has compute and reference executables
byte-identical to the corrected measured source `16c437c35eac`:
`9ac8cfb740dfa1c07fbbee47a86e2c64692b3fdebfc3c9a445ae22afa360c3be`
and `93b93b8dd241c6bf7b038c9bc3abef646e72de5abc6f91c23003b268b3ee3902`.
Expanded test/benchmark registration does not change these driver binaries.
The short-row-inclusive kernel benchmark uses a separate executable and its
measurements remain separate. No certification or kernel-checking timing is
claimed here.

[Validation capsule](raw/matrix-primitives-final-validation.tar.gz), SHA256
`fbf2594639c06d1b8aa78197143e75983ebfbdf8350413bc9f4a2a709419cc61`; 41 verified payload digests,
including generated probe/wrapper sources, compiled artifact hashes, source
files, full check logs and the retained initial failed test log.
