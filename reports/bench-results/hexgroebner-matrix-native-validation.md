# Native matrix phases: final conformance and proof support

This capsule records validation of commit `282413d199` based on merged main
`68c7223028495696762ad3a91c4f6f623acf7902`. It contains no timing campaign.
The [validation](hexgroebner-matrix-validation.md) and
[workspace](hexgroebner-matrix-workspace.md) measurements retain their exact
source snapshots and executables; their observations are not transferred to
this source.

All library/theory/conformance targets build. Independent oracles pass,
including 567 complete reduced bases compared with Singular. Both CLI drivers
pass 1,134 complete corpus outputs/counters and input/resource boundaries.
All 39 benchmark verifications and structural checks pass. The first DAG check
rejected the unregistered optional scan-proof module; its explicit Lake root
is registered, and the library build, DAG, phase, release-manifest, copyright
and line checks pass after that packaging correction. The failed check remains
in the capsule alongside the passing records.

Four Clang and four GCC ASan/UBSan variants require native outcome masks at
all three coefficient widths. Every malformed length/column/coefficient
branch, validation input-entry/byte/work exhaustion, workspace byte/work
exhaustion, native row-admission edge/fallback and successful allocation must
execute. Each variant records 311,983 native calls, 302,530 validation phases
and 46,910 workspace phases. Explicit workspace tests use byte limits just
below and at the exact allocation boundary, and a work limit one below the
required total after successful byte reservation, for each of seven fields.
Saved snapshots, full errors and exact prefix counters are compared.

Loop-count instrumentation records at most 105 iterations and a 528,516
cap-arithmetic product, with zero scheduling errors. It does not measure
actual phase cost or allocator-copy bytes. Shape/copy bounds remain analytical.
Mimalloc limits sanitizer coverage and leak detection is disabled; explicit
ownership/snapshot tests supplement it.

`MatrixValidation.validate_rows` proves that combined-cursor validation equals
the reference's reducer loop followed by its target loop, preserving first
errors and charged prefixes. The component success/failure/terminal laws and
`Native.Scan.events_eq` are kernel checked. Axiom audits use only `propext`,
`Classical.choice` and `Quot.sound`; `Matrix.charge_run` uses no axioms.
These lemmas are reusable support, not a completed-continuation equivalence
or general fuel theorem. F4 retains its existing routing.

[Validation capsule](raw/matrix-native-root-validation.tar.gz), SHA256
`ead6faf67b85e813659366cc96c7f7c95023fca595599ca9dc8b1fc252e6de6d`; 48 payload digests verified after packing.

The [preceding validation capsule](raw/matrix-native-final-validation.tar.gz)
remains unchanged (SHA256
`915e3b80fd32c9f36862a0e92b41f1efc16c4cc5db6bf28f879ea2a0382d4643`).
It predates the explicit scan-proof root and contains the first DAG failure;
the capsule above additionally records the corrected packaging checks.
