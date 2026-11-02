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

`MatrixValidation.validateFrom_zero` proves that combined-cursor validation equals
the reference's reducer loop followed by its target loop, preserving first
errors and charged prefixes. The component success/failure/terminal laws and
`Native.Scan.untraced_events` are kernel checked. Axiom audits use only `propext`,
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

Additional records bind commit `b95c20360e`, where elimination directly calls
the shared inline `validateRows` function, the validation transition lemmas
preserve the field/limits/column/input context, and separate native masks
require both validation work-exhaustion sites across all coefficient widths.
Workspace work tests cover one below and exactly at the boundary. Eight
Clang/GCC sanitizer variants and all nine full project checks pass. Earlier
capsules retain their original sources and counts.

[Additional validation capsule](raw/matrix-native-review-validation.tar.gz),
SHA256 `bb48607a91ef0e24b5e4bf1632beae0c8accfed3deab2b2ce394b8e4f77e2fb0`;
46 verified payload digests. These are validation records, not timings.

The final test/proof refinement additionally asserts explicit workspace outcomes:
exact byte/work limits reach input processing, and one below yields the
corresponding exhaustion. Public validation lemmas preserve the read-only
`State.contents` of all unchanged fields, with cursor, phase, result and
statistics stated separately. The native C source is unchanged. Four Clang
sanitizer variants pass these stronger assertions in addition to the preceding
eight-variant C checks.

[Refined validation records](raw/matrix-native-frame-validation.tar.gz), SHA256
`367b417ee1e54065f1b65469d1715957c6c9105b2df184366112750fcfb69468`;
12 verified payloads. No timing data is associated with this refinement.
