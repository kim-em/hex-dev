# Bounded matrix continuation: sparse known pivots

Source fingerprint `f9ebaf35e308`, snapshot `a5cbdd8b0807e46fb48d92ca1cda2975b78b2ca3`, fresh benchmark SHA256 `93e56c3ab18c62ab084dbbac10359a9bd47365dce57e7fb20744bb7a6234b632`. The base is merged main `57c7ae515b2d147c06e68a03e097b2cf3d95c6e5`, with an exact family overlay in the capsule. All three functions are in one fresh detached executable.

Each matrix over prime 65537 has n columns, n/2 two-entry reducers with distinct leading columns, and eight three-entry targets. There is one new target pivot and seven zero target rows. All coefficients are one, so known-pivot installation exercises the unit-inverse alias shortcut and gathers need no normalization product. The known-pivot installation path is exercised n/2 times. Validation, installation, fixed-eight-target scanning and full output consumption are linear in n. Preparation is excluded. The measured snapshot checks the Lean bulk prefilter at every registered size (64, 128, 256, 512, 1024), successful completion and equality of complete rows, target flags, multipliers, sugars and every resource counter.

Two separate comparisons use adjacent AB/BA whole five-size sweeps (block 0 AB, block 1 BA), one trial per sweep: A is either `Elimination.reference` (ordinary Lean scheduling with bounded native scan/gather) or `Elimination.run` (the admitted whole-matrix native route); B is the bounded continuation. This is the first campaign for this sparse family, with forty completed samples and no unchanged repeat. It is separate from the dense Cauchy records. All samples, including signal-floor flags, are retained.

The shared EPYC 9455 host has 96 logical CPUs. One algorithm thread is requested on automatically leased CPU 59. Recorded loads (1/5/15 minutes): [5.1328125, 7.484375, 11.1787109375] → [2.54541015625, 5.6435546875, 10.00927734375]. There is no host-activity filtering. The registered inner target is four seconds and the call cap thirty-two seconds; actual batches, repeats, effective targets and spawn floors are retained.

| Comparator A | Block | Columns | A µs/call | Continuation µs/call | B/A | A RSS KiB | B RSS KiB | Below floor A/B |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| reference | 0 | 64 | 16.721 | 13.744 | 0.8219 | 67692 | 67912 | False/False |
| reference | 0 | 128 | 27.605 | 23.478 | 0.8505 | 67972 | 67908 | False/False |
| reference | 0 | 256 | 49.680 | 42.344 | 0.8523 | 67972 | 67912 | False/False |
| reference | 0 | 512 | 96.753 | 78.887 | 0.8153 | 67976 | 67972 | False/False |
| reference | 0 | 1024 | 191.998 | 155.315 | 0.8089 | 67920 | 67856 | False/False |
| reference | 1 | 64 | 16.513 | 13.710 | 0.8302 | 68036 | 67912 | False/False |
| reference | 1 | 128 | 27.776 | 23.275 | 0.8380 | 67976 | 67908 | False/False |
| reference | 1 | 256 | 51.087 | 42.340 | 0.8288 | 67976 | 67912 | False/False |
| reference | 1 | 512 | 98.044 | 81.014 | 0.8263 | 68040 | 67908 | False/False |
| reference | 1 | 1024 | 194.246 | 156.021 | 0.8032 | 67920 | 67860 | False/False |
| bulk | 0 | 64 | 4.667 | 13.721 | 2.9396 | 61636 | 67916 | False/False |
| bulk | 0 | 128 | 7.970 | 23.355 | 2.9303 | 67908 | 67908 | False/False |
| bulk | 0 | 256 | 14.202 | 42.460 | 2.9897 | 67844 | 67912 | False/False |
| bulk | 0 | 512 | 27.494 | 79.545 | 2.8932 | 67844 | 67908 | False/False |
| bulk | 0 | 1024 | 52.926 | 156.244 | 2.9521 | 67792 | 67692 | False/False |
| bulk | 1 | 64 | 4.549 | 13.842 | 3.0432 | 67696 | 61704 | False/False |
| bulk | 1 | 128 | 7.753 | 23.268 | 3.0013 | 67844 | 67912 | False/False |
| bulk | 1 | 256 | 14.480 | 41.849 | 2.8902 | 67844 | 67908 | False/False |
| bulk | 1 | 512 | 27.660 | 79.709 | 2.8817 | 67844 | 67908 | False/False |
| bulk | 1 | 1024 | 52.910 | 155.599 | 2.9408 | 67792 | 67856 | False/False |

Complete result hashes agree across all three functions at every size. No sample is below the runner signal floor. Exported linear-model fits:

| Comparator | Block | Arm | Verdict | Slope |
| --- | ---: | --- | --- | ---: |
| reference | 0 | A | consistent_with_declared_complexity | -0.064417 |
| reference | 0 | B | consistent_with_declared_complexity | -0.092491 |
| reference | 1 | A | consistent_with_declared_complexity | -0.064156 |
| reference | 1 | B | consistent_with_declared_complexity | -0.082921 |
| bulk | 0 | A | consistent_with_declared_complexity | -0.085310 |
| bulk | 0 | B | consistent_with_declared_complexity | -0.086826 |
| bulk | 1 | A | consistent_with_declared_complexity | -0.075388 |
| bulk | 1 | B | consistent_with_declared_complexity | -0.084623 |

Across the retained samples, the continuation takes 0.803–0.852 times the
ordinary reference time and 2.882–3.043 times the existing native bulk time.
This supports retaining the bulk provider for admitted inputs when integrating
a proved continuation for larger shapes.

These observations cover this sparse family and do not imply a general F4 speedup, an asymptotic proof or external performance leadership. The existing bulk provider remains relevant when its admission succeeds. F4 still uses the existing route: completed-execution equivalence with the reference and the general phase-fuel proof remain prerequisites for continuation integration.

Fresh F4 compute/reference SHA256 values remain `fb8e8c73858b122576cc3fe631a47876d10c6af06ec86b6d4ad93d980b76b617` and `7936068cb67aab7824434fe4e2bfeb5f3ecadf13427e3f63b01ccd852f338ad0`, byte-identical to the earlier twenty-object refactoring source. Existing full-system observations retain their original provenance. Candidate production, certificate generation, independent certification and kernel checking are not measured by these standalone kernels.

The `c0e07d8b36` conformance checks field names, object slots, scalar offsets and phase/resource/error constructor order against the manually mirrored layout table, including a negative same-kind permutation check. Eight Clang/GCC ASan/UBSan variants pass with loop-count instrumentation: maximum 105 executed phases and a 528,516 cap-arithmetic product, zero loop-count errors. This checks the clamped loop schedule; it does not measure each phase's actual cost or establish the analytical phase/copy bounds. Copy-byte bounds are analytical and supported by alias/snapshot tests; the harness does not instrument every allocator copy. Mimalloc limits sanitizer coverage and leak detection is disabled. The `c0e07d8b36` library/conformance/benchmark builds, all 39 benchmark verifications, DAG, phase, release-manifest, header and line checks pass; independent oracles and both 1,134-case drivers passed for the unchanged algorithm/identical driver binaries.

[Raw capsule](raw/matrix-state-f9ebaf35e308.tar.gz), SHA256 `b7278edb819107f213f8e276fa18d652ff9234d981934951cd6c29584d64c2de`; 155 exact Git source blobs and 271 payload digests verified after packing.

[Dense Cauchy measurements](hexgroebner-matrix-state-guarded.md) use their separate source and capsule. The [generated-C comparison](hexgroebner-matrix-state-reviewed.md) records why code-generation neutrality is not asserted.

The measured snapshot predates the constructor-tag checks, which are test-only
and outside the measured executable family. Subsequent guards additionally
require the real native `Elimination.attempt` to return `some` at every timed
size; the measured snapshot checked only `fits`. Those guards do not change
the timed functions or establish acceptance for arbitrary matrices. RSS includes
the Lean runtime baseline; the exported fits remain finite-size observations.

The capsule scope/runner metadata uses “bulk admission” as shorthand for its
`fits` guard. The explicit native `attempt.isSome` check is a subsequent
validation addition, as distinguished above. The recorded loop-count values
are cap arithmetic, not measurements of scan ticks, phase work or copy bytes.
