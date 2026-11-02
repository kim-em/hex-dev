# Bounded native matrix workspace initialization

Source fingerprint `955b7e557f73`, snapshot `6dd72ff449063b78d0b75e83421d23053899942b`, fresh benchmark SHA256 `90dd3f2f1ca41d933b469591b663615bb453751743aa3fb6554b343b1b44d2c4`. The base is merged main `57c7ae515b2d147c06e68a03e097b2cf3d95c6e5`, with an exact family overlay in the capsule. All three functions are in one fresh detached executable.

Every coefficient is one, exercising the unit-inverse alias shortcut. Each matrix over prime 65537 has n columns, n/2 two-entry reducers with distinct leading columns, and eight three-entry targets. There is one new target pivot and seven zero target rows. The known-pivot installation path is exercised n/2 times. Validation, installation, fixed-eight-target scanning and full output consumption are linear in n. Preparation is excluded. Every registered size (64, 128, 256, 512, 1024) has build-time checks for native bulk admission, successful completion and equality of complete rows, target flags, multipliers, sugars and every resource counter.

Two separate comparisons use adjacent AB/BA whole five-size sweeps, one trial per sweep (block 0 AB, block 1 BA): A is either `Elimination.reference` (ordinary Lean scheduling with bounded native scan/gather) or `Elimination.run` (the admitted whole-matrix native route); B is the bounded continuation. This is the first reference/bulk campaign for this measured source, with forty completed samples and no unchanged repeat. It is separate from the dense Cauchy records. All samples, including signal-floor flags, are retained.

The shared EPYC 9455 host has 96 logical CPUs. One algorithm thread is requested on automatically leased CPU 18. Recorded loads (1/5/15 minutes): [20.2197265625, 26.41259765625, 24.4267578125] → [6.64453125, 19.70751953125, 22.291015625]. There is no host-activity filtering. The registered inner target is four seconds and the call cap thirty-two seconds; actual batches, repeats, effective targets and spawn floors are retained.

| Comparator A | Block | Columns | A µs/call | Continuation µs/call | B/A | A RSS KiB | B RSS KiB | Below floor A/B |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| reference | 0 | 64 | 20.334 | 6.262 | 0.3080 | 64880 | 61428 | False/False |
| reference | 0 | 128 | 31.934 | 10.293 | 0.3223 | 61476 | 67628 | False/False |
| reference | 0 | 256 | 52.375 | 18.429 | 0.3519 | 67516 | 67628 | False/False |
| reference | 0 | 512 | 99.959 | 33.520 | 0.3353 | 62460 | 67316 | False/False |
| reference | 0 | 1024 | 193.595 | 63.471 | 0.3279 | 67608 | 67412 | False/False |
| reference | 1 | 64 | 17.114 | 6.183 | 0.3613 | 67412 | 67412 | False/False |
| reference | 1 | 128 | 27.695 | 10.156 | 0.3667 | 65124 | 67628 | False/False |
| reference | 1 | 256 | 49.750 | 17.939 | 0.3606 | 64220 | 64168 | False/False |
| reference | 1 | 512 | 94.909 | 33.083 | 0.3486 | 67696 | 63380 | False/False |
| reference | 1 | 1024 | 187.218 | 63.494 | 0.3391 | 67644 | 67412 | False/False |
| bulk | 0 | 64 | 4.699 | 6.153 | 1.3095 | 67568 | 67632 | False/False |
| bulk | 0 | 128 | 7.854 | 9.942 | 1.2659 | 67568 | 67628 | False/False |
| bulk | 0 | 256 | 14.561 | 17.363 | 1.1924 | 67564 | 67628 | False/False |
| bulk | 0 | 512 | 27.920 | 32.753 | 1.1731 | 67564 | 67628 | False/False |
| bulk | 0 | 1024 | 53.670 | 62.607 | 1.1665 | 67516 | 67580 | False/False |
| bulk | 1 | 64 | 4.737 | 6.075 | 1.2825 | 67568 | 67632 | False/False |
| bulk | 1 | 128 | 8.031 | 10.058 | 1.2523 | 67564 | 67628 | False/False |
| bulk | 1 | 256 | 14.715 | 17.607 | 1.1965 | 67568 | 67628 | False/False |
| bulk | 1 | 512 | 27.619 | 32.296 | 1.1694 | 67568 | 67628 | False/False |
| bulk | 1 | 1024 | 52.703 | 63.062 | 1.1965 | 67628 | 67576 | False/False |

Complete result hashes agree across all three functions at every size. No sample is below the runner signal floor. The fitted slope is the regression of log(time/n) against log(n); zero corresponds to the declared linear model. Exported linear-model fits:

| Comparator | Block | Arm | Verdict | Slope |
| --- | ---: | --- | --- | ---: |
| reference | 0 | A | consistent_with_declared_complexity | -0.126797 |
| reference | 0 | B | consistent_with_declared_complexity | -0.126367 |
| reference | 1 | A | consistent_with_declared_complexity | -0.079716 |
| reference | 1 | B | consistent_with_declared_complexity | -0.118403 |
| bulk | 0 | A | consistent_with_declared_complexity | -0.074280 |
| bulk | 0 | B | consistent_with_declared_complexity | -0.112019 |
| bulk | 1 | A | consistent_with_declared_complexity | -0.094911 |
| bulk | 1 | B | consistent_with_declared_complexity | -0.117950 |

These observations cover this sparse family and do not imply a general F4 speedup, an asymptotic proof or external performance leadership. The existing bulk provider remains relevant when its admission succeeds. F4 still uses the existing route: completed-execution equivalence with the reference and the general phase-fuel proof remain prerequisites for continuation integration.

Fresh F4 compute/reference SHA256 values remain `fb8e8c73858b122576cc3fe631a47876d10c6af06ec86b6d4ad93d980b76b617` and `7936068cb67aab7824434fe4e2bfeb5f3ecadf13427e3f63b01ccd852f338ad0`, byte-identical to the earlier twenty-object refactoring source. Existing full-system observations retain their original provenance. Candidate production, certificate generation, independent certification and kernel checking are not measured by these standalone kernels.

Build-time conformance checks field names, object slots, scalar offsets and phase/resource/error constructor order against the manually mirrored matrix-layout table, including a negative same-kind permutation check. Eight Clang/GCC ASan/UBSan variants pass with loop-schedule instrumentation: maximum 105 loop iterations and a 528,516 cap-arithmetic product, zero loop-count errors. These counters check only loop schedule/cap arithmetic, not actual phase cost. Copy-byte bounds are analytical and supported by alias/snapshot tests; the harness does not instrument every allocator copy. Mimalloc limits sanitizer coverage and leak detection is disabled. Current library/conformance/benchmark builds, all 39 benchmark verifications, DAG, phase, release-manifest, header and line checks pass; independent oracles and both 1,134-case drivers also pass for this source.

[Raw capsule](raw/matrix-workspace-955b7e557f73.tar.gz), SHA256 `e5163ae9c8b7b1607e8c91b47c8ddf0c10fd66848c4246dfd230f3bec08d2d19`; 155 exact Git source blobs and 277 payload digests verified after packing.

[Dense Cauchy measurements](hexgroebner-matrix-state-guarded.md) use their separate source and capsule. The [generated-C comparison](hexgroebner-matrix-state-reviewed.md) records why code-generation neutrality is not asserted.

The first direct before/after campaign compares the native-validation-only continuation A (source `14564559e1b2`, benchmark SHA256 `e1bb2907b3a012272da688fce95a423b28eab21ddddd664892d238cf3917f505`) with native validation plus zeroed workspace allocation B. It uses the same unit-coefficient family and full result consumption, adjacent AB/BA whole sweeps, one trial per sweep. Complete hashes agree at every size. Sources remain separate.

| Block | Columns | Before µs | Native workspace µs | B/A | Before RSS KiB | Workspace RSS KiB | Below floor A/B |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 0 | 64 | 7.134 | 6.270 | 0.8789 | 68028 | 67812 | False/False |
| 0 | 128 | 11.805 | 10.028 | 0.8494 | 67964 | 67812 | False/False |
| 0 | 256 | 21.328 | 18.346 | 0.8601 | 67964 | 67812 | False/False |
| 0 | 512 | 40.173 | 33.702 | 0.8389 | 67964 | 67812 | False/False |
| 0 | 1024 | 77.556 | 64.057 | 0.8260 | 67912 | 67812 | False/False |
| 1 | 64 | 7.211 | 6.304 | 0.8742 | 67556 | 67812 | False/False |
| 1 | 128 | 11.991 | 10.222 | 0.8525 | 67556 | 67812 | False/False |
| 1 | 256 | 21.313 | 17.720 | 0.8314 | 67560 | 67812 | False/False |
| 1 | 512 | 39.607 | 33.358 | 0.8422 | 67556 | 67812 | False/False |
| 1 | 1024 | 76.817 | 63.899 | 0.8318 | 67556 | 67816 | False/False |

The direct campaign leases CPU 10, with host loads [2.47509765625, 13.97705078125, 19.8974609375] → [12.5, 14.6337890625, 19.7177734375]. All twenty samples remain. Native workspace initialization takes 0.826–0.879 times the validation-only continuation time in these samples. All exported linear-model fits are consistent with the model; finite timings are not an asymptotic proof or a universal speedup claim.

Each sanitizer variant executes 46,889 native workspace phases and 302,467 native validation phases. The workspace phase charges bytes and work before allocating at most 524,288 zeroed payload bytes in its admitted geometry. Tests cover malformed lengths, coefficients and columns at all seven field fixtures, saved paused states, exact errors and resource prefixes, the native row-size boundary and its checked fallback. `validate_ok` and `validate_error` audit to `propext` and `Quot.sound`; the exact charge-result lemma has no axioms. Residual validation-tail lemmas preserve monadic failure behavior. These are component lemmas; complete legacy-reference equivalence and the general fuel proof remain outstanding.

The measured snapshots have per-phase counters, so their result comparisons
do not establish native branch coverage. Subsequent conformance adds outcome
masks for every coefficient width, requiring native malformed-input errors,
validation/workspace exhaustion, the row admission edge and fallback, and
workspace allocation. Exact workspace byte/work boundaries are tested for
each field. These additions have separate logs and do not replace the raw
measured snapshots. Validation charge admission bounds saturation arithmetic
as well as reads; it is not merely a loop limit.
