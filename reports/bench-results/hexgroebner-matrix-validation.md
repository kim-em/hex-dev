# Bounded native row validation: sparse matrices

Source fingerprint `14564559e1b2`, snapshot `1cbdc7e22dc1b59e256a6efffba98c971bfa0bef`, fresh benchmark SHA256 `e1bb2907b3a012272da688fce95a423b28eab21ddddd664892d238cf3917f505`. The base is merged main `57c7ae515b2d147c06e68a03e097b2cf3d95c6e5`, with an exact family overlay in the capsule. All three functions are in one fresh detached executable.

Every coefficient is one, exercising the unit-inverse alias shortcut. Each matrix over prime 65537 has n columns, n/2 two-entry reducers with distinct leading columns, and eight three-entry targets. There is one new target pivot and seven zero target rows. The known-pivot installation path is exercised n/2 times. Validation, installation, fixed-eight-target scanning and full output consumption are linear in n. Preparation is excluded. Every registered size (64, 128, 256, 512, 1024) has build-time checks for native bulk admission, successful completion and equality of complete rows, target flags, multipliers, sugars and every resource counter.

Two separate comparisons use adjacent AB/BA whole five-size sweeps, one trial per sweep (block 0 AB, block 1 BA): A is either `Elimination.reference` (ordinary Lean scheduling with bounded native scan/gather) or `Elimination.run` (the admitted whole-matrix native route); B is the bounded continuation. This is the first reference/bulk campaign for this measured source, with forty completed samples and no unchanged repeat. It is separate from the dense Cauchy records. All samples, including signal-floor flags, are retained.

The shared EPYC 9455 host has 96 logical CPUs. One algorithm thread is requested on automatically leased CPU 31. Recorded loads (1/5/15 minutes): [31.208984375, 21.61279296875, 16.99609375] → [29.11376953125, 25.1875, 19.0224609375]. There is no host-activity filtering. The registered inner target is four seconds and the call cap thirty-two seconds; actual batches, repeats, effective targets and spawn floors are retained.

| Comparator A | Block | Columns | A µs/call | Continuation µs/call | B/A | A RSS KiB | B RSS KiB | Below floor A/B |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| reference | 0 | 64 | 17.394 | 7.506 | 0.4315 | 67736 | 64916 | False/False |
| reference | 0 | 128 | 29.345 | 12.488 | 0.4256 | 60708 | 67696 | False/False |
| reference | 0 | 256 | 52.806 | 23.329 | 0.4418 | 67756 | 67696 | False/False |
| reference | 0 | 512 | 98.451 | 42.497 | 0.4317 | 65768 | 65616 | False/False |
| reference | 0 | 1024 | 198.682 | 80.195 | 0.4036 | 67708 | 67644 | False/False |
| reference | 1 | 64 | 17.479 | 7.834 | 0.4482 | 61648 | 61492 | False/False |
| reference | 1 | 128 | 28.736 | 12.665 | 0.4407 | 63392 | 61508 | False/False |
| reference | 1 | 256 | 50.615 | 22.622 | 0.4469 | 63432 | 61548 | False/False |
| reference | 1 | 512 | 97.312 | 40.811 | 0.4194 | 61676 | 67696 | False/False |
| reference | 1 | 1024 | 193.878 | 78.067 | 0.4027 | 61892 | 67644 | False/False |
| bulk | 0 | 64 | 4.832 | 7.513 | 1.5548 | 63452 | 67700 | False/False |
| bulk | 0 | 128 | 8.530 | 12.107 | 1.4192 | 67636 | 67696 | False/False |
| bulk | 0 | 256 | 15.294 | 22.072 | 1.4432 | 64260 | 67696 | False/False |
| bulk | 0 | 512 | 28.857 | 40.544 | 1.4050 | 67632 | 64396 | False/False |
| bulk | 0 | 1024 | 55.700 | 77.150 | 1.3851 | 67580 | 61752 | False/False |
| bulk | 1 | 64 | 7.618 | 7.390 | 0.9700 | 67636 | 67700 | False/False |
| bulk | 1 | 128 | 13.104 | 16.953 | 1.2938 | 67636 | 64288 | False/False |
| bulk | 1 | 256 | 23.850 | 35.725 | 1.4979 | 67632 | 67700 | False/False |
| bulk | 1 | 512 | 46.075 | 67.055 | 1.4553 | 67632 | 67700 | False/False |
| bulk | 1 | 1024 | 85.840 | 126.473 | 1.4733 | 67580 | 67644 | False/False |

Complete result hashes agree across all three functions at every size. No sample is below the runner signal floor. The fitted slope is the regression of log(time/n) against log(n); zero corresponds to the declared linear model. Exported linear-model fits:

| Comparator | Block | Arm | Verdict | Slope |
| --- | ---: | --- | --- | ---: |
| reference | 0 | A | consistent_with_declared_complexity | -0.082343 |
| reference | 0 | B | consistent_with_declared_complexity | -0.108594 |
| reference | 1 | A | consistent_with_declared_complexity | -0.079425 |
| reference | 1 | B | consistent_with_declared_complexity | -0.127698 |
| bulk | 0 | A | consistent_with_declared_complexity | -0.096297 |
| bulk | 0 | B | consistent_with_declared_complexity | -0.110716 |
| bulk | 1 | A | consistent_with_declared_complexity | -0.091493 |
| bulk | 1 | B | consistent_with_declared_complexity | -0.039399 |

These observations cover this sparse family and do not imply a general F4 speedup, an asymptotic proof or external performance leadership. The existing bulk provider remains relevant when its admission succeeds. F4 still uses the existing route: completed-execution equivalence with the reference and the general phase-fuel proof remain prerequisites for continuation integration.

Fresh F4 compute/reference SHA256 values remain `fb8e8c73858b122576cc3fe631a47876d10c6af06ec86b6d4ad93d980b76b617` and `7936068cb67aab7824434fe4e2bfeb5f3ecadf13427e3f63b01ccd852f338ad0`, byte-identical to the earlier twenty-object refactoring source. Existing full-system observations retain their original provenance. Candidate production, certificate generation, independent certification and kernel checking are not measured by these standalone kernels.

Build-time conformance checks field names, object slots, scalar offsets and phase/resource/error constructor order against the manually mirrored matrix-layout table, including a negative same-kind permutation check. Eight Clang/GCC ASan/UBSan variants pass with loop-schedule instrumentation: maximum 105 loop iterations and a 528,516 cap-arithmetic product, zero loop-count errors. These counters check only loop schedule/cap arithmetic, not actual phase cost. Copy-byte bounds are analytical and supported by alias/snapshot tests; the harness does not instrument every allocator copy. Mimalloc limits sanitizer coverage and leak detection is disabled. Current library/conformance/benchmark builds, all 39 benchmark verifications, DAG, phase, release-manifest, header and line checks pass; independent oracles and both 1,134-case drivers also pass for this source.

[Raw capsule](raw/matrix-validation-14564559e1b2.tar.gz), SHA256 `7c6c7adcc9ceaa46c7ac7ad7fb5bf883c27457d1efbdb7db4be2e53402177429`; 155 exact Git source blobs and 280 payload digests verified after packing.

[Dense Cauchy measurements](hexgroebner-matrix-state-guarded.md) use their separate source and capsule. The [generated-C comparison](hexgroebner-matrix-state-reviewed.md) records why code-generation neutrality is not asserted.

The first direct before/after campaign compares the original continuation A (source `f9ebaf35e308`, benchmark SHA256 `93e56c3ab18c62ab084dbbac10359a9bd47365dce57e7fb20744bb7a6234b632`) with native validation B. It uses the same unit-coefficient family and full result consumption, adjacent AB/BA whole sweeps, one trial per sweep. Complete hashes agree at every size. Sources remain separate.

| Block | Columns | Before µs | Native validation µs | B/A | Before RSS KiB | After RSS KiB | Below floor A/B |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 0 | 64 | 13.943 | 7.187 | 0.5154 | 67896 | 67948 | False/False |
| 0 | 128 | 23.532 | 11.853 | 0.5037 | 67548 | 67948 | False/False |
| 0 | 256 | 42.392 | 21.263 | 0.5016 | 67548 | 67944 | False/False |
| 0 | 512 | 80.791 | 39.604 | 0.4902 | 67548 | 67728 | False/False |
| 0 | 1024 | 156.071 | 77.152 | 0.4943 | 67548 | 64780 | False/False |
| 1 | 64 | 14.020 | 7.244 | 0.5167 | 64376 | 67732 | False/False |
| 1 | 128 | 24.981 | 11.860 | 0.4748 | 67896 | 64536 | False/False |
| 1 | 256 | 42.626 | 21.128 | 0.4957 | 61744 | 67944 | False/False |
| 1 | 512 | 80.833 | 39.438 | 0.4879 | 61812 | 67944 | False/False |
| 1 | 1024 | 158.149 | 76.999 | 0.4869 | 61948 | 67892 | False/False |

The direct campaign leases CPU 20, with host loads [25.6904296875, 24.99560546875, 19.43798828125] → [23.7255859375, 24.49365234375, 19.6123046875]. All twenty samples remain. Native validation takes 0.475–0.517 times the old continuation time in these samples. All exported linear-model fits are consistent with the model; finite timings are not an asymptotic proof or a universal speedup claim.

Each sanitizer variant executes 302,467 native validation phases. Tests cover malformed lengths, coefficients and columns at all seven field fixtures, saved paused states, exact errors and resource prefixes, the native row-size boundary and its checked fallback. `validate_ok` and `validate_error` audit to `propext` and `Quot.sound`; the exact charge-result lemma has no axioms. Residual validation-tail lemmas preserve monadic failure behavior. These are component lemmas; complete legacy-reference equivalence and the general fuel proof remain outstanding.

The measured snapshots have per-phase counters, so their result comparisons
do not establish native branch coverage. Subsequent conformance adds outcome
masks for every coefficient width, requiring native malformed-input errors,
validation/workspace exhaustion, the row admission edge and fallback, and
workspace allocation. Exact workspace byte/work boundaries are tested for
each field. These additions have separate logs and do not replace the raw
measured snapshots. Validation charge admission bounds saturation arithmetic
as well as reads; it is not merely a loop limit.

In bulk block 1 both arms slow substantially relative to block 0; the ratio
at 64 columns consequently falls below one. All observations remain, with no
cause inferred or sample discarded. Those ratios are local observations, not
a uniform advantage over bulk elimination.
