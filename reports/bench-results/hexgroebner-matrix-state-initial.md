# Bounded matrix continuation: initial standalone kernels

These measurements bind content fingerprint `87692e081b76`, staged snapshot
`65c91b4b09bafa10c197c91d4abff3f591659ec4`, and benchmark SHA256
`ae2a3c06f9e7616947fcc05536c31790be934efc99d2e6b5b005f533874e9aee`. Both arms use the same fresh detached executable.
The monorepo base is commit `53831dd285e7c79fd79929e0f316fc565890f1d2`; the capsule supplies the measured family overlay.
A is the existing `Elimination.reference`; B is the nineteen-object continuation.
The twenty-object source has different ownership handling, per-row fuel,
shape-based completion fuel and carrier registration. These observations
apply only to the nineteen-object source and are not pooled with other sources.

Cauchy matrices over prime 65537 have full rank. Preparation is excluded;
validation, allocation, elimination, complete decoded rows, multipliers, sugars
and every resource counter are consumed and structurally hashed. All sixteen
processes complete successfully, with identical complete result hashes at every
size. The benchmark Boolean incorrectly expects zero reducer rank despite
half of the rows being reducers, so that flag is false in both arms. The
complete successful echelon rows and counters are still consumed; errors would
produce empty arrays. These records do not validate that erroneous predicate.
The corrected benchmark requires the actual reducer count and successful
complete equality at every timed size. All rows are above the runner's signal floor. No unchanged repeat is used.

The manual shared EPYC 9455 host run uses one requested algorithm thread and CPU
2, automatically leased. Whole four-size sweeps alternate AB/BA.
Recorded 1/5/15-minute host loads are 52.01/63.74/60.61 at start
and 46.58/60.67/59.72 at end. Every observation remains, without activity filtering.
The registered inner target is four seconds and the call cap thirty-two seconds;
the exports retain effective targets, spawn floors and repeat counts.

| Block | Columns | Reference ms/call | Native frame ms/call | B/A |
| --- | ---: | ---: | ---: | ---: |
| 0 | 64 | 0.3805 | 0.3154 | 0.8291 |
| 0 | 128 | 1.8801 | 1.1583 | 0.6161 |
| 0 | 256 | 6.6380 | 6.4249 | 0.9679 |
| 0 | 512 | 44.3274 | 38.4637 | 0.8677 |
| 1 | 64 | 0.3255 | 0.2598 | 0.7980 |
| 1 | 128 | 1.2631 | 1.3380 | 1.0593 |
| 1 | 256 | 6.7061 | 5.6643 | 0.8447 |
| 1 | 512 | 57.9214 | 34.9164 | 0.6028 |

All four exported cubic-model verdicts are inconclusive. Their normalized slopes
are −0.759/−0.674 in the first A/B sweeps and −0.517/−0.671 in the second A/B sweeps.
These finite timings do not establish the declared asymptotic model or a uniform
speedup. Input size, cache effects and variability remain relevant; no cause is
inferred from the fit alone.

This is standalone matrix evidence. It measures neither F4 candidate production,
certificate generation, independent native verification nor kernel checking.
It establishes no external-comparator or fastest-open-source milestone. The
existing F4 route and deterministic reference remain unchanged.

- [Raw capsule](raw/matrix-state-initial-87692e081b76.tar.gz): `04873020a4805fdeecab70bd231d724928fe11a9bb1c8c21bb632b14c0a96ef1`;
  153 exact Git source blobs and 172 payload digests checked after packing.
