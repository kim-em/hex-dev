# Sampled F4 and owned phase transitions

`Sampled.computeWith` is an opt-in unchecked candidate producer. It samples full-field
linear combinations of fixed row blocks with explicit advanced SplitMix64 rejection
state and stops each block after a configured total number of zero reductions.
Rows remain in the input row space, but rank can be missed. No independence,
uniform-sampling error bound, checked-computation speedup or leadership is claimed.
An independent complete-basis certificate is required. Automatic checked retry,
fallback and sampled trace reuse remain outstanding.

The current measured runtime fingerprint is `58952f05cd8c`. Source commits,
compiler revisions, fresh build logs and
binary hashes are in the capsule. Frozen sources rebuild through `lake build`;
executables are identified but not bundled. The sampler leaves deterministic
production as the default.

All campaigns use the same 14 medium development inputs: cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over 32003 and 2147483647,
grevlex and degree scheduling. One automatically leased CPU and one algorithm
thread run adjacent AB then BA per input. Seed 10987, blocks of 32 and three total
zero tests are fixed for sampled arms. All 504 processes and 252 complete-basis comparisons are
retained, including regressions; none failed or timed out. Each campaign stands
alone. There are no held-out inputs or performance acceptance results here.

Candidate time covers normalization, F4 and interreduction. Process time also
includes startup, parsing and complete output under identical GNU-time wrappers.
Neither includes certificate generation, independent verification
or kernel checking. Values below are candidate/baseline ratios; smaller is faster.
The balanced suite gives equal weight to each family. Small differences remain
inconclusive under shared-host variability. The frame change has one unchanged
repeat; no campaigns are pooled or selected as best runs.

| Campaign | Baseline → candidate runtime | CPU | Process geometric mean | Candidate geometric mean | Process pair range | Peak RSS A/B (KiB) | Observation |
| --- | --- | ---: | ---: | ---: | --- | --- | --- |
| `sampled/before-after` | `b6822c6a5f65` → `387910880bdc` | 19 | 1.1368 | 1.1379 | 0.272–1.709 | 83516/71660 | regression |
| `sampled-owned/before-after` | `387910880bdc` → `4d4e4b4f3348` | 4 | 0.9798 | 0.9892 | 0.751–1.232 | 71368/71724 | inconclusive |
| `sampled-frame/before-after` | `4d4e4b4f3348` → `01736fe0bf82` | 81 | 0.9456 | 0.8156 | 0.220–4.042 | 67224/71032 | inconclusive |
| `sampled-frame/before-after-repeat` | `4d4e4b4f3348` → `01736fe0bf82` | 21 | 1.0120 | 1.0112 | 0.753–1.231 | 75668/70856 | inconclusive |
| `sampled-frame/deterministic` | `b6822c6a5f65` → `01736fe0bf82` | 46 | 1.1775 | 1.1600 | 0.442–1.942 | 96088/70960 | regression |
| `sampled-abi/before-after` | `3476217e65f8` → `b865a5399fec` | 40 | 0.8968 | 0.8846 | 0.607–1.212 | 75840/85964 | lower in this run |
| `sampled-abi/deterministic` | `b6822c6a5f65` → `b865a5399fec` | 80 | 1.0844 | 1.1599 | 0.821–1.537 | 96216/85904 | regression |
| `sampled-reviewed/deterministic` | `58952f05cd8c` → `58952f05cd8c` | 44 | 1.0629 | 1.1324 | 0.813–1.564 | 94248/86216 | regression |
| `sampled-reviewed/refactor` | `b6822c6a5f65` → `58952f05cd8c` | 62 | 0.9960 | 0.9988 | 0.848–1.211 | 96216/94248 | inconclusive |

`3476217e65f8` identifies `sampled-install`, the isolated reducer-install helper and registered-kernel baseline before owned ABI controls. The seven earlier campaigns retain their original sources. The current two campaigns use bounded scan ranges, atomic inverse admission, shared F4 stages and retained candidate provenance. The current `deterministic` campaign compares sampler B with current deterministic A; `refactor` compares current deterministic B with retained deterministic A. The deterministic refactor observation is inconclusive; the current sampler still regresses overall. CPU values are recorded collection context, not per-process placement attestations.

The final sampler remains slower overall than deterministic F4. Its direct per-family process ratios are:

| Family | Ratio |
| --- | ---: |
| cyclic | 0.9820 |
| kat | 1.0179 |
| eco | 0.8254 |
| noon | 1.3618 |
| reimer | 1.1705 |
| minrank | 1.0427 |
| dense-quadratic | 1.1178 |

Known-pivot installation uses a fixed trial-major lean-bench schedule, three outer
trials at every declared input from 128 to 8192. Preparation is excluded; full
pivot decoding, hashing and counters are included. These are separate complexity
runs, not a matched AB/BA speedup experiment. The two historical ABI campaigns
have 21 equal result hashes; the current bounded-range implementation has different
work counters and its hashes are not equated with those historical values.

| Known reducers | Historical borrowed ABI (ms) | Historical owned ABI (ms) | Current owned ABI (ms) |
| ---: | ---: | ---: | ---: |
| 128 | 0.0542 | 0.0354 | 0.0366 |
| 256 | 0.1248 | 0.0664 | 0.0688 |
| 512 | 0.3089 | 0.1289 | 0.1320 |
| 1024 | 0.9301 | 0.2562 | 0.2633 |
| 2048 | 3.1435 | 0.5056 | 0.5194 |
| 4096 | 11.1071 | 1.0304 | 1.0397 |
| 8192 | 39.7895 | 2.0745 | 2.0825 |

Lean-bench reports `inconclusive` before and `consistent_with_declared_complexity` after. The normalized log slopes are 0.681312 and -0.005587.

The current kernel reports `consistent_with_declared_complexity` with normalized slope -0.013865.

The untimed array-push diagnostic counts exactly n(n−1)/2 existing pivot-array
elements exposed to shared pushes before the ABI control, and zero afterward,
at all six retained sizes. The final runtime uses Lean's available exported owned
ABI for consuming phase functions, releases buffers before extending them and
removes the outer driver's extra matrix owner. Real caller snapshots retain
immutable contents. This is an implemented workaround using the current compiler,
not evidence that the performance goal requires a language change.

The retained Eco11 M31 cycle profiles report array copying and reference-count
cleanup in the initial sampler; subtract arithmetic is a small fraction. Profile
reports and hashes of the original binary perf traces are bundled; the traces
remain in the measurement workspace. The ownership interposer supplies direct
copy-count evidence independently of that sampled profile.

Native/scalar/resumption comparisons cover 1,134 systems. Independent complete-basis
certification accepts 1,124 and rejects ten sampled misses; the forced F2 miss is
also rejected. Ordinary F2 polynomials retain ordinary exponents. All eight native
compiler/sanitizer variants pass, including fresh pivot ownership and bounded native
composition checks. Fresh known-reducer and generated-target pivot arrays copy
zero existing elements; these counters do not measure every ByteArray copy.
Retained scan/gather snapshots separately check immutability. Parent-budget tests
cover every resource plus ten interruptions in matrix and atomic F4 stages.
Both driver initializers agree on the corpus and continue cooperative suspensions. The full project
checks cover independent oracles, kernel replay/axiom audit, bench verification,
dependency DAG, phase, release manifest, headers and file lengths. Kernel agreement
theorems compare the portable Lean definitions; native-provider agreement is tested.
The current staged runtime is byte-bound to the measured source manifest and
the source identifiers in the verification records. Historical snapshots and
verification remain separate from the current implementation.

Raw evidence: `f4-sampling-b865a5399fec.tar.xz`, SHA-256 `d964d4fc22f1c0f62f1fe98f9548803bb70518f23bfe6518f021928a68e64068`, 2621 payloads plus manifest. Current measurements: `f4-sampling-58952f05cd8c.tar.xz`, SHA-256 `ded8064872e6191962b8c973d5b2d0299dd294297d00ff77a021e359de5f0148`, 601 payloads plus manifest. Verification: `f4-sampling-checks-ad855e8a2e.tar.xz`, SHA-256 `2e81daf04b905051ce69506339edff81c63e9e55b4e902322d5b0ea684430199`, 26 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_sampling_report.py --archive reports/bench-results/raw/f4-sampling-b865a5399fec.tar.xz --reviewed reports/bench-results/raw/f4-sampling-58952f05cd8c.tar.xz --guards reports/bench-results/raw/f4-sampling-checks-ad855e8a2e.tar.xz --report reports/bench-results/hexgroebner-sampling.md --check`. Every consumed payload is verified against its capsule manifest; ratios, complete outputs and runtime source blobs are independently recomputed or checked.
