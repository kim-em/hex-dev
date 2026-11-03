# Sampled F4 and owned phase transitions

`Sampled.computeWith` is an opt-in unchecked candidate producer. It samples full-field
linear combinations of fixed row blocks with explicit advanced SplitMix64 rejection
state and stops each block after a configured total number of zero reductions.
Rows remain in the input row space, but rank can be missed. No independence,
uniform-sampling error bound, checked-computation speedup or leadership is claimed.
An independent complete-basis certificate is required. Automatic checked retry,
fallback and sampled trace reuse remain outstanding.

The final measured runtime fingerprint is `b865a5399fec`. Its original source commit,
rebased byte-identical source identity, compiler revision, fresh build logs and
binary hashes are in the capsule. Frozen sources rebuild through `lake build`;
executables are identified but not bundled. The sampler leaves deterministic
production as the default.

All campaigns use the same 14 medium development inputs: cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over 32003 and 2147483647,
grevlex and degree scheduling. One automatically leased CPU and one algorithm
thread run adjacent AB then BA per input. Seed 10987, blocks of 32 and three total
zero tests are fixed. All 392 processes and 196 complete-basis comparisons are
retained, including regressions; none failed or timed out. Each campaign stands
alone. There are no held-out inputs or performance acceptance results here.

Candidate time covers normalization, F4 and interreduction. Process time also
includes startup, parsing and complete output under identical GNU-time wrappers.
Neither includes certificate generation, independent verification
or kernel checking. Values below are candidate/baseline ratios; smaller is faster.
The balanced suite gives equal weight to each family. Small differences remain
inconclusive under shared-host variability. The frame change has one unchanged
repeat; no campaigns are pooled or selected as best runs.

| Campaign | Baseline → candidate runtime | CPU | Process geometric mean | Candidate geometric mean | Process pair range | Peak RSS A/B (KiB) |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `sampled/before-after` | `b6822c6a5f65` → `387910880bdc` | 19 | 1.1368 | 1.1379 | 0.272–1.709 | 83516/71660 |
| `sampled-owned/before-after` | `387910880bdc` → `4d4e4b4f3348` | 4 | 0.9798 | 0.9892 | 0.751–1.232 | 71368/71724 |
| `sampled-frame/before-after` | `4d4e4b4f3348` → `01736fe0bf82` | 81 | 0.9456 | 0.8156 | 0.220–4.042 | 67224/71032 |
| `sampled-frame/before-after-repeat` | `4d4e4b4f3348` → `01736fe0bf82` | 21 | 1.0120 | 1.0112 | 0.753–1.231 | 75668/70856 |
| `sampled-frame/deterministic` | `b6822c6a5f65` → `01736fe0bf82` | 46 | 1.1775 | 1.1600 | 0.442–1.942 | 96088/70960 |
| `sampled-abi/before-after` | `3476217e65f8` → `b865a5399fec` | 40 | 0.8968 | 0.8846 | 0.607–1.212 | 75840/85964 |
| `sampled-abi/deterministic` | `b6822c6a5f65` → `b865a5399fec` | 80 | 1.0844 | 1.1599 | 0.821–1.537 | 96216/85904 |

The final sampler remains slower overall than deterministic F4. Its direct per-family process ratios are:

| Family | Ratio |
| --- | ---: |
| cyclic | 0.9736 |
| kat | 1.0447 |
| eco | 0.8375 |
| noon | 1.4612 |
| reimer | 1.2014 |
| minrank | 1.0865 |
| dense-quadratic | 1.0856 |

Known-pivot installation uses a fixed trial-major lean-bench schedule, three outer
trials at every declared input from 128 to 8192. Preparation is excluded; full
pivot decoding, hashing and counters are included. These are separate complexity
runs, not a matched AB/BA speedup experiment. All 21 result hashes agree.

| Known reducers | Borrowed ABI median (ms) | Owned ABI median (ms) |
| ---: | ---: | ---: |
| 128 | 0.0542 | 0.0354 |
| 256 | 0.1248 | 0.0664 |
| 512 | 0.3089 | 0.1289 |
| 1024 | 0.9301 | 0.2562 |
| 2048 | 3.1435 | 0.5056 |
| 4096 | 11.1071 | 1.0304 |
| 8192 | 39.7895 | 2.0745 |

Lean-bench reports `inconclusive` before and `consistent_with_declared_complexity` after. The normalized log slopes are 0.681312 and -0.005587.

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
composition checks. Both driver initializers agree on the corpus. The full project
checks cover independent oracles, kernel replay/axiom audit, bench verification,
dependency DAG, phase, release manifest, headers and file lengths. Kernel agreement
theorems compare the portable Lean definitions; native-provider agreement is tested.
The final source differs from the measured runtime snapshot by two adjacent portable
cost-model comment lines. Its rebuilt benchmark is byte-identical. The exact source
delta, build identity and project-check records are retained in the verification capsule.

Raw evidence: `f4-sampling-b865a5399fec.tar.xz`, SHA-256 `d964d4fc22f1c0f62f1fe98f9548803bb70518f23bfe6518f021928a68e64068`, 2621 payloads plus manifest. Verification: `f4-sampling-checks-1fbc86e53a.tar.xz`, SHA-256 `bd92eaf6570eae65d0c85eac724b0042772ba34d252d5bf8fc14663f6f947f59`, 30 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_sampling_report.py --archive reports/bench-results/raw/f4-sampling-b865a5399fec.tar.xz --guards reports/bench-results/raw/f4-sampling-checks-1fbc86e53a.tar.xz --report reports/bench-results/hexgroebner-sampling.md --check`. Every consumed payload is verified against its capsule manifest; ratios, complete outputs and runtime source blobs are independently recomputed or checked.
