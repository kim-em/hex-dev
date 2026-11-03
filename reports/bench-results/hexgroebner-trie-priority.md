# Reducer priority bounds and bounded native lookup

Reducer tries cache the minimum descendant-leaf priority in their existing
packed records. Validation checks each cache against its children. Lookup
skips a subtree that cannot improve the selected divisor and finishes when a
divisor attains the root bound. Zero retains the legacy unknown-bound meaning.
The independent unpruned traversal checks the selected reducer policy.
The final revision tests the global bound only on divisor selection, avoiding
an extra conditional on every node visit.

Validated views admit at most 16384 nodes and 16383 edges. Validation inspects
at most 32767 records; each lookup separately retains its 4096-unit work cap.
Native dispatch admits only trees with at most 2048 nodes, whose complete
walks fit 4095 units. Larger views decline before any traversal and use
portable priority pruning under the actual parent allowance. Earlier native
experiments discarded attempted work on quantum decline; those superseded
sources and observations are retained. The final implementation avoids that
unaccounted speculative traversal, including for filtered large queries.

The measured runtime fingerprint is `49de4cd1c280`. The selected
source `4cc86f34dd0a` adds only the portable benchmark cost-model comment
and freshly reproduces all three executables byte-identically. Final verification binds
both runtime and test-source blobs to their recorded manifests. All eight
Clang/GCC sanitizer, SIMD/scalar and remainder variants and all nine project
checks pass. Earlier experimental sources, checks and failed stale-cost/fixture-freshness gates are retained separately.
The regenerated fixture changes only three work fields across 1,134 records;
all other fields agree. The final guard uses the exact pruned charges.
Verification collectors and their host-specific commands are bundled.

All sweeps use the same fourteen medium development inputs, seven families
at 32003 and 2147483647, grevlex and degree scheduling. Every run uses one
automatically leased CPU and one algorithm thread, with adjacent AB then BA.
All 560 processes and 280 complete-basis comparisons are retained;
none failed or timed out. Campaigns are separate observations. The wide-view
stage and the superseded global-bound comparison each have one unchanged repeat;
none is pooled with its first observation.
Candidate time includes canonicalization, F4 and interreduction. Process time
also includes startup, parsing and full output under identical wrappers.
Certificate generation, independent verification and kernel checking are
outside timing. These inputs are not held out and establish no leadership.

| Campaign | Baseline → candidate | Process ratio | Candidate ratio | Charged work ratio | Process range | CPU | Peak RSS A/B KiB |
| --- | --- | ---: | ---: | ---: | --- | ---: | --- |
| `trie-bound/before-after` | `58952f05cd8c` → `a4ae297e63a8` | 1.0044 | 0.9928 | 0.996515 | 0.676–1.456 | 76 | 80848/84348 |
| `trie-wide/before-after` | `a1eb7697c27d` → `fb9de0864fee` | 0.9479 | 0.8490 | 0.996515 | 0.402–1.717 | 50 | 87156/79380 |
| `trie-wide/before-after-repeat` | `a1eb7697c27d` → `fb9de0864fee` | 0.9671 | 1.0528 | 0.996515 | 0.365–1.891 | 13 | 91252/94016 |
| `trie-global/combined` | `a1eb7697c27d` → `403b929c0433` | 1.1174 | 1.1449 | 0.996500 | 0.642–2.494 | 2 | 85608/79212 |
| `trie-global/combined-repeat` | `a1eb7697c27d` → `403b929c0433` | 1.0038 | 1.0039 | 0.996500 | 0.846–1.206 | 52 | 94036/94172 |
| `trie-global/early-stop` | `fb9de0864fee` → `403b929c0433` | 0.9178 | 0.9950 | 0.999985 | 0.374–1.341 | 93 | 77720/87416 |
| `trie-direct/combined` | `a1eb7697c27d` → `75429d0355a5` | 1.0074 | 1.0046 | 0.996500 | 0.853–1.270 | 21 | 93992/94260 |
| `trie-direct/control` | `403b929c0433` → `75429d0355a5` | 1.0093 | 1.0113 | 1.000000 | 0.852–1.229 | 22 | 94156/94260 |
| `trie-bounded/combined` | `a1eb7697c27d` → `49de4cd1c280` | 1.0002 | 1.0073 | 0.996500 | 0.791–1.224 | 63 | 93992/93984 |
| `trie-bounded/control` | `75429d0355a5` → `49de4cd1c280` | 1.0092 | 1.0053 | 1.000000 | 0.829–1.210 | 25 | 94292/93984 |

Smaller ratios mean less observed time or charged work. All non-work JSON fields and complete bases agree, including allocation counters. Shared-host variability remains in every observation; no significance threshold or causal attribution is inferred from these finite sweeps.

| Final combined family | Process ratio |
| --- | ---: |
| cyclic | 1.0121 |
| kat | 1.0036 |
| eco | 1.0032 |
| noon | 0.9953 |
| reimer | 1.0185 |
| minrank | 1.0211 |
| dense-quadratic | 0.9492 |

The antichain kernel prepares n two-variable monomial reducers outside timing. The dispatch kernel uses native lookup through n=512 and portable fallback at n=1024 and 2048; the other kernel always uses the node traversal. The query admits every reducer; scanning the root edges and the first preferred branch takes n+4 charged units. It hashes the actual selected leading monomial and work. Native and portable traversals use separate fixed trial-major schedules, three trials at each declared size. All completed samples, including signal-floor flags, remain available. The table takes medians over every completed trial; the engine verdict omits samples flagged below its signal floor.

| Reducers | Dispatch ms | Portable ms |
| ---: | ---: | ---: |
| 16 | 0.000140 | 0.000369 |
| 32 | 0.000146 | 0.000482 |
| 64 | 0.000160 | 0.000677 |
| 128 | 0.000189 | 0.001057 |
| 256 | 0.000259 | 0.001778 |
| 512 | 0.000373 | 0.003125 |
| 1024 | 0.005845 | 0.005817 |
| 2048 | 0.011184 | 0.011137 |

These independent complexity runs are not a matched native/portable speedup experiment. Dispatch lean-bench verdict: `consistent_with_declared_complexity`, normalized slope 0.077026, 0 of 24 completed samples marked below the signal floor. Portable lean-bench verdict: `inconclusive`, normalized slope -0.237090, 0 of 24 completed samples marked below the signal floor.

The fastest-open-source milestone remains unestablished. These changes use available compiler/runtime facilities and establish no language impossibility. Issue #10987 remains open.

Campaigns: [f4-trie-priority-49de4cd1c280.tar.xz](raw/f4-trie-priority-49de4cd1c280.tar.xz), SHA-256 `4cd6bcdd8bd0c94413a0f3329f9c8efca7985b58ef5bee0253a2b7c4e8cda38b`, 3265 payloads plus manifest.

Intermediate baseline: [f4-sampling-58952f05cd8c.tar.xz](raw/f4-sampling-58952f05cd8c.tar.xz), SHA-256 `ded8064872e6191962b8c973d5b2d0299dd294297d00ff77a021e359de5f0148`, 601 payloads plus manifest.

Final baseline: [f4-sampling-a1eb7697c27d.tar.xz](raw/f4-sampling-a1eb7697c27d.tar.xz), SHA-256 `99a522cf1785f60cf2541b438c1d0f2758b8a70dab0b30de81163488236784b1`, 601 payloads plus manifest.

Final verification: [f4-trie-priority-checks-7affce133f75.tar.xz](raw/f4-trie-priority-checks-7affce133f75.tar.xz), SHA-256 `fc0d17e4c9a8808700ac03a42b11acd2599d26d986f42984a14500da25907273`, 333 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_trie_report.py --archive reports/bench-results/raw/f4-trie-priority-49de4cd1c280.tar.xz --intermediate-baseline reports/bench-results/raw/f4-sampling-58952f05cd8c.tar.xz --final-baseline reports/bench-results/raw/f4-sampling-a1eb7697c27d.tar.xz --guards reports/bench-results/raw/f4-trie-priority-checks-7affce133f75.tar.xz --report reports/bench-results/hexgroebner-trie-priority.md --check`. Historical checks use archived blobs; add `--current` to require current runtime/test identity.
