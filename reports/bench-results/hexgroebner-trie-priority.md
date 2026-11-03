# Reducer priority bounds and bounded native lookup

Reducer tries cache the minimum descendant-leaf priority in their existing
packed records. Validation checks each cache against its children. Lookup
skips a subtree that cannot improve the selected divisor and finishes when a
divisor attains the root bound. Zero retains the legacy unknown-bound meaning.
The independent unpruned traversal checks the selected reducer policy.
The final revision tests the global bound only on divisor selection, avoiding
an extra conditional on every node visit.

Validated views admit at most 16384 nodes and 16383 edges. Validation and a
complete query each inspect at most 32767 node/edge records. Native queries
use a fixed 16384-entry stack and 32768-unit bound, covering every admitted
view without discarded speculative work. Larger formats decline before traversal.
Earlier 4096-unit experiments and the conservative 2048-node dispatch stage
are superseded; all their completed observations remain available.

The final measured and verified runtime fingerprint is `20c0f7e7df0d`.
Final verification binds runtime and test-source blobs to recorded manifests.
All eight Clang/GCC sanitizer, SIMD/scalar and remainder variants and all nine
project checks pass. Earlier failed stale-cost/fixture-freshness gates are
retained separately. The fixture audit finds 286 changed
`work` values, 447 `serialWork` values and
289 `referenceWork` values, among 448 of 1134 records.
Every other field and basis agrees, and all changed work values decrease.
Verification collectors and their host-specific commands are bundled.

All sweeps use the same fourteen medium development inputs, seven families
at 32003 and 2147483647, grevlex and degree scheduling. Every run uses one
automatically leased CPU and one algorithm thread, with adjacent AB then BA.
All 672 processes and 336 complete-basis comparisons are retained;
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
| `trie-format/combined` | `a1eb7697c27d` → `20c0f7e7df0d` | 1.0120 | 1.0101 | 0.996500 | 0.890–1.224 | 81 | 93928/93508 |
| `trie-format/control` | `49de4cd1c280` → `20c0f7e7df0d` | 0.9920 | 0.9826 | 1.000000 | 0.606–1.251 | 44 | 94324/93604 |

The medium sweeps did not encode any newly admitted 2049–16384-node views: allocation counters match the original 2048-node-format baseline under the ample measurement allowances. Their timing observations therefore do not measure full-F4 widening costs or benefits. Larger-format coverage comes from synthetic lookup kernels and representation/budget conformance tests. No real-system widening speedup is established.

Smaller ratios mean less observed time or charged work. All non-work JSON fields and complete bases agree, including allocation counters. Shared-host variability remains in every observation; no significance threshold or causal attribution is inferred from these finite sweeps.

| Final combined family | Process ratio |
| --- | ---: |
| cyclic | 1.0068 |
| kat | 1.0070 |
| eco | 0.9997 |
| noon | 1.0281 |
| reimer | 1.0127 |
| minrank | 1.0249 |
| dense-quadratic | 1.0049 |

The antichain kernel prepares n two-variable monomial reducers outside timing. The dispatch kernel uses native lookup at every declared size; the other kernel always uses the node traversal. The query admits every reducer; scanning the root edges and the first preferred branch takes n+4 charged units. It hashes the actual selected leading monomial and work. Native and portable traversals use separate fixed trial-major schedules, three trials at each declared size. All completed samples, including signal-floor flags, remain available. The table takes medians over every completed trial; the engine verdict omits samples flagged below its signal floor.

| Reducers | Dispatch ms | Portable ms |
| ---: | ---: | ---: |
| 16 | 0.000149 | 0.000355 |
| 32 | 0.000150 | 0.000466 |
| 64 | 0.000156 | 0.000659 |
| 128 | 0.000181 | 0.001044 |
| 256 | 0.000252 | 0.001750 |
| 512 | 0.000337 | 0.003093 |
| 1024 | 0.000517 | 0.005772 |
| 2048 | 0.000877 | 0.011145 |

These independent complexity runs are not a matched native/portable speedup experiment. Dispatch lean-bench verdict: `inconclusive`, normalized slope -0.571959, 1 of 24 completed samples marked below the signal floor. Portable lean-bench verdict: `inconclusive`, normalized slope -0.229818, 0 of 24 completed samples marked below the signal floor.

The fastest-open-source milestone remains unestablished. These changes use available compiler/runtime facilities and establish no language impossibility. Issue #10987 remains open.

Campaigns: [f4-trie-priority-49de4cd1c280.tar.xz](raw/f4-trie-priority-49de4cd1c280.tar.xz), SHA-256 `4cd6bcdd8bd0c94413a0f3329f9c8efca7985b58ef5bee0253a2b7c4e8cda38b`, 3265 payloads plus manifest.

Intermediate baseline: [f4-sampling-58952f05cd8c.tar.xz](raw/f4-sampling-58952f05cd8c.tar.xz), SHA-256 `ded8064872e6191962b8c973d5b2d0299dd294297d00ff77a021e359de5f0148`, 601 payloads plus manifest.

Final baseline: [f4-sampling-a1eb7697c27d.tar.xz](raw/f4-sampling-a1eb7697c27d.tar.xz), SHA-256 `99a522cf1785f60cf2541b438c1d0f2758b8a70dab0b30de81163488236784b1`, 601 payloads plus manifest.

Final format measurements: [f4-trie-format-20c0f7e7df0d.tar.xz](raw/f4-trie-format-20c0f7e7df0d.tar.xz), SHA-256 `8c32eeb18a5546dcceabe4f0c5e96ee041696f85c738663c3d1848fd669e05de`, 604 payloads plus manifest.

Fixture baseline: [f4-sampling-checks-0b5c579aa3eb.tar.xz](raw/f4-sampling-checks-0b5c579aa3eb.tar.xz), SHA-256 `1792e2117dcf389ac3feffc21bb52beec4dbfe31a334b7717345b62f143044f5`, 145 payloads plus manifest.

Final verification: [f4-trie-priority-checks-550e98d5e854.tar.xz](raw/f4-trie-priority-checks-550e98d5e854.tar.xz), SHA-256 `8c6d8c9ed7272d876f61ccc304420dc35b24d6ed6a5728a69198fb692911fc58`, 333 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_trie_report.py --archive reports/bench-results/raw/f4-trie-priority-49de4cd1c280.tar.xz --format reports/bench-results/raw/f4-trie-format-20c0f7e7df0d.tar.xz --fixture-baseline reports/bench-results/raw/f4-sampling-checks-0b5c579aa3eb.tar.xz --intermediate-baseline reports/bench-results/raw/f4-sampling-58952f05cd8c.tar.xz --final-baseline reports/bench-results/raw/f4-sampling-a1eb7697c27d.tar.xz --guards reports/bench-results/raw/f4-trie-priority-checks-550e98d5e854.tar.xz --report reports/bench-results/hexgroebner-trie-priority.md --check`. Historical checks use archived blobs; add `--current` to require current runtime/test identity.

The earlier [verification capsule](raw/f4-trie-priority-checks-7affce133f75.tar.xz) is retained for the conservative dispatch snapshot.
