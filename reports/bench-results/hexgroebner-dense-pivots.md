# Checked dense pivots: kernels and complete F4 observations

Dense pivot buffers preserve their exact sparse sources through typed cache
provenance. Preparation reserves its work and packed payload against the parent
allowances. Dense updates preserve zero gaps, invalid-target prefixes, pending
cursors and trace events. The deterministic continuation and whole-eliminator
proofs include preparation charges. Final runtime `b672e7fcc65e` and
verification sources `467877f9757b` pass eight Clang/GCC sanitizer variants
and nine project gates. One synthetic 174-variable linear-ideal F4 fixture exercises exactly one native
dense update in each compiler variant. Kernel checking remains separate from native testing.

The experimental option defaults off. Only M31 matrices admit caches; narrower
fields retain their existing kernels. A proved active-cache bit preserves sparse
dispatch when no cache exists. Admission selects non-contiguous spans at least
three-quarter full, 128–4096 nonzero entries and at most 65536 columns. Fully
contiguous rows retain the existing contiguous sparse SIMD path. Certificate
production and sampled computation retain their sparse routes.

The kernel input has 128–4096 nonzero entries over M31. Each output byte is
consumed. The first experiment times one pending update, including full output
hashing. The next experiment performs 64 owned updates and consumes the full
final output once. Preparation is excluded in both. Complexity ladders use three
fixed trial-major trials. Matched comparisons use adjacent sparse/dense then
dense/sparse arms at every declared size, with increasing recorded timestamps.
All 105 benchmark invocations and 48 matched pairs remain available.
No completed sample was rerun or filtered. Two matched half-full samples are
below the signal floor; their commands return an inconclusive status and their
observations remain in the descriptive ratios.

| Kernel | Dense/sparse ratio | Signal-floor samples in matched pairs |
| --- | ---: | ---: |
| Single, half full | 0.9918 | 0 |
| 64 updates, half full | 0.9458 | 2 |
| 64 updates, three-quarter full | 0.7329 | 0 |
| 64 updates, full | 1.0325 | 0 |

| Nonzero entries | Single half | 64 half | 64 three-quarter | 64 full |
| ---: | ---: | ---: | ---: | ---: |
| 128 | 1.0091 | 0.9856 | 0.8330 | 1.0181 |
| 256 | 1.0124 | 0.9792 | 0.7640 | 1.0300 |
| 512 | 0.9431 | 0.9709 | 0.7272 | 0.9813 |
| 1024 | 0.9980 | 0.9317 | 0.7120 | 1.0236 |
| 2048 | 0.9957 | 1.0129 | 0.6925 | 1.0777 |
| 4096 | 0.9939 | 0.8096 | 0.6791 | 1.0674 |

The three-quarter-full kernel benefits from contiguous updates. Fully dense rows
already have a contiguous sparse path. The single-update diagnostic profiles
include four fixed AB/BA recordings with no lost samples: output hashing takes
about half the sampled cycles and row updates about 37% on that input. Profiles
explain that experiment; they are not independent timing evidence or a compiler
impossibility claim.

All complete-F4 sweeps use fourteen development inputs in seven families at
15- and 31-bit primes, grevlex, degree scheduling and one algorithm thread.
They compare complete reduced candidates outside timing with matched input,
output and resource contracts. Candidate time includes canonicalization, F4 and
interreduction; process time also includes initialization, parsing and output.
Certificate generation, independent final verification and kernel checking are
excluded. These inputs are not held out and establish no leadership.

The first integration also routed narrow fields and cache-empty matrices through
the dense dispatch. Its negative results are retained. The second integration
restricts dispatch as described above; its control uses the merged trie runtime.
The current integration additionally restores small-matrix bulk frames and
bounds dense updates over partial pending rows.
`enabled` compares caches off/on in the same binary; `control` compares prior
production with caches off; `combined` compares prior production with caches on.
Each campaign independently keeps adjacent AB/BA samples, peak RSS, host context,
all raw outputs and failures. The order audit checks recorded order and the
sequential collector; full-F4 per-process timestamps were not recorded.

| Campaign | Baseline → candidate | Process ratio | Candidate ratio | Work ratio | Allocated-byte delta range | Peak RSS A/B KiB |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `dense-state/enabled` | `6ebe0f52c27e` → `6ebe0f52c27e` | 1.0806 | 1.0943 | 1.000410 | 0–371872 | 94272/96304 |
| `dense-state/control` | `a1eb7697c27d` → `6ebe0f52c27e` | 1.0208 | 1.0187 | 1.000000 | 0–0 | 94036/94272 |
| `dense-state/combined` | `a1eb7697c27d` → `6ebe0f52c27e` | 1.0974 | 1.1166 | 1.000410 | 0–371872 | 94036/96260 |
| `dense-active/enabled` | `7af81facc404` → `7af81facc404` | 1.0301 | 1.0200 | 1.000410 | 0–371872 | 92336/96432 |
| `dense-active/control` | `20c0f7e7df0d` → `7af81facc404` | 1.0118 | 1.0038 | 1.000000 | 0–0 | 94224/92312 |
| `dense-active/combined` | `20c0f7e7df0d` → `7af81facc404` | 1.0034 | 1.0085 | 1.000410 | 0–371872 | 94372/96408 |
| `dense-review/enabled` | `b672e7fcc65e` → `b672e7fcc65e` | 1.0049 | 1.0043 | 1.000410 | 0–371872 | 92340/96436 |
| `dense-review/control` | `20c0f7e7df0d` → `b672e7fcc65e` | 1.0157 | 1.0137 | 1.000000 | 0–0 | 94696/92340 |
| `dense-review/combined` | `20c0f7e7df0d` → `b672e7fcc65e` | 1.0242 | 1.0173 | 1.000410 | 0–371872 | 94696/96436 |

The following ranges retain all 28 paired process and candidate ratios in each campaign. They describe variation across inputs and AB/BA blocks, not confidence intervals. Each prime has fourteen pairs. The 32003 enabled comparison runs the same arithmetic path on both arms and provides an inert control.

| Campaign | Process pair range | Candidate pair range | p=32003 process / candidate | p=2147483647 process / candidate |
| --- | --- | --- | ---: | ---: |
| `dense-state/enabled` | 0.8057–1.3956 | 0.9678–1.4038 | 1.1351 / 1.1651 | 1.0287 / 1.0278 |
| `dense-state/control` | 0.8712–1.2332 | 0.9704–1.0635 | 1.0240 / 1.0176 | 1.0177 / 1.0197 |
| `dense-state/combined` | 0.8374–1.3935 | 0.9364–1.4095 | 1.1607 / 1.1833 | 1.0375 / 1.0536 |
| `dense-active/enabled` | 0.8706–1.3803 | 0.9076–1.1858 | 1.0295 / 1.0166 | 1.0306 / 1.0234 |
| `dense-active/control` | 0.8596–1.2217 | 0.9003–1.0737 | 1.0162 / 1.0108 | 1.0074 / 0.9968 |
| `dense-active/combined` | 0.8808–1.0794 | 0.8939–1.0870 | 0.9885 / 0.9917 | 1.0185 / 1.0257 |
| `dense-review/enabled` | 0.7986–1.3067 | 0.9356–1.1189 | 0.9973 / 0.9993 | 1.0125 / 1.0093 |
| `dense-review/control` | 0.8857–1.1939 | 0.9080–1.2486 | 1.0074 / 1.0020 | 1.0240 / 1.0255 |
| `dense-review/combined` | 0.8372–1.2575 | 0.8741–1.0704 | 1.0288 / 1.0121 | 1.0197 / 1.0225 |

The `dense-active` control × enabled process ratios give 1.0422, while its independently collected combined campaign gives 1.0034. This discrepancy exceeds the reported 1–3% point effects. These campaigns cannot attribute a speedup or slowdown to the dense kernel. Both default-off controls exceed 1; these observations do not distinguish default-path overhead from host variation and do not establish that the new path is free.

All 504 complete-F4 processes / 252 matched pairs complete with equal bases. Shared-host variability is retained; these descriptive sweeps establish no overall speedup. The option remains disabled by default. The fastest-open-source milestone and remaining compiler/runtime investigation remain open under #10987.

For the current integration, control × enabled gives 1.0206, versus 1.0242 in the independent combined campaign. Its default-off control also exceeds 1; the attribution limitation remains.

Separate untimed instrumented executions record native usage for every input with the option off and on. Clang and GCC agree exactly, and complete candidate outputs and counters agree with the timed source. These sanitizer executions are coverage observations and are excluded from timings.

| Input | Preparation calls / admitted on | Dense scan calls / packets on | Bulk accepted off / on | Bulk declined off / on |
| --- | ---: | ---: | --- | --- |
| cyclic7-15 | 0 / 0 | 0 / 0 | 9 / 9 | 19 / 19 |
| cyclic7-31 | 444 / 444 | 17345 / 71946 | 9 / 4 | 19 / 24 |
| eco11-15 | 0 / 0 | 0 / 0 | 7 / 7 | 14 / 14 |
| eco11-31 | 18 / 0 | 0 / 0 | 7 / 3 | 14 / 18 |
| kat8-15 | 0 / 0 | 0 / 0 | 5 / 5 | 5 / 5 |
| kat8-31 | 21 / 0 | 0 / 0 | 5 / 2 | 5 / 8 |
| minrank_d_2_p_2_q_4_r_2-15 | 0 / 0 | 0 / 0 | 5 / 5 | 0 / 0 |
| minrank_d_2_p_2_q_4_r_2-31 | 0 / 0 | 0 / 0 | 5 / 5 | 0 / 0 |
| noon5-15 | 0 / 0 | 0 / 0 | 7 / 7 | 4 / 4 |
| noon5-31 | 0 / 0 | 0 / 0 | 7 / 3 | 4 / 8 |
| quadratic6-15 | 0 / 0 | 0 / 0 | 8 / 8 | 0 / 0 |
| quadratic6-31 | 1 / 0 | 0 / 0 | 8 / 7 | 0 / 1 |
| reimer6-15 | 0 / 0 | 0 / 0 | 16 / 16 | 10 / 10 |
| reimer6-31 | 16 / 15 | 4013 / 326 | 16 / 5 | 10 / 21 |

The current integration preserves bulk-frame eligibility for M31 matrices of at most 128 columns. Dense packets cover bounded pending prefixes after pivot selection or suspension, with a local span bound; rejected packets retain sparse updates. The selected-pivot kernel includes the selection tick in each of 64 updates and resumes the final entry of 4096-entry rows in a second call. Its 26 invocations / 12 matched pairs give a dense/sparse geometric mean of 0.7330, with 0 matched samples below the signal floor. Preparation remains excluded.

| Selected-pivot nonzeros | Dense/sparse ratio |
| ---: | ---: |
| 128 | 0.8436 |
| 256 | 0.7456 |
| 512 | 0.7226 |
| 1024 | 0.7142 |
| 2048 | 0.6858 |
| 4096 | 0.6967 |

| Final combined family | Process ratio |
| --- | ---: |
| cyclic | 1.0465 |
| kat | 1.0595 |
| eco | 0.9749 |
| noon | 1.0168 |
| reimer | 1.0557 |
| minrank | 1.0058 |
| dense-quadratic | 1.0131 |

An earlier unselected C-local row-shape cache retains 112 process samples / 56 matched deterministic and sampled comparisons in the experiment capsule. Its process ratios are 1.0035 (deterministic) and 0.9965 (sampled). Its complete outputs agree and it establishes no benefit; that cache is absent from the implementation. The diagnostic profiles and all native-check snapshots are retained with their exact source manifests.

Kernel and unselected experiments: [f4-dense-experiments-afec08f91ee7.tar.xz](raw/f4-dense-experiments-afec08f91ee7.tar.xz), SHA-256 `e03503434f4b649f176e36e5c9adc73d525d88d3c50de0962cbdd68915146421`, 2753 payloads plus manifest.

First integration: [f4-dense-state-6ebe0f52c27e.tar.xz](raw/f4-dense-state-6ebe0f52c27e.tar.xz), SHA-256 `d16c332fc72857732e451ee80eaac7007d3eef139ade6c02b8c0167587dbd028`, 927 payloads plus manifest.

Second integration: [f4-dense-active-7af81facc404.tar.xz](raw/f4-dense-active-7af81facc404.tar.xz), SHA-256 `732eacb39cdf95188f458cfc8b76e4d0aae0fc3d933fb3f664215d7a7b6d4592`, 928 payloads plus manifest.

Second verification: [f4-dense-checks-20fb9d9dfc65.tar.xz](raw/f4-dense-checks-20fb9d9dfc65.tar.xz), SHA-256 `08fde2ae3af724a6e5726019245add3eab5230b2a131d51b9f9e0f2e249ea92d`, 337 payloads plus manifest.

Trie baseline: [f4-trie-format-20c0f7e7df0d.tar.xz](raw/f4-trie-format-20c0f7e7df0d.tar.xz), SHA-256 `8c32eeb18a5546dcceabe4f0c5e96ee041696f85c738663c3d1848fd669e05de`, 604 payloads plus manifest.

Earlier production baseline: [f4-sampling-a1eb7697c27d.tar.xz](raw/f4-sampling-a1eb7697c27d.tar.xz), SHA-256 `99a522cf1785f60cf2541b438c1d0f2758b8a70dab0b30de81163488236784b1`, 601 payloads plus manifest.

Current integration: [f4-dense-review-b672e7fcc65e.tar.xz](raw/f4-dense-review-b672e7fcc65e.tar.xz), SHA-256 `b8e4bfef30b89c09b214e77896829e5557144a24343e0389465e3859450940d8`, 1205 payloads plus manifest.

Current verification: [f4-dense-checks-467877f9757b.tar.xz](raw/f4-dense-checks-467877f9757b.tar.xz), SHA-256 `5448a2cc2366fb9c67dea21af6289cce246ae9b450b4dbed5ab72fcb26751bd2`, 527 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_dense_report.py --experiments reports/bench-results/raw/f4-dense-experiments-afec08f91ee7.tar.xz --first reports/bench-results/raw/f4-dense-state-6ebe0f52c27e.tar.xz --final reports/bench-results/raw/f4-dense-active-7af81facc404.tar.xz --baseline reports/bench-results/raw/f4-trie-format-20c0f7e7df0d.tar.xz --old-baseline reports/bench-results/raw/f4-sampling-a1eb7697c27d.tar.xz --guards reports/bench-results/raw/f4-dense-checks-20fb9d9dfc65.tar.xz --report reports/bench-results/hexgroebner-dense-pivots.md --reviewed reports/bench-results/raw/f4-dense-review-b672e7fcc65e.tar.xz --reviewed-guards reports/bench-results/raw/f4-dense-checks-467877f9757b.tar.xz --check`. Add `--current` to require the present runtime and verification sources. Collectors include host-specific commands and paths; adapt those locations when replaying on another host.
