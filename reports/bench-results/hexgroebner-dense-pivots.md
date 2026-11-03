# Checked dense pivots: kernels and complete F4 observations

Dense pivot buffers preserve their exact sparse sources through typed cache
provenance. Preparation reserves its work and packed payload against the parent
allowances. Dense updates preserve zero gaps, invalid-target prefixes, pending
cursors and trace events. The deterministic continuation and whole-eliminator
proofs include preparation charges. Final runtime `7af81facc404` and
verification sources `20fb9d9dfc65` pass eight Clang/GCC sanitizer variants
and nine project gates. Instrumented complete F4 exercises a native dense update
in every compiler variant. Kernel checking remains separate from native testing.

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
the dense dispatch. Its negative results are retained. The final integration
restricts dispatch as described above; its control uses the merged trie runtime.
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

All 336 complete-F4 processes / 168 matched pairs complete with equal bases. Shared-host variability is retained; these descriptive sweeps establish no overall speedup. The option remains disabled by default. The fastest-open-source milestone and remaining compiler/runtime investigation remain open under #10987.

| Final combined family | Process ratio |
| --- | ---: |
| cyclic | 1.0427 |
| kat | 1.0042 |
| eco | 0.9750 |
| noon | 0.9827 |
| reimer | 1.0188 |
| minrank | 0.9994 |
| dense-quadratic | 1.0024 |

An earlier unselected C-local row-shape cache retains 112 process samples / 56 matched deterministic and sampled comparisons in the experiment capsule. Its process ratios are 1.0035 (deterministic) and 0.9965 (sampled). Its complete outputs agree and it establishes no benefit; that cache is absent from the implementation. The diagnostic profiles and all native-check snapshots are retained with their exact source manifests.

Kernel and unselected experiments: [f4-dense-experiments-afec08f91ee7.tar.xz](raw/f4-dense-experiments-afec08f91ee7.tar.xz), SHA-256 `e03503434f4b649f176e36e5c9adc73d525d88d3c50de0962cbdd68915146421`, 2753 payloads plus manifest.

First integration: [f4-dense-state-6ebe0f52c27e.tar.xz](raw/f4-dense-state-6ebe0f52c27e.tar.xz), SHA-256 `d16c332fc72857732e451ee80eaac7007d3eef139ade6c02b8c0167587dbd028`, 927 payloads plus manifest.

Final integration: [f4-dense-active-7af81facc404.tar.xz](raw/f4-dense-active-7af81facc404.tar.xz), SHA-256 `732eacb39cdf95188f458cfc8b76e4d0aae0fc3d933fb3f664215d7a7b6d4592`, 928 payloads plus manifest.

Final verification: [f4-dense-checks-20fb9d9dfc65.tar.xz](raw/f4-dense-checks-20fb9d9dfc65.tar.xz), SHA-256 `08fde2ae3af724a6e5726019245add3eab5230b2a131d51b9f9e0f2e249ea92d`, 337 payloads plus manifest.

Trie baseline: [f4-trie-format-20c0f7e7df0d.tar.xz](raw/f4-trie-format-20c0f7e7df0d.tar.xz), SHA-256 `8c32eeb18a5546dcceabe4f0c5e96ee041696f85c738663c3d1848fd669e05de`, 604 payloads plus manifest.

Earlier production baseline: [f4-sampling-a1eb7697c27d.tar.xz](raw/f4-sampling-a1eb7697c27d.tar.xz), SHA-256 `99a522cf1785f60cf2541b438c1d0f2758b8a70dab0b30de81163488236784b1`, 601 payloads plus manifest.

Regenerate with `python3 scripts/bench/groebner_dense_report.py --experiments reports/bench-results/raw/f4-dense-experiments-afec08f91ee7.tar.xz --first reports/bench-results/raw/f4-dense-state-6ebe0f52c27e.tar.xz --final reports/bench-results/raw/f4-dense-active-7af81facc404.tar.xz --baseline reports/bench-results/raw/f4-trie-format-20c0f7e7df0d.tar.xz --old-baseline reports/bench-results/raw/f4-sampling-a1eb7697c27d.tar.xz --guards reports/bench-results/raw/f4-dense-checks-20fb9d9dfc65.tar.xz --report reports/bench-results/hexgroebner-dense-pivots.md --check`. Add `--current` to require the present runtime and verification sources. Collectors include host-specific commands and paths; adapt those locations when replaying on another host.
