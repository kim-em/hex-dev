# Restored matrix row-update experiments

Neither a sixteen-lane AVX-512 update nor forced geometry inlining establishes
an improvement on the matched medium development suite. Both variants are
restored; neither is part of the production row kernel. The canonical row
representation, bounded native calls, malformed-input checks and output
contracts remain unchanged.

The AVX-512 variant has source fingerprint `00dfa6f38a1c`. It uses sixteen
four-byte coefficients per vector, exact Montgomery/Mersenne products,
contiguous stores or scatter, runtime CPU/OS feature detection and the existing
eight-lane/scalar tails. All 8 source-identified Clang/GCC sanitizer
variants pass, including guarded buffers, malformed lanes, aliasing, resumed
prefixes and instrumented complete F4 calls on both vector layouts. The separate
one-line `always_inline` variant (`b1072a0a1dcb`) changes only geometry helper compilation;
its fresh CLI build and complete before/after output comparisons pass.

All campaigns compare against frozen source `8f56f7677ce6`, with adjacent
AB pairs followed by BA pairs, one automatically leased CPU and identical
resource/output contracts. The AVX-512 repeat is the one unchanged repeat after
an inconclusive first observation. The inlining source has one campaign.
Every completed sample is retained, with failures, RSS, variability, CPU and
host context. Sources are never pooled across campaigns.

| Variant/campaign | Process ratio new/baseline | Internal candidate ratio | Median process ratio | Process range | CPU | Peak RSS baseline/new KiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| AVX-512 first | 1.0079 | 1.0084 | 1.0072 | 0.8513–1.2809 | 77 | 96140/96376 |
| AVX-512 repeat | 1.0067 | 1.0048 | 1.0038 | 0.8597–1.2267 | 19 | 96140/96480 |
| Forced inline | 1.0017 | 1.0097 | 0.9967 | 0.8340–1.2351 | 80 | 96076/96424 |

Each campaign retains 56 processes and 28 complete-basis comparisons, all
successful with identical output/counter/scheduling fields except internal
candidate time. The process metric weights the seven development families
equally. Candidate production and process intervals are distinct; certificate
generation, independent native verification and kernel checking are excluded.
These inputs are not held out and cannot establish acceptance or leadership.

The diagnostic Eco11 M31 profiles report no lost samples. Their instruction
annotations place substantial samples near gather/scatter dependency boundaries.
This is cost attribution for one input, including startup/output, rather than
a causal proof of a memory bottleneck or a scientific timing comparison.
The observations justify retaining the existing production kernel while
pursuing less repeated algebraic work. They establish no language limitation.

The [report generator](../../scripts/bench/groebner_vector_report.py) reruns the
complete JSON comparisons and recomputes all displayed figures from raw sample
metadata. It verifies every payload digest and binds all unpacked analysis
inputs to the corresponding capsule members before consuming them. Fixed schedules and all completed observations remain available;
there is no retry-until-faster selection. Issue #10987 remains open.

[Raw restored-experiment capsule](raw/f4-rejected-vectors-00dfa6f38a1c.tar.gz): SHA-256
`393d3b8c2d50b5403807efe5fbe2cdc014c6d723b00ce152928df48e952490ee`, 1031 data payloads, each read back and digest
checked, plus the digest manifest. It contains source patches/manifests, compiler/build/native logs,
all three campaigns, independent analyses and raw profiles/annotations.
