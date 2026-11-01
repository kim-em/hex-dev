# Total-degree and sugar-degree F4 scheduling

`Limits.scheduling` selects fair total-degree (`.degree`, default) or sugar-degree
(`.sugar`) critical-pair batches. Total degree is the actual pair LCM degree;
propagated sugar remains separate. Both heaps break ties by stable basis indices.
The original choice is sealed through candidate, traced, checked-preparation
and candidate-validation continuations. A different resume allowance cannot
change it. CLI output and checked history retain the selected strategy.

Pair coverage, reduced output, complete certificates, deterministic producer
correctness and termination remain obligations under either strategy. New
inhomogeneous pairs can have lower degree than earlier batches. This scheduling
choice supplies no substitute for those obligations.

Measured source family `bf00a2b578a8`, retained by implementation commit
`8f1485df5f`, is frozen by a fresh 188-job build. Its default executable SHA256 is
`2ece3bf2646f90393331ce349043b8a19adb02d236ee1bf300337ceaf9e9bd67`.
The subsequent independent-oracle corpus guard changes only
`scripts/oracle/groebner_singular.py` within that source family. A second fresh
188-job build of `6ede9cb261a4` produces byte-identical default and full-init
executables; exact source comparisons and both manifests are retained.

The same-binary experiment compares explicit sugar (A) with explicit degree
(B). The before/after experiment compares the previous sugar implementation
`a5989cb5e42e` (A) with the new default (B), including its cached priority field.
Each uses 16 development inputs in seven families, primes 32003/2147483647,
one algorithm thread and automatically leased CPUs on the shared AMD EPYC 9455
host. Each comparison has first and exactly one unchanged repeat: same-binary
CPU60/70, before/after CPU34/71, exact msolve CPU2/69, probabilistic msolve
CPU15/72. Different campaign types run concurrently on distinct leased CPUs;
host load is recorded without rejecting samples. Arms are adjacent AB then BA.
Repeats use the unchanged measured checkout. All 512 processes complete, with
256 agreeing full reduced-basis pairs and zero failures/timeouts. All samples
and outliers remain; no further unchanged repeat is used.

Candidate time includes canonicalization, F4 and final interreduction. Process
results add initialization, input/output and identical GNU-time wrappers, whose
child RSS is retained. Certificate generation, independent certification and
kernel checking are excluded. This is a development corpus; the SPEC balanced
and held-out suite, wider fields, extensions, parallel scaling, remaining
comparators and complete producer proofs remain required. No performance
leadership or compiler-change impossibility claim follows.

| Pooled comparison, 64 pairs each | Candidate B/A | Median | Range | Process B/A | Equal-family process |
| --- | ---: | ---: | --- | ---: | ---: |
| Degree/sugar, same binary | 0.8909 | 0.9056 | 0.0175–8.8814 | 0.9483 | 0.9345 |
| New default/previous implementation | 0.8549 | 0.9504 | 0.0091–7.0540 | 0.8880 | 0.8665 |

Process medians/ranges are 0.9256 / 0.3088–4.3296 (same binary) and
0.9162 / 0.2497–2.8274 (before/after). Mixed cases and substantial variability
preclude a uniform speedup claim. Same-binary family means and exact work
changes are reported together below.

| Family | Candidate degree/sugar | Process degree/sugar | Hex/msolve exact | Hex/msolve probabilistic |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 1.0808 | 1.0510 | 3.0552 | 2.8253 |
| dense-quadratic | 1.9015 | 1.3456 | 1.7349 | 1.7214 |
| eco | 0.8022 | 0.8699 | 4.5390 | 5.5131 |
| kat | 0.8909 | 1.0048 | 2.3510 | 2.4594 |
| minrank | 0.7455 | 0.9260 | 1.7075 | 1.4346 |
| noon | 0.5786 | 0.8694 | 1.6405 | 1.5519 |
| reimer | 0.5797 | 0.6254 | 3.2250 | 3.3308 |

The next table uses the same-binary experiment. Every repeated instance of
each input/strategy has identical non-timing counters. Full work/allocation
counts remain in `counter-analysis.json` and `pooled-analysis.json` in each
capsule; names identify the exact archived input.

| Input | Matrix entries sugar→degree | Rounds sugar→degree | Candidate ratio | Process ratio |
| --- | ---: | ---: | ---: | ---: |
| `cyclic5-15` | 8757→9067 | 13→14 | 1.5602 | 1.7474 |
| `cyclic5-31` | 8757→9067 | 13→14 | 1.1148 | 0.8955 |
| `cyclic6-15` | 93597→69316 | 21→18 | 1.1126 | 1.1504 |
| `cyclic6-31` | 93597→69325 | 21→18 | 0.7052 | 0.6779 |
| `eco10-15` | 2939286→2326011 | 16→20 | 0.8324 | 0.9063 |
| `eco10-31` | 2939286→2326029 | 16→20 | 0.7731 | 0.8350 |
| `kat6-15` | 16569→16569 | 6→6 | 0.9268 | 0.8328 |
| `kat6-31` | 16569→16569 | 6→6 | 0.8564 | 1.2124 |
| `minrank_d_2_p_2_q_3_r_2-15` | 807→807 | 2→2 | 1.4242 | 1.0458 |
| `minrank_d_2_p_2_q_3_r_2-31` | 807→807 | 2→2 | 0.3902 | 0.8199 |
| `noon4-15` | 8780→8780 | 7→7 | 0.5271 | 1.0226 |
| `noon4-31` | 8780→8780 | 7→7 | 0.6351 | 0.7391 |
| `quadratic5-2147483647` | 18711→18711 | 5→5 | 2.2684 | 1.2531 |
| `quadratic5-32003` | 18711→18711 | 5→5 | 1.5939 | 1.4448 |
| `reimer5-15` | 435489→176082 | 19→18 | 0.6368 | 0.6622 |
| `reimer5-31` | 435489→176082 | 19→18 | 0.5277 | 0.5907 |

At the large prime, Reimer rows fall 4261→2027 and work 7406968→3052094.
Eco rows fall 32987→26541 and work 129768131→103428231, while rounds rise
16→20. Fewer rounds alone therefore do not explain the work reductions.

Extreme candidate observations remain explicitly included:

- Same binary, `minrank_d_2_p_2_q_3_r_2-31`, degree-vs-sugar-repeat-bf00a2b578a8, block 1: 37.501451→0.656343 ms, ratio 0.017502.
- Same binary, `quadratic5-2147483647`, degree-vs-sugar-bf00a2b578a8, block 0: 3.079387→27.349376 ms, ratio 8.881435.
- Before/after, `minrank_d_2_p_2_q_3_r_2-15`, before-after-repeat-bf00a2b578a8, block 1: 41.761576→0.379402 ms, ratio 0.009085.
- Before/after, `minrank_d_2_p_2_q_3_r_2-31`, before-after-repeat-bf00a2b578a8, block 0: 1.315090→9.276664 ms, ratio 7.054015.

Their algorithm counters agree with other executions of the same input and
strategy. The counters do not attribute those isolated duration differences to
scheduling delays, runtime behavior or other host effects.

The registered fixed sweeps on CPUs 60/45 retain all 240 points, five declared
repetitions per case, matched complete structural hashes and actual inner-repeat
normalization. The second is the single unchanged repeat after the first mixed
observation. The baseline is the previous implementation `a5989cb5e42e`;
its source blobs and prior benchmark hash/build metadata are retained.

| Fixed case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9813 | 0.9913 | 0.8615–1.0570 |
| cyclic5 | 1.0708 | 1.0857 | 0.8915–1.4917 |
| cyclic6 | 0.8283 | 0.8506 | 0.4509–1.4444 |
| katsura3 | 0.9875 | 0.9911 | 0.8035–1.1618 |
| reimer5 | 0.4458 | 0.4549 | 0.2860–1.0914 |
| cyclic6Small | 0.8705 | 0.8509 | 0.5006–2.5690 |

Cyclic5 regresses, while Reimer and cyclic6 favor the new default. Every
completed fixed point, including the large cyclic6Small outlier, remains.

msolve source `3672113ee2c696a2ac9c637636e0f7214f500ba1` uses Clang23.1.3,
effective `-O3 -march=native` recorded in its engine ELF, and GMP/MPFR/FLINT
6.3.0/4.2.2/3.6.0. Configure cannot find `omp.h`; one algorithm thread is
explicitly requested. The direct `.libs/msolve` ELF receives its recorded
neogb library path. Modes2/42 request complete reduced grevlex output. Verbosity2
diagnostics and uncontrolled probabilistic seeds remain in stderr/process time.
Build inputs, binary hashes and complete input/output comparisons are retained.

| Pooled comparator observation | Hex/msolve exact | Hex/msolve probabilistic |
| --- | ---: | ---: |
| Equal-family mean | 2.4373 | 2.4221 |
| All-pair mean | 2.5071 | 2.4691 |
| Median | 2.6720 | 2.4087 |
| Range | 0.8182–8.7343 | 0.7615–8.3039 |

Matched before/after observations estimate default-change effects; shifts
between independent comparator campaigns also include host variation.

Validation passes 1957 conformance/theory targets, both 1134-profile CLI
corpora, 175 matrix cases, 1134 independent SymPy/Singular basis cases and
1288 division cases. All 567 sugar profiles preserve every previous field and
counter; degree changes no reduced basis. New negative oracle tests reject
missing/duplicate strategy cases, incompatible polynomial problems and false
strategy metadata. Both strategies exercise traced derivations, independent
complete certificate replay and all tested native/portable paths. Four Clang
and four GCC ASan/UBSan variants, 32 benchmark checks, nine build/freeze tests
and dependency/phase/release/header/size audits pass. Native counts include
2668 trie calls, two intentional declines, 510 F4 calls without decline, and
4089 accepted F4 monomial comparisons without decline. Original constructor
and corpus-size integration failures are retained with their corrections.

Capsules retain source blobs, frozen executable hashes, schedules, raw samples,
full outputs, failures and analysis scripts. SHA256:

- [scheduling-before-after-bf00a2b578a8.tar.gz](raw/scheduling-before-after-bf00a2b578a8.tar.gz): `fff7904dabc15b1a327f771e2262ee314f681e7a9623dc9afa3bc303f8b23398`.
- [scheduling-before-after-repeat-bf00a2b578a8.tar.gz](raw/scheduling-before-after-repeat-bf00a2b578a8.tar.gz): `4a42a82be5d7c0a3bf80d82d62d928836ef69eb100ed4a4eeed75d68640a69dc`.
- [scheduling-degree-vs-sugar-bf00a2b578a8.tar.gz](raw/scheduling-degree-vs-sugar-bf00a2b578a8.tar.gz): `3137dee27b738ac8008187ba34e66845a0395e1411304f81d691b8275cbef5df`.
- [scheduling-degree-vs-sugar-repeat-bf00a2b578a8.tar.gz](raw/scheduling-degree-vs-sugar-repeat-bf00a2b578a8.tar.gz): `3b482d41542a16a410a08846553c154ab8d617a132adc9f9d6490edb43e96504`.
- [scheduling-msolve-l2-bf00a2b578a8.tar.gz](raw/scheduling-msolve-l2-bf00a2b578a8.tar.gz): `48fdd0cf7b6d536b863ccf988327a821404ae70d85c2780081098d99a1403f67`.
- [scheduling-msolve-l2-repeat-bf00a2b578a8.tar.gz](raw/scheduling-msolve-l2-repeat-bf00a2b578a8.tar.gz): `2b5ed8788efd05755d75268e1a7a30860f767e25c658881e78bdb6a7531b116e`.
- [scheduling-msolve-l42-bf00a2b578a8.tar.gz](raw/scheduling-msolve-l42-bf00a2b578a8.tar.gz): `09ae217499d3689bf9c67e4041af83d1339d2348f6e2c59056591764fe1993df`.
- [scheduling-msolve-l42-repeat-bf00a2b578a8.tar.gz](raw/scheduling-msolve-l42-repeat-bf00a2b578a8.tar.gz): `a1189b0e401767c218cb3283056f9f74872f971d1a580b808ab2a451074bf746`.
- [scheduling-scheduling-production-bench-6ede9cb261a4.tar.gz](raw/scheduling-scheduling-production-bench-6ede9cb261a4.tar.gz): `73ee30609a2fc75b705cb23bbd38d6561336c9349e49017475acae8b923a6807`.
- [scheduling-scheduling-production-bench-repeat-6ede9cb261a4.tar.gz](raw/scheduling-scheduling-production-bench-repeat-6ede9cb261a4.tar.gz): `5b0709d11d545b2d10089476637401eba791da23793596946baa1aefbf8794eb`.
- [scheduling-validation-6ede9cb261a4.tar.gz](raw/scheduling-validation-6ede9cb261a4.tar.gz): `1e4f632a10a7024c90aae412e4fc812f758e6bdf661536975602d0be7f5361de`.
