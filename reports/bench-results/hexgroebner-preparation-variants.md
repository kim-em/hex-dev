# Packed monomial preparation and append variants

Three separate prototypes investigate allocation and metadata overhead in
monomial construction. None is selected. They use the default total-degree
scheduler from the scheduling implementation, retain its algebraic choices,
The CLI comparisons use frozen source `0cb80bf73a4a`, whose compute executable
is byte-identical to `6ede9cb261a4`. Fixed-benchmark metadata names baseline
`6ede9cb261a4`; compute identity does not imply benchmark-executable identity. Exact computational sources and both baseline/prototype
manifests are retained in each capsule.

`6b380360b565` appends a validated prepared monomial to owned exponent and
metadata arenas in one native operation. An explicit declined result returns
both original buffers, so portable fallback runs after the native frame and
does not retain an avoidable alias. The first capacity helper unnecessarily
doubled capacity when copying shared buffers even when capacity sufficed;
MonomialConformance caught an out-of-memory panic. The corrected helper
preserves sufficient capacity. Only the corrected source is timed. Failure
and correction logs are retained.

`6302d3c58d00` implements the same operation without the fixed 16-KiB temporary
packet. It retains the prepared buffer when that borrowed input aliases an
owned arena, validates coordinates before mutation and then writes directly.
The earlier source's disassembly shows unconditional stack probes; this is
motivation, not evidence of their isolated cost. Its disassembly is explicitly
identified as old source and is not attributed to the revised binary.

`325788939fd4` returns preparation bytes and degree, divisibility mask, hash
and largest exponent as one typed record. Monomial construction reads scalar
fields instead of repeatedly decoding them. The kernel theorem
`prepareInfo_data` proves that the portable data projection returns exactly
the prior prepared payload, with only `propext` and `Quot.sound` in its axiom
audit. That theorem does not justify the native provider; differential tests
check native bytes and every metadata field independently.

Each variant has a fresh detached 188-job driver freeze, one 64-process small
campaign, one 56-process medium campaign and one 120-point registered fixed
campaign. Each case runs adjacent AB then BA on one automatically leased CPU
of the shared EPYC 9455 host, with one algorithm thread. No unchanged repeat
is used. Every completed sample, outlier, failure and host context is retained.
The 16 small and 14 medium inputs span seven families and the explicit fields
32003 and 2147483647, with grevlex order. Full reduced bases agree in every
pair; all non-timing algorithm statistics are equal. Fixed complete structural
output hashes agree too. These are development suites, not held-out or SPEC
acceptance coverage.

Candidate time includes canonical packing, F4 and final interreduction.
Process time adds launch, initialization, parsing, full output and identical
GNU-time wrappers. Child peak RSS is measured after exec. Certificate generation,
independent final certification and kernel replay are excluded. Candidate and
process measurements remain distinct; no latency difference is assigned to a
particular runtime cause.

| Variant | Small candidate B/A | Small process, equal-family B/A | Medium candidate B/A | Medium process B/A |
| --- | ---: | ---: | ---: | ---: |
| append-packed | 0.8970 | 0.8990 | 1.0293 | 1.0404 |
| append-alias | 0.8644 | 1.2043 | 0.9988 | 0.9522 |
| prepared-info | 0.9684 | 1.0099 | 1.2883 | 0.9477 |

The small process column is family-balanced; the other columns use all-pair
geometric means (the medium corpus has equal family counts). Small all-pair
process ratios are 0.9265, 1.1946 and 1.0142 for append-packed, append-alias and
prepared-info, respectively.

The append-alias small candidate median is 1.0115, with ratios 0.0773–5.1263;
its medium candidate median is 1.0006, range 0.8202–1.2462. Thus the small
candidate mean is not a uniform gain. Its small process mean regresses and
its fixed Reimer case regresses substantially. The other variants also give
mixed or regressive observations, rather than an established improvement.

| Fixed case | Append packet | Append alias | Prepared metadata |
| --- | ---: | ---: | ---: |
| cyclic4 | 1.0100 | 0.9965 | 0.9836 |
| cyclic5 | 0.9846 | 1.0086 | 0.9922 |
| cyclic6 | 1.1800 | 0.8546 | 1.1079 |
| katsura3 | 1.0234 | 0.9831 | 1.0088 |
| reimer5 | 1.1793 | 1.6561 | 0.8907 |
| cyclic6Small | 1.0863 | 1.0467 | 1.1133 |

All three providers pass four Clang and four GCC ASan/UBSan variants, including
real F4 calls, exact portable equality, shared and aliased arrays, malformed
spans, coefficient/exponent widths, overflow, and work/byte boundaries. Append
variants execute 1162 calls, including 526 inside F4; typed preparation executes
9656 calls, including 4967 inside F4. The harness requires genuine accepted
native answers for valid inputs, so declining every operation does not pass.
No full independent oracle/conformance profile is claimed for these research
variants. The production implementation does not adopt them.

These results leave algorithm, representation, allocation and matrix work to
investigate. They establish no compiler/runtime impossibility and do not meet
the fastest-open-source milestone. The issue remains open.

- [prototype-append-packed-6b380360b565.tar.gz](raw/prototype-append-packed-6b380360b565.tar.gz): `f680b13b39b84f54d125517fe887527152b826a4c5264208b9b6c4435e79f9ec`.
- [prototype-prepared-info-325788939fd4.tar.gz](raw/prototype-prepared-info-325788939fd4.tar.gz): `2b62297d8efd0f20068a7345c2cba2bdde2e0e5c0addbbf0a16563da2fbe6af5`.
- [prototype-append-alias-6302d3c58d00.tar.gz](raw/prototype-append-alias-6302d3c58d00.tar.gz): `c7545687139332a2226950bf148ed4e436e5d9348610cb3baf4bc71d4dacb1b1`.

A separate target-sort-key variant, source `70d510e4fd93`, computes leading
column and support size once per row before sorting. It retains stable ties,
traced root associations and positional independent remainders, charging the
extra linear pass. A fresh 188-job driver build and one 64-process small and
56-process medium observation give candidate ratios 0.9970/1.0018 and
process family ratios 0.9802/0.9889. Every complete basis agrees. Candidate summaries for append-alias, prepared-info and target-keys are
recomputed from retained raw nanosecond timings; standalone candidate-analysis
outputs are absent from those capsules. No unchanged
repeat, fixed sweep, full oracle profile or new native validation is claimed.
The baseline is target-column source `b9c671b4f9af`; these observations are
separate from compact indexing. The variant is not selected because it shows
no established candidate gain.

- [prototype-target-keys-70d510e4fd93.tar.gz](raw/prototype-target-keys-70d510e4fd93.tar.gz): `b3ba7ebface08bc05f7c266fa1c0511fe90941d20ed1aafa576caae7f3d9db76`.
