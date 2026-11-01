# Total-degree critical-pair scheduling experiment

This research prototype uses actual LCM degree to select pairs, while retaining
separate propagated sugar labels for symbolic and matrix work. Its source family
is `0fdb6c42a1c6`, commit `1f2c363f06c94f26e08b3cb529f5ff3707a7209e`.
The baseline is the dedicated Mersenne dispatch family `b1e96ea920dd`.
Field arithmetic, matrix kernels, pair criteria and benchmark sources agree.
Algorithm counters may differ: this experiment changes the algebraic work.

This is not a production selection. The governing SPEC requires sugar-degree
scheduling or verified homogenization for inhomogeneous systems. Allowing the
experimental policy for those systems requires resolving that restriction.
Complete-output comparisons below are evidence, not a producer correctness or
termination proof. The prototype also changes the critical-pair constructor;
existing conformance clients need updating, and the previous large-batch
performance assertion does not hold for the changed scheduling.

The fixed development suite has 16 inputs in seven families, at primes 32003
and 2147483647. Each input runs adjacent AB then BA, on automatically leased
CPU52, one thread. All 64 processes succeed, and every one of the 32 complete
reduced-basis comparisons agrees. Every completed sample is retained. No
unchanged repeat is used. Internal candidate time includes canonicalization,
F4 and final interreduction; process time adds startup, parsing and output.
Certificate generation, independent certification and kernel replay are excluded.

The all-pair candidate geometric mean B/A is 0.8141, median 0.9949 and range
0.2618–1.0896. The process ratio is 0.8757, median 0.9793 and range
0.4550–1.2317. Equal weighting of the seven family candidate geometric means
gives 0.7958; cyclic5 and cyclic6 share one family. This is development evidence,
with no held-out or fastest-open-source claim.

| Family | Candidate geometric mean B/A |
| --- | ---: |
| cyclic | 0.9544 |
| Katsura | 0.9983 |
| Eco | 0.7898 |
| Noon | 0.9991 |
| Reimer | 0.2630 |
| MinRank | 1.0239 |
| dense quadratic | 0.9986 |

At prime 2147483647, the changed work is substantial for two families. These
are cumulative validated matrix input-plus-output entries, not arithmetic
operation counts or msolve's differently scoped matrix statistics.

| Input | Baseline rounds | Degree rounds | Baseline matrix entries | Degree matrix entries | Baseline work | Degree work |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Cyclic5 | 13 | 14 | 8945 | 9201 | 230242 | 250030 |
| Cyclic6 | 22 | 18 | 97786 | 70172 | 2559099 | 2074167 |
| Eco10 | 15 | 20 | 3268590 | 2689194 | 172847811 | 127841538 |
| Reimer5 | 26 | 18 | 960252 | 192346 | 15341887 | 3210321 |

The separate registered fixed benchmark sweep retains all 120 points, using
CPU53 and five declared repetitions per case in adjacent AB/BA order. The
ratios normalize by actual inner repeats; full structural basis hashes agree.

| Fixed case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0531 | 1.0087 | 0.9543–1.5913 |
| cyclic5 | 1.1017 | 1.0958 | 1.0812–1.1339 |
| cyclic6 | 0.8458 | 0.8474 | 0.8254–0.8588 |
| katsura3 | 1.0037 | 1.0010 | 0.9815–1.0460 |
| reimer5 | 0.2687 | 0.2687 | 0.2639–0.2713 |
| cyclic6Small | 0.8437 | 0.8426 | 0.8301–0.8569 |

Each archive preserves both source manifests and their Git blobs, frozen
executable hashes, build configuration, complete outputs and analyses. The
runner inherited an incorrect `protocol.B` description of zero scans; separate
protocol corrections identify the actual degree experiment, without rewriting
raw metadata. No zero-scan optimization is present in either arm.

- [degree-production-bench-0fdb6c42a1c6.tar.gz](raw/degree-production-bench-0fdb6c42a1c6.tar.gz): `331c4e4d807d0e9ee50450275d88d52ad6135e5307069712c36b9dc250f5aa60`
- [degree-production-records-0fdb6c42a1c6.tar.gz](raw/degree-production-records-0fdb6c42a1c6.tar.gz): `dc28ec42dfe54cb36aa635333f22a57043749f2813f6883bcef7002d52277238`
