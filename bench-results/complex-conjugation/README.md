# Conjugation comparison

The tag implementation takes about 18 ns per call on the recorded host across
minimal-polynomial degrees 2, 3, 4 and 6. The former root-search algorithm takes
about 2 ms, 10 ms, 26 ms and 172 ms respectively. These are host-specific
observations, including loop and checksum overhead, not portable latency bounds.

| Degree | Tag median, ns/call | Search median, ms/call |
|---|---:|---:|
| 2 | 17.91 | 2.12 |
| 3 | 18.02 | 9.60 |
| 4 | 17.66 | 26.25 |
| 6 | 17.57 | 171.80 |

Run `lake build hexnumberfield_bench`, then
`.lake/build/bin/hexnumberfield_bench conjugation-compare` on an automatically
selected CPU (the recorded run used `scripts.bench.idle_core.pick`).
The command constructs each input once, records construction separately, checks
that the two algorithms agree, and runs eight adjacent AB/BA blocks. Search
uses two calls per block; tag conjugation uses 100000. Both arms alternate a
number and its conjugate and consume the output orientation in a checksum.
Alternating inputs adds one extra tag conjugation on half the iterations;
its overhead is visible in the tag timing and negligible beside the search.
The reported tag number therefore includes about 1.5 conjugations per iteration.
Every completed block is retained in `samples.jsonl`; metadata records CPU,
load, host, toolchain and base revision. No rerun or sample exclusion was used.

The search arm is the former algorithm run over the new representation, so this
compares the operation strategies rather than two complete historical builds.
The constructor observations describe the new representation only. The compiled
`AlgebraicNumber.conj` and `OrientedIsolation.conj` bodies only inspect/update
records and the side tag; they contain no calls to polynomial arithmetic,
root enumeration, ball refinement, or certificate constructors. This code
inspection is the evidence for constant work in polynomial degree; the timing
sample illustrates its practical effect and does not independently establish
an asymptotic law.
