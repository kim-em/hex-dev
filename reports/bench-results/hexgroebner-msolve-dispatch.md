# F4 comparison with msolve after dedicated Mersenne dispatch

The frozen Hex engine uses source family `b1e96ea920dd`, commit `d031fbf200`,
with executables byte-identical to measured `d1278bde9bd5`. Source manifests,
source blobs, binary hashes and the equivalence check are retained. The msolve
source is captured commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`. Its source tree is clean. Both the CLI and libneogb configure with
Clang 23.1.3, `-O3 -march=native`; GMP 6.3.0, MPFR 4.2.2 and FLINT 3.6.0 are
identified in the captured linkage. The reused script's GCC compiler label is
stale. Separate protocol corrections retain the configure settings, both
Makefile compiler lines and the actual libneogb SHA-256. GNU runtime/startup
objects explain the executable's GCC comment. Raw metadata is unchanged.

This historical comparison is superseded for comparator ranking by the
[effective-native medium comparison](hexgroebner-medium.md). Its retained
command invokes `/tmp/hex-groebner-msolve/msolve`, the top-level path, rather
than explicitly selecting `.libs/msolve`. The capsule records configured
flags, but does not establish their effective ISA or a direct-ELF timing
boundary. The known Nix flag-stripping and libtool-wrapper failure modes
therefore remain unresolved here; these ratios are not used as tuned-msolve
performance evidence. Raw results and the logical-stage profile remain useful
historical observations, with these limitations.

The fixed development suite has 16 inputs: two fields, 32003 and 2147483647,
across cyclic5/cyclic6, Katsura6, Eco10, Noon4, Reimer5, MinRank and dense
quadratic systems. This is development evidence, not a held-out or leadership
suite. Both systems compute full reduced grevlex bases with one thread and the
same resource limits. Each input runs adjacent AB then BA on one automatically
leased CPU. No completed sample is discarded and no unchanged repeat is used.

Whole-process time includes startup, parsing and full output consistently.
Hex's internal candidate time is retained separately and is not compared with
msolve process time. Certificate generation, independent final certification
and kernel checking are excluded. msolve `-l 2` uses exact sparse elimination;
`-l 42` uses probabilistic sparse/dense elimination. Both remain distinct from
completed checked Hex results. The probabilistic seed is recorded in each
msolve stderr log. All 64 processes succeed per mode; all 32 complete bases
match per mode, using canonical polynomial parsing and coefficient reduction.

The primary ratio first averages paired Hex/msolve process ratios geometrically
within each family, then averages the seven family values geometrically with
equal family weights. Cyclic5 and cyclic6 share one family.

| msolve mode | CPU | Family-balanced ratio | All-pair ratio | Median | Range | Peak Hex KiB | Peak msolve KiB |
| --- | ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 2 | 60 | 2.6697 | 2.6094 | 2.1179 | 1.0963–6.4328 | 94072 | 19396 |
| 42 | 95 | 2.8101 | 2.7448 | 2.1421 | 1.6479–8.9845 | 93504 | 19380 |

| Family | Exact mode 2 | Probabilistic mode 42 |
| --- | ---: | ---: |
| cyclic | 2.2242 | 2.3281 |
| kat | 1.9624 | 2.0060 |
| eco | 5.5184 | 6.8623 |
| noon | 1.9552 | 2.0014 |
| reimer | 5.8940 | 5.9406 |
| minrank | 1.7637 | 1.8427 |
| dense-quadratic | 1.9743 | 1.9708 |

Every jointly solved input is slower in these process observations. The
fastest-open-source milestone is not met, and a wider-prime/extension-field,
held-out and parallel comparison corpus remains required. These observations
do not establish a language limitation. They are not pooled with earlier
compiled Hex variants or with the other msolve elimination guarantee.

Eco10 at p31 illustrates an important remaining gap: Hex records 17 matrix
calls, 15 rounds, 3268590 validated input-plus-output matrix entries and a peak
4179 rows. msolve reports 19 F4 rounds, 1663 selected pairs, a largest F4 matrix
3620 by 3590 and a final reduction matrix 213 by 469. The counters have different
definitions and are not interchangeable. Raw per-round logs support further
work attribution; the aggregate timings do not identify a compiler cause.

A separate explanatory driver calls `F4.step` at the same source snapshot.
It records logical stage counters, with no timing claim; decoding is outside
its charged work. Complete bases match the retained comparison outputs for
all three traced inputs. These counters indicate that final interreduction
alone accounts for only about 2% of Eco10's pre-decode work; they do not measure
the wall-clock share of that phase.

| Input | Matrix rows, cumulative | Matrix entries, cumulative | Final reduction rows | Final reduction work | Total work before decode |
| --- | ---: | ---: | ---: | ---: | ---: |
| Eco10, p=32003 | 31112 | 3268590 | 1110 | 3305104 | 170755591 |
| Eco10, p=2147483647 | 31112 | 3268590 | 1110 | 3361220 | 172497901 |
| Cyclic6, p=2147483647 | 1870 | 97786 | 83 | 122411 | 2551154 |

Archives include all raw outputs, samples, failures, memory, source manifests,
Hex source blobs, msolve source, configure/engine identity, full-output
comparisons, analysis and measurement scripts. SHA-256:

- [msolve-l2-records-b1e96ea920dd.tar.gz](raw/msolve-l2-records-b1e96ea920dd.tar.gz): `c56c77b80fe48e48cce2c9e1f838c2a721a6eaddba8fa9c225a062b765c26b6d`
- [msolve-l42-records-b1e96ea920dd.tar.gz](raw/msolve-l42-records-b1e96ea920dd.tar.gz): `ecc4d5f30bc28d3bc47d4701f2ed0be31c7874985b16c2a2016a2d8b470b6980`

- [msolve-dispatch-engine-provenance.tar.gz](raw/msolve-dispatch-engine-provenance.tar.gz): `96ef12e37d4fa7766a6784d608406efcc95c2cc3bd5c3156f65ab7854426e3cd`

- [dispatch-round-trace-b1e96ea920dd.tar.gz](raw/dispatch-round-trace-b1e96ea920dd.tar.gz): `997df98f12d51f4d8f0dfd5cde9d9a45b2446d25c3bcd205ba72426925d554f1`
