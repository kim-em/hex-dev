# Transparent huge pages in the F4 drivers

The standalone F4 drivers call `prctl(PR_SET_THP_DISABLE)` from a constructor that runs before Lean module initialization. The Lean runtime's allocator otherwise reserves its arena with `MADV_HUGEPAGE`; under the host's `transparent_hugepage/defrag=madvise` policy a first touch may compact memory synchronously and zero a whole 2 MiB page. Comparators using glibc `malloc` never request huge pages under that policy. Outputs and logical counters are unchanged.

A is the frozen main build and B the frozen candidate `64eddfd8f204`; both arms run the identical CLI options on one leased CPU with adjacent AB/BA pairs. The selection is the first primary size of all ten families in all three fields plus Eco-14/Eco-15 over F₂, as in the preceding delayed-update campaigns.

| Field | Pairs | Candidate B/A | Process B/A | Process pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|---:|
| 2 | 24 | 0.5377 | 0.6817 | 0.2211–1.5706 | 843072/842800 |
| 32003 | 20 | 0.6547 | 0.6778 | 0.2673–1.0505 | 508572/508840 |
| 2147483647 | 20 | 0.6098 | 0.6312 | 0.1209–1.2368 | 582504/584152 |
| all | 64 | 0.5947 | 0.6643 | 0.1209–1.5706 | |

All 64 completed pairs have identical complete outputs and logical counters.

## msolve, held-out corpus

108 retained processes (completed); 54 jointly solved adjacent pairs, all with equal complete reduced bases. The equal-family Hex/msolve process ratio is **1.0837** (median pair 1.0023, range 0.7402–2.7897). Peak RSS Hex/msolve is 1392300/266040 KiB.

| Family | Jointly solved pairs | Hex solved | msolve solved | Hex/msolve process |
|---|---:|---:|---:|---:|
| dense-quadratic | 18 | 18/18 | 18/18 | 1.4235 |
| positive-dimensional | 18 | 18/18 | 18/18 | 0.9450 |
| sparse-structured | 18 | 18/18 | 18/18 | 0.9461 |

No input solved by msolve went unsolved by Hex within the same limits.

The comparator is msolve `3672113ee2c696a2ac9c637636e0f7214f500ba1` (full reduced output, `-g 2 -t 1 -l 2`). Process time includes startup, parsing and complete output. Candidate production excludes certificate generation, independent certification and kernel checking. These are observations on the shared AMD EPYC 9455 host; all completed samples are retained and no control-adjusted improvement is claimed. The fastest-open-source milestone remains open under issue #10987.
