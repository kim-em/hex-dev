# Sparse F₂ elimination: measured snapshot

This campaign compares frozen runtime `5fd07b982681` with `c4cb8197a53d`. Both produce unchecked complete monic reduced bases in ordinary polynomial rings; `x` and `x²` remain distinct over F₂. These observations do not establish the fastest-open-source milestone.

Requested binary-pivot frames use borrowed sparse pivots and a UInt64 parity accumulator beyond the packed dimension ceilings. A bounded header pass also chooses sparse elimination when the packed private payload cannot fit, or even maximal four-row table savings cannot meet its word-work cap. Every table consumes four dense known rows, so their count divided by four bounds the possible savings. Each call tries one backend; successful packed admissions are preserved.

Sparse limits are 2²⁰ columns and known reducers, 4096 targets, a 2³⁸ conservative shape bound and at most 2³⁴ charged work. Extra payload is `7*columns + 40*min(rows,columns)`, reserved in addition to the complete reference payload. Unsupported or exhausted native frames release private state and continue with exact reference rows, labels and counters. A discarded prefix is bounded per frame.

All 128 processes completed and all 64 adjacent pairs have identical complete outputs and all logical counters. The fixed selection contains the first primary size of each of ten families in all three fields, plus Eco-14 and Eco-15 over F₂. Runs use one automatically leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled. Adjacent arm order alternates AB/BA.

| First-size field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 | 1.0010 | 0.9738 | 0.8683–1.1550 | 34664/34740 |
| 32003 | 1.0042 | 0.9967 | 0.8967–1.2347 | 565848/565452 |
| 2147483647 | 1.0030 | 1.0091 | 0.9377–1.0797 | 620164/638448 |

The odd-prime arithmetic routes are unchanged controls. F₂ first-size cases include header-selection overhead. These are descriptive point estimates with every completed sample and outlier retained; no control-adjusted improvement is inferred. The selection does not replace the complete fixed balanced suite or held-out acceptance.

| In-sample F₂ case | Candidate B/A | Pair ratios |
|---|---:|---|
| eco14-2 | 0.7807 | 0.8054, 0.7567 |
| eco15-2 | 0.7671 | 0.7665, 0.7677 |

The host is AMD EPYC 9455. Native production code uses Clang 21.1.8 and Lean-generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3. Source blobs, complete outputs, build inputs, executable/compiler hashes, CPU assignment, host activity, all observations and failures are retained. Limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with the fixed corpus’s large explicit parent allowances. The data do not establish timing or admission under library default budgets.

Verification records all nine project gates and 36 strict Clang/GCC ASan/UBSan configurations: regular dispatch, forced sparse small/large frames and packed-only admission controls. Tests compare all rows, labels and eight counters, independent remainders, exact work/byte/input/output boundaries, malformed buffers, duplicate heads, shared inputs, near-UInt64 parity offsets and zero-accumulator reuse. Kernel replay and axiom audits remain separate from timed candidate production.

Certificate generation, independent native certification, kernel checking and full checked calls are excluded from these candidate timings. Finite-extension adapters, deterministic producer correctness/termination, full balanced and held-out comparator acceptance, equal-thread parallel comparisons and the overall-fastest gap remain open under issue #10987. Scientific claims use manual shared-host observations, never CI timings.

Raw capsule `f4-sparse-production-5fd07b982681.tar.xz` has SHA-256 `40fbf83897c6d2fb1472a7fe72f867ba937849cf9b7328cf5b0003b9a505d3b2`. Its per-payload hashes, exact runtime/check-source manifests, all 64 full-output comparisons and actual gate receipts are replayed by this generator. `--current` additionally requires the checkout’s runtime and verification sources to match the recorded snapshot. CI uses `--current-runtime` to bind runtime sources while replaying the recorded verification snapshot; updated gate receipts are assembled after those gates finish.
Seeded sparse frames exercise dozens of reducers and targets, reducer chains, reused target pivots and independent remainders. The committed profile generator records its source identity, probe compiler version, exact probe variant flags and hashes of generated drivers, probe source and Lake configuration.


| Private in-sample Eco-14 experiment | Candidate B/A | Process B/A | Pair ratios |
|---|---:|---:|---|
| continuation | 1.1089 | 1.1088 | 1.1177, 1.1002 |
| continuation-factor | 1.0853 | 1.0852 | 1.0573, 1.1140 |
| wide-sparse | 0.9212 | 0.9210 | 0.9092, 0.9334 |
| bit-accumulator | 1.0189 | 1.0188 | 1.0109, 1.0270 |
| retry | 0.7578 | 0.7583 | 0.8487, 0.6767 |
| selector | 0.8219 | 0.8245 | 0.8482, 0.7965 |
| constant-prime | 0.9982 | 0.9997 | 0.9375, 1.0627 |

These are seven distinct private executables and source snapshots, with 28 successful samples and 14 complete output/counter comparisons. The original four permission-denied launches are retained separately. The continuation, factor-only, bit-accumulator and constant-prime variants are unselected. The retry and upfront-selector experiments motivated the production change, but their source/executable identities differ from production. Ratios from different stages are not multiplied. All observations and rejected routes remain included.

The retry experiment’s discarded-work counter covers only its sparse retry. A separate production admission trace records 202062207 charged units discarded by the preceding packed attempts across 15 frames; the last of 16 packed refusals occurs before charged work. The upfront selector avoids those preceding attempts. The prototype counts do not substitute for current-production instrumentation.

Experimental capsule `f4-sparse-experiments-e36a6d3dba87.tar.xz` has SHA-256 `5f7a502708c2ef3e664df1c7de29ec8f4f604289484e14a1e31e6fd5b8643299`. Source blobs, all complete prototype outputs, input bindings, schedules, failed launches and admission accounting are independently replayed.

| Held-out family | Hex/msolve process ratio |
|---|---:|
| dense-quadratic | 1.0796 |
| sparse-structured | 1.5511 |
| positive-dimensional | 1.2008 |

The complete held-out sweep contains all 27 fixed inputs in three families across all three fields. All 108 processes succeeded, all 54 complete bases agree and there were no timeouts or missing observations. The equal-family process ratio is 1.2622× Hex/msolve; the implementation remains slower overall on this held-out suite. Peak RSS is 1347816/266068 KiB for Hex/msolve. These measurements do not establish a language/runtime limit.

The comparator is msolve commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with Clang 23.1.3, `-O3 -march=native`, full reduced output (`-g 2`), linear algebra mode 2 and one thread. Both arms use the same GNU time wrapper and adjacent AB/BA scheduling on one automatically leased CPU. Ratios include process startup, parsing and complete output; checking lies outside candidate timing. Field/order/output contracts, comparator engine hashes and recorded compile commands are retained.

Held-out archive stream SHA-256 is `bdd2789a17fdda7f84f0c780dc5c5b64bb820dcb40405d632264914d2abdf65b`. Parts index `f4-sparse-heldout-5fd07b982681.parts.json` has SHA-256 `f6f2d5f75268348c7e1bd395b60701af3f3aef839cb5ea96e0bc3126cd0cc0fd`. All complete bases, source/executable/compiler bindings, fixed inputs, samples, memory observations and family ratios are replayed independently. Full primary balanced acceptance and parallel comparisons remain outstanding.
