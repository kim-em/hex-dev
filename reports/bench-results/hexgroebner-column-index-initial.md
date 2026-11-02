# Packed column lookup: initial measured variant

These observations bind initial source `9449e25be93d`. The subsequent
[charged-comparison revision](hexgroebner-column-index.md) has separate sources,
measurements and validation; no timing observations are pooled between them.

Symbolic row construction uses compact u32 column positions. Dense monomial-ID prefixes use direct positions plus one; sparse u32 IDs use eight-byte open-addressed buckets with full key comparisons. Zero values mark empty slots. Hash collisions never establish equality. Geometry alone selects the route. A chain beyond 64 probes retains the charged attempt and builds the ordinary hash map; non-u32 IDs or unsupported addressability also retain that route.

Both candidate production and certificate generation use this representation. Bounded native calls translate up to 4,096 IDs, reserve output once, write little-endian u32 values and commit the logical size only on success. They preserve borrowed/output aliases and marked-linear ownership. The scalar Lean model has identical successful output and failure behavior. Bounded zero initialization visits at most 4,096 bytes per call.

Packed initialization, insertion probes and payload are charged before work. Row construction reserves the largest successful probe count per entry, at most 64. These conservative charges and cumulative packed payload can exhaust earlier than the old unit-cost hash route. Increasing a limit cannot change the selected layout. No partial matrix is returned as a successful computation.

Measured source `9449e25be93d` has compute SHA256 `5ae4c7005f44ca0f85e1a8ba65cbe141414588a3e156e3c275af01601058580a` and reference-driver SHA256 `18b4838a4e76503d5f2f28220f1d3cf393258263ca15d7be7a874c8f733b07b7`. Baseline `e878b78cf727` has `fb6a033166de667e753df9ba554203503bb7bb9e89ad893f351f18f064eb2a1d`. Validation source `88c20c2efbd1` adds documentation and erased/test changes; benchmark source `8267339d38e6` also registers the two kernels. Both compute binaries remain byte-identical to the measured drivers.

Integrated source `1efac70aad44` is built on merged main; both compute hashes
remain identical. Fixed F4 observations retain their original measured benchmark
identities; the new linear-kernel binary is a separate benchmark build.

Both arms have fresh detached driver and benchmark builds, sharing only pinned dependency packages. The local SDK linker wrapper references an obsolete Nix script; the archived relocatable compiler helper restores bundled flags and invokes SDK Clang/LLD 23.1.0. Native FFI uses Clang 23.1.3. These observations apply to this build arrangement, with no pooling across source or toolchain variants.

Manual shared-host runs use EPYC 9455, one requested algorithm thread, an automatically leased CPU and adjacent AB/BA per input. All completed samples, failures, outliers, host activity observations and child RSS remain. The first campaign and sole unchanged repeat are retained for small, medium and fixed observations. No further unchanged repeat is used.

The small suite has 16 inputs and the medium 14, seven families at primes 32003 and 2147483647, grevlex, with complete monic reduced bases. They are development inputs, not held-out SPEC acceptance. Candidate time includes packing, F4 and final interreduction; process time also includes initialization, parsing, full output and identical GNU-time wrappers. Certificate generation, independent certification and kernel replay are excluded.

| Suite | Campaign | CPU | Candidate B/A | Process B/A |
| --- | --- | ---: | ---: | ---: |
| small | first | 22 | 1.1227 | 1.0989 |
| small | repeat | 64 | 1.4084 | 1.2992 |
| medium | first | 53 | 0.9288 | 0.9606 |
| medium | repeat | 64 | 0.8879 | 0.8228 |

| Suite | Complete pairs | Candidate B/A | Candidate median | Process B/A | Equal-family process |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 64 | 1.2575 | 0.9934 | 1.1949 | 1.1975 |
| medium | 56 | 0.9081 | 0.9361 | 0.8890 | 0.8890 |

The process-ratio shifts are not attributed to this representation change.
All 240 CLI processes succeed and all 120 complete basis pairs agree, with zero measured failures or timeouts. Work and packed-allocation counters differ by representation and are retained per process; other algorithm metadata agrees. Small-suite aggregate regressions remain material evidence, despite its near-one candidate median. No uniform speedup is established.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 1.1800 | 1.1769 | 0.9240 | 0.9045 |
| dense-quadratic | 1.2266 | 1.5413 | 0.9237 | 0.7322 |
| eco | 0.9662 | 0.9696 | 0.9260 | 0.9320 |
| kat | 0.8576 | 0.8271 | 1.1966 | 1.0494 |
| minrank | 3.4195 | 1.4438 | 0.6393 | 0.7441 |
| noon | 1.3802 | 1.5066 | 0.9727 | 1.0716 |
| reimer | 0.9361 | 1.1156 | 0.8659 | 0.8499 |

Small candidate ratios span 0.0553–96.7849; process ratios span 0.1850–9.8500. Maximum child RSS is 56888/56732 KiB for baseline/new. Logical packed-byte limits do not bound allocator capacity or process RSS.

Medium candidate ratios span 0.0226–7.1603; process ratios span 0.1062–2.4041. Maximum child RSS is 98388/100956 KiB for baseline/new. Logical packed-byte limits do not bound allocator capacity or process RSS.

The small MinRank family mean is driven largely by two extreme M31 pairs.
Its M31 case has retained candidate ratios near 96 in one pair of each campaign. An explanatory profile runs a fresh adjacent AB/BA on a leased CPU and records user cycles, instructions, task-clock, context switches, full output and CPU/wall/RSS. It does not reproduce the anomaly: the final four candidate times are 0.30–0.36 ms and whole-process user-cycle counts are 16.61–17.96 million. This does not establish the cause of the earlier wall-time spikes. Two preceding baseline-only profile processes completed before a reporting-key error; both are retained with the corrected four-process profile. No profiled duration is pooled with timing estimates or used to replace a sample.

| Fixed campaign | CPU | Case | B/A geomean | Per-call median | Range |
| --- | ---: | --- | ---: | ---: | --- |
| first | 22 | cyclic4 | 0.9940 | 0.9948 | 0.9622–1.0112 |
| first | 22 | cyclic5 | 0.9954 | 0.9940 | 0.9559–1.0449 |
| first | 22 | cyclic6 | 0.9986 | 1.0017 | 0.9787–1.0148 |
| first | 22 | katsura3 | 0.9836 | 0.9828 | 0.9693–0.9961 |
| first | 22 | reimer5 | 0.9418 | 0.9430 | 0.9249–0.9620 |
| first | 22 | cyclic6Small | 0.9784 | 0.9806 | 0.9559–0.9953 |
| repeat | 79 | cyclic4 | 1.0036 | 1.0020 | 0.9746–1.0550 |
| repeat | 79 | cyclic5 | 1.0029 | 1.0057 | 0.9635–1.0343 |
| repeat | 79 | cyclic6 | 0.9730 | 0.9738 | 0.9614–0.9859 |
| repeat | 79 | katsura3 | 0.9902 | 0.9865 | 0.9807–1.0044 |
| repeat | 79 | reimer5 | 0.9188 | 0.9217 | 0.8874–0.9341 |
| repeat | 79 | cyclic6Small | 0.9750 | 0.9757 | 0.9679–0.9810 |

All 240 fixed points succeed with equal complete structural output hashes. Reimer5 improves in both campaigns; Cyclic4 and Cyclic5 remain near parity. This is bounded implementation evidence, not the SPEC fastest-open-source milestone.

| Profiled input | Direct maps | Indexed maps | Hash-map fallback | Maximum indexed probes |
| --- | ---: | ---: | ---: | ---: |
| cyclic7-31 | 11 | 17 | 0 | 12 |
| eco11-31 | 18 | 3 | 0 | 16 |
| reimer6-31 | 19 | 7 | 0 | 9 |
| minrank_d_2_p_2_q_4_r_2-31 | 5 | 0 | 0 | n/a |

The explanatory route profile uses CPU 17 and four complete systems. Full bases and counters agree with uninstrumented same-source execution; build-call totals equal `matrixCalls`. Instrumented durations are excluded from timing estimates. Every matrix uses a packed layout on this corpus; the direct-map density threshold and fallback remain explicit implementation choices.

Two registered lean-bench kernels measure map construction, bounded row translation,
independent output validation and full packed map/support hashing. Input generation
is excluded. A fresh detached build uses source `8267339d38e6`, with byte-identical
compute drivers to the measured source. The explicit five-trial, five-size sweep
uses `--target-inner-nanos 4000000000` on leased CPU 67. All 50 completed rows
are retained. Both verdicts are consistent with the declared linear model.

| Kernel | n=1024 median | n=16384 median | Normalized slope | Signal-floor flags |
| --- | ---: | ---: | ---: | ---: |
| columnDirect | 8.821 µs | 137.621 µs | -0.005115 | 2 |
| columnIndex | 72.622 µs | 1228.183 µs | 0.012571 | 0 |

Signal-floor flags and lean-bench warmup/fit decisions remain in the exports;
no completed point is removed. Earlier one-trial and five-trial 500 ms observations remain separate in the
capsule with all configuration failures and flags; they are not pooled here.
The four-second CLI override differs from the initial registered 500 ms default.
The subsequent revision registers the measured duration and extends the sizes.
The direct/indexed kernels hash different complete payloads, so their timing
ratio is not an isolated construction-cost comparison. This finite scaling evidence does not prove asymptotic complexity.

| msolve mode | CPU | Hex/msolve process | Process median | Range | RSS Hex/msolve KiB |
| --- | ---: | ---: | ---: | --- | ---: |
| 2 | 2 | 2.2242 | 2.2388 | 0.8447–4.1916 | 111992/20312 |
| 42 | 95 | 2.3915 | 2.2588 | 0.7091–5.7307 | 111992/20312 |

Here mode is msolve's `-l` linear-algebra selection: 2 uses sparse exact
elimination and 42 selects probabilistic sparse/dense elimination.
Both identical RSS maxima were checked against all retained raw process
records: 111992 KiB for Hex and 20312 KiB for msolve in each mode.

Each matched msolve mode retains its first sweep, 56 successful processes and 28 equal complete basis pairs, with no failures or timeouts. The comparator is effective native Clang 23.1.3/znver5 msolve commit `3672113ee2c6`, direct executable, one thread and the same full reduced grevlex output. Complete source/build/ISA identities are archived. Earlier whole-matrix msolve ratios 3.5590/3.4374 are separate observations, not an adjacent comparison; the change is not attributed to this implementation from those external sweeps.

Validation passes the 2,180-job integrated library/theory/conformance build, independent 175-matrix/567 unique SymPy–Singular basis/1,288-division oracles, both 1,134-output CLI corpus checks, 34 benchmark checks and all project audits. Four Clang and four GCC ASan/UBSan variants pass. The Lean runtime uses
mimalloc, so ASan does not track every runtime object allocation; leak detection
is disabled in this mixed-runtime harness. Ownership evidence additionally
uses exact model comparisons and dedicated alias checks, and the subsequent
revision strengthens these with explicit refcounts and unchanged-byte assertions. Compiled counters require actual index, direct-remap and zero-init calls, including complete F4 and cache checks.

Direct tests compare multi-element, repeated-ID and large sparse maps with an independently populated hash map. The 64-collider indexed case charges exactly 2,272 work and 1,024 bytes; 65 colliders trigger the hash fallback after exactly 2,530 work and 2,048 bytes. Other tests cover malformed geometry, absent keys, maximum probe/chunk sizes, large scalar arguments, shared buffers, exclusive borrowed/output aliases and marked-linear growth. Exact resource tests include pre-existing table payload. The emitted corpus is regenerated only after all 1,134 baseline records agree except the charged work fields.

Validation/setup failures and their corrected logs remain in the capsule.

Windows/macOS native execution is unverified. Parallel scaling, extension adapters, larger native matrices, probabilistic/trace features, remaining theory and broader held-out/comparator coverage remain required. The issue stays open. These measurements establish neither leadership nor a language/runtime impossibility.


- [column-index-9449e25be93d.tar.gz](raw/column-index-9449e25be93d.tar.gz): `0fe6fded5e42b717259358e8983e54d719f03d3e619498725275eb79c65a54ab`; measured, baseline, final and kernel source blobs plus all raw observations and final validation.
