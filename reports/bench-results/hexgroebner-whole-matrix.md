# Bounded native Macaulay elimination

Untraced prime-field matrices can run in one native frame: validate canonical
rows, normalize distinct known reducer pivots, scatter targets, reuse the exact
sparse/dense scan and gather kernels, and extract the deterministic echelon or
independent remainders. Inputs are borrowed and immutable, including shared
reducer/target arrays. Traced elimination retains the existing route.

The 64-bit route admits at most 4096 columns, 1024 known reducers and 64 targets,
with a conservative work bound of `2^20`. It returns only a complete successful
reference result, including exact rows, sugars, aliasing and all counters.
Unsupported shapes continue in the ordinary implementation after the native
frame. Large limits saturate above every possible accepted total; non-machine
sugars continue portably. The [binding](../../HexGroebner/Elimination.lean) and
[C contract](../../HexGroebner/ffi/matrix_eliminate.c) specify layouts, bounds,
ownership and the bounded speculative failure path. The conservative bound
ensures a charged decline implies reference failure; F4 terminates that run or
resumption at the matrix failure. No hidden unbounded retry is introduced.

Measured source `e878b78cf727` has a fresh 276-job detached driver
build. Minimal compute SHA256 is `fb6a033166de667e753df9ba554203503bb7bb9e89ad893f351f18f064eb2a1d`.
Baseline source `9bac12f60779` is rebuilt through the same SDK
wrapper, with compute SHA256 `70a1c37a56f41677892073f5836203e141e4086eaff26fc0f17f7149f1198140`.

An obsolete local SDK linker wrapper references a missing Nix store script.
A task-local `LEAN_CC` wrapper restores the SDK compile/link flags and invokes
the existing SDK Clang 23.1.0 and LLD 23.1.0 directly. Its baseline binaries
differ from earlier builds of the same source. Both arms are freshly rebuilt
with this wrapper; fixed benchmarks use separate detached worktrees sharing
only pinned dependency packages. Exact wrappers, flags, compiler/build logs,
source blobs and manifests are retained. Native FFI compilation uses Clang
23.1.3. Earlier build variants and sources remain separate and are never pooled.

All timings are manual shared-host observations on AMD EPYC 9455, one requested
algorithm thread, automatically leased CPU, Lean 4.35.0-rc3 and exact AVX2 paths
where supported. Placement is not isolation. Small first/repeat CPUs are
58/89, medium 71/24, with adjacent AB then BA per input. Every completed
sample, failure and outlier is retained, without activity filters. Each of the
small, medium and fixed observations uses its first campaign and sole unchanged
repeat; no further unchanged repeat is used.

The small suite has 16 development inputs and the medium 14 larger inputs,
each in seven families at primes 32003 and 2147483647, grevlex, returning
complete monic reduced bases. These are not held-out or SPEC acceptance inputs.
Candidate time covers packing, F4 and final interreduction. Process time adds
initialization, parsing, output and identical GNU-time wrappers. Certificate
generation, independent final certification and kernel replay are separate
and excluded; these timings describe unchecked candidate production.

| Observation | Complete pairs | Candidate B/A | Median | Process B/A | Equal-family process |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 64 | 0.9179 | 0.9283 | 0.9462 | 0.9286 |
| medium | 56 | 0.9294 | 0.9739 | 0.9648 | 0.9648 |

All 240 CLI processes succeed, all 120 complete basis pairs agree, and every
algorithm counter agrees. There are zero measured failures or timeouts.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 1.1028 | 1.0794 | 1.0014 | 1.0123 |
| dense-quadratic | 1.0194 | 0.8030 | 0.8828 | 0.9534 |
| eco | 0.9783 | 0.9851 | 0.9935 | 0.9914 |
| kat | 0.9917 | 0.9329 | 1.0507 | 1.0556 |
| minrank | 0.6116 | 0.9727 | 0.8528 | 0.9561 |
| noon | 0.6907 | 0.8423 | 0.7964 | 0.8507 |
| reimer | 0.9922 | 0.9123 | 0.9557 | 0.9472 |

Small candidate ratios span 0.1161–2.8994; process ratios span 0.2672–2.5474.

Medium candidate ratios span 0.4730–3.1390; process ratios span 0.5671–2.8028.

Maximum child RSS across completed processes is 56460/57240 KiB
for baseline/new on small and 100624/100884 KiB on medium.
Logical packed-byte limits do not bound allocator capacity or process RSS.

Fresh fixed-benchmark builds complete 394/398 jobs for baseline/new. The fixed
sweep retains 240 points, with five declared repetitions, actual inner repeats
normalized and all complete structural output hashes equal.

| Fixed case | B/A mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.8408 | 0.8854 | 0.1695–1.8997 |
| cyclic5 | 1.4558 | 0.9317 | 0.5015–12.7527 |
| cyclic6 | 0.9870 | 0.9334 | 0.4346–2.9190 |
| katsura3 | 0.8271 | 0.8529 | 0.4499–1.4408 |
| reimer5 | 1.0917 | 0.9436 | 0.7238–2.6594 |
| cyclic6Small | 0.9694 | 0.9331 | 0.3514–3.2520 |

Cyclic5 and Reimer5 geometric means regress despite lower medians. Extreme
outliers remain in the estimates. These observations do not establish a uniform
speedup or isolate host, allocator or generated-code causes.

The matched medium msolve sweeps use the effective native Clang 23.1.3/znver5
build at commit `3672113ee2c6`, direct executable, one thread and full reduced
grevlex bases. The helper records complete source/build/ISA identities. Each
mode retains its first adjacent AB/BA sweep, 56 processes and 28 complete basis
pairs, with zero measured failures or timeouts.

| msolve mode | CPU | Hex/msolve process | Median | Range | RSS Hex/msolve KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 50 | 3.5590 | 4.0518 | 0.8338–7.5445 | 93320/20312 |
| 42 | 38 | 3.4374 | 3.6245 | 0.7149–9.1560 | 94868/20312 |

The fastest-open-source milestone is not met. Older source `8cf25024fa12`,
with the original linker arrangement, observed msolve ratios 2.2566/2.5293.
These are separate observations, not an adjacent comparison with this build;
the change cannot be attributed to the algorithm or linker from these sweeps.

An explanatory shape profile of that older source runs four complete systems
on CPU 45, with equal bases/counters and 80 recorded whole-matrix calls. Native
acceptance is Cyclic7 9/28, Eco11 7/21, Reimer6 16/26 and MinRank 5/5. Eco
reaches 10250 columns and 837 targets; Cyclic7 reaches 311 targets. The current
caps exclude many large matrices. The profile uses a temporary ELF wrapper and
a separately recorded working LLVM 23.1.3 linker, after retained local linking
failures. Instrumented runs are excluded from timing estimates.

The measured 2175-job local build passes, including theory examples and axiom
audits. A fresh 2179-job build on the default branch also passes with the exact
measured source manifest. Independent checks cover 175 matrices, 567 unique SymPy/Singular bases,
1288 divisions and 1134 degree/sugar profiles per CLI corpus. Both CLI checks,
32 benchmark checks and dependency, phase, released-manifest, copyright and
line-count audits pass. Four Clang and four GCC ASan/UBSan variants pass.

Direct tests sweep work, packed bytes and output entries, exact `2^20` and
`2^20 + 1` shape bounds, `2^63 - 1`/`2^63` limits and sugars, and shared
reducer/target arrays. Compiled counters require accepted joint and independent
calls. A seed-dependent F4 work-budget sweep compares every result/counter
prefix with portable execution; each variant records 3602 accepted and 274
deferred F4 whole-matrix attempts. An earlier coverage assertion failed because
its small F4 cases all accepted; the failure and final expanded test are kept.
The monomial checks retain 115 exclusive reuses and 24 workspace-aliased inserts
per variant. Marked-linear testing applies to its dedicated resize test.

Historical sources remain separate: `607b158b16db` caps targets at eight and
has 120 complete CLI basis/counter pairs; `8cf25024fa12` caps at 64 and has 120
CLI pairs and 120 fixed points. Both retain their own validation snapshots and
logs. The latter has one zero-process medium-repeat setup failure: SHA validation
rejects a manifest supplied as the baseline binary; the corrected command
supplies its sole measured repeat. No samples from these sources are pooled
with the current source or used to replace its regressions.

Windows/macOS native execution remains unverified. Large-matrix native coverage,
parallel scaling, extension adapters, trace/probabilistic support, remaining
proofs and broader comparator/held-out coverage remain required. The issue stays
open; no language-change impossibility is established.

- [whole-matrix-capped-607b158b16db.tar.gz](raw/whole-matrix-capped-607b158b16db.tar.gz): `375976b7ce43ac6009cd6ae41e91bbf0b788b1bba23dea19619162589831a014`.
- [whole-matrix-64-8cf25024fa12.tar.gz](raw/whole-matrix-64-8cf25024fa12.tar.gz): `7026976f987fb0ff3f6925c0124172b9c93b161ec19e58c638fe9dc762be121f`.
- [whole-matrix-reviewed-e878b78cf727.tar.gz](raw/whole-matrix-reviewed-e878b78cf727.tar.gz): `0a7a8c9b2e20dc0cbcd4b3021881201d1fa6e09b6a0be39a1be947e7b9e3af73`.
