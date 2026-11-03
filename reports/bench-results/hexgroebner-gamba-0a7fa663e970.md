# Finite-field F4 medium comparison with GamBa v0.3

Hex remains slower than both official GamBa v0.3 Linux binaries on the fixed
14-input medium development suite. The required family-balanced whole-process ratios are
2.9471 against AVX-512 and 3.4853 against AVX2. The larger cyclic/Eco families
show gaps of roughly 5.9/8.3× for AVX-512 and 7.6/9.5× for AVX2. Small-process
startup substantially influences the balanced aggregate. All 28 paired complete reduced
bases agree in each campaign. These measurements quantify part of the remaining
overall-fastest gap. GamBa is partially closed source and is excluded from the
fastest-fully-open-source acceptance set.

Hex source fingerprint `0a7fa663e970` identifies frozen snapshot
`8d83b29c3ef99062f4816ba6217117412f88f802`. Its freshly built compute executable
has SHA-256 `e913bc8129e2027e18056f4bfb9afb56d26cbfa3b7ca01005b9d384b0f6b5d50`;
Lean is 4.35.0-rc3, compiler revision
`470d5ce1400764999581fd26d5d72b00d990b0f4`. The driver links this pinned SDK's
`libinitialize_minimal.a`; its symbol audit confirms the elaborator frontend
initializer is absent, while the full-initialization reference contains it.
Generated driver import initializers and native providers remain initialized.
The ordinary full-initialization executable is separately built and checked.
This avoids elaborator startup in a driver that never elaborates Lean source;
no custom SDK/runtime patch is applied.
The minimal-initialization audit, compiler revision,
build log, source blobs and runtime patch are retained. This is the guarded
continuation engine in the [dispatch report](hexgroebner-continuation-dispatch.md).
Later source experiments are not measured by this campaign.

The [official v0.3 release](https://github.com/gblanco92/gamba/releases/tag/v0.3)
supplies AVX2 and AVX-512 executables. The public repository at
`f18c2db3a288f20f63f752b44e0171cf1cb86163` states that part of the implementation
is closed and cannot be rebuilt from the available source. Its source and
release metadata are archived; no vendor compiler flags are inferred.
Binary/download hashes and required library paths are retained. Each executable
runs through the recorded glibc 2.44 dynamic loader, with recorded libc/libm/
libgcc/pthread/rt hashes; that loader and startup are timed. Vendor binaries are
not republished in the evidence capsule. The URLs and hashes identify them. The original capsule retains recorded
library-path hashes; the supplementary audit resolves actual loaded files for
both arms, including Hex's SDK libc and loader.

| Vendor ISA | Download archive SHA-256 | Executable SHA-256 |
| --- | --- | --- |
| avx512 | `fec73f3f800fe1f39d87e545ccf055c2cb9a45422c2f33448a501531adfa2174` | `026d778c3e87ae37e1524b0e15055a3362e33e9d20a4b9f53adfb1534b33385e` |
| avx2 | `30db43526f7d570cabf3766acb9754b3c4f3f69d17a3da84f1540c440f5c7b48` | `14f56bf673c180c2681c662c11caa602ea4c1769f6de1d92817383aee2d6e3db` |

The suite is the [existing medium corpus](hexgroebner-medium.md): cyclic7,
Katsura8, Eco11, Noon5, Reimer6, MinRank and dense quadratic6, each over primes
32003 and 2147483647 with grevlex order. The same source inputs are parsed and
compared before measurement. It is a development suite, with no held-out,
hard-family or acceptance claim.

Each campaign runs all 14 adjacent AB pairs, then all 14 adjacent BA pairs, on shared host chungus2
(EPYC 9455). A is Hex, B is GamBa. The CPU is automatically leased; GamBa receives `-t 1`; the Hex algorithm is serial and has no thread-count
argument. Both processes inherit the same single-CPU affinity.
GamBa receives seed 10987, grevlex, verbosity 2 and full reduced-basis output; `--no-reduce`
and `--lead-mons` are absent. `--all-spairs` is also absent. The public v0.3
source default for `--max-spairs` is 2000, but the closed binary does not print
that default and the campaigns do not override it; its compiled value is
unverified. Both vendor `--help` outputs are retained. Hex uses degree scheduling and deterministic
elimination. GamBa's Monte Carlo computation has no certified-success or rank-
preservation guarantee inferred here. Equality of complete reduced bases is
checked outside the timing interval.

Identical GNU-time wrappers include launch, dynamic-loader work, startup,
parsing, candidate production, final interreduction and complete native-format
output. The processes have matched 60-second, 16-GiB address-space and 64-MiB
per-file output limits. Every completed sample, failure, RSS, seed, input/output
and host-load context is retained, with no host filtering or unchanged repeat.
Certificate generation, independent final certification and kernel checking
are excluded. Hex internal candidate timing is retained and is not compared
with GamBa's process wall time or printed internal timing.

| Hex/GamBa process ratio | Equal-family geometric mean | Median | Range | CPU | Peak RSS Hex/GamBa KiB |
| --- | ---: | ---: | --- | ---: | ---: |
| avx512 | 2.9471 | 2.7660 | 1.0610–9.4940 | 60 | 124052/42292 |
| avx2 | 3.4853 | 3.5423 | 1.0160–9.7120 | 3 | 124052/38300 |

The family-balanced aggregate is the SPEC metric; it intentionally gives each
family equal weight. For comparison, total process wall time summed across all
samples has different weighting toward longer cases:

| Vendor ISA | Hex total ms | GamBa total ms | Ratio of totals |
| --- | ---: | ---: | ---: |
| avx512 | 6093.163 | 979.359 | 6.2216 |
| avx2 | 5677.330 | 768.678 | 7.3858 |

These totals are descriptive observations, not a replacement acceptance metric
or an estimate of pure arithmetic speed. Several families take only 5–20 ms;
startup and full output remain included. No synthetic no-work startup baseline
is collected. Post-capture analysis computes totals, medians and ranges from the
retained wall samples, with no filtering or new scientific timing run.

An untimed post-capture operational audit records both ELF interpreter/NEEDED
lists, loader resolutions and mapped-file hashes for each arm. It samples nice
value 0 for both GamBa binaries and Hex. GamBa has one observed OS thread; Hex
has 1, 3 or 4 during startup/execution, including runtime threads, while its F4
algorithm remains serial and all threads share the inherited single CPU.
These later observations do not prove the historical priority/thread state of
the timed processes. The public vendor source calls `setpriority` with a value
from an unpublished header, so that historical setting is left unverified.
The release receipts, help outputs, audit script and full outputs are retained.

Each campaign completes 56 processes and 28 complete-basis comparisons with no
failures or timeouts. The mean first combines paired ratios within each family
geometrically, then weights the seven families equally. Both field widths and
both order blocks are retained. The two ISA campaigns are separate observations,
not a matched AVX2/AVX-512 speed comparison, and are not pooled.

| Family | Hex/AVX-512 GamBa | Hex/AVX2 GamBa |
| --- | ---: | ---: |
| cyclic | 5.9333 | 7.5675 |
| dense-quadratic | 1.7752 | 1.8515 |
| eco | 8.3326 | 9.5405 |
| kat | 2.4810 | 3.4986 |
| minrank | 1.3570 | 1.5030 |
| noon | 1.9044 | 2.2904 |
| reimer | 3.4318 | 3.8805 |

Every family mean is above one. Small process timings remain sensitive to
startup and shared-host variation; raw absolute times and variability remain
visible. These finite results neither prove a general speed ranking nor
attribute the gap to an unavoidable language/runtime cost. Remaining acceptance
work includes the fixed balanced hard suite, held-out inputs, solved coverage,
other current fully open-source comparators, parallel cases, finite extensions
and separate certification/native-verification/kernel-checking costs.

[Complete raw capsule](raw/f4-gamba-0a7fa663e970.tar.gz): SHA-256 `21297de9ea617956c896a6f04890d0a568914d71e2c1385c17ae6d700ed9392c`, 659 payloads. Every payload was read back and its digest checked. The capsule contains both complete campaigns, full outputs, all inputs, vendor binary/source/release identity, runtime library hashes, the exact measurement script and frozen Hex source/build provenance.

[Supplementary source, native-boundary and loader audit](raw/f4-followup-audit-a3938be198b4.tar.gz): SHA-256 `de837be4725c97920a96d8d308823b66700e8eef3357c782d3a51892a9f30c5a`, 50 payloads, read back and digest checked. This includes the added workspace-boundary checks and eight final native configurations, post-capture GamBa medians/totals, both help outputs and actual loaded-file/priority/thread audit. Timed raw outputs and the original capture scripts remain unchanged in the original capsules.
