# Portable F4 performance gaps and literal bounds

Historical comparator-build caveat: compiler labels and `-march=native` commands
below record the original build description. Nix can strip requested native CPU
tuning, and effective flags were not independently established for every older
build. These samples remain retained observations. The direct-ELF comparison
with recorded effective native flags in [the driver report](hexgroebner-driver.md)
supersedes them as evidence of the current msolve gap.

The portable candidate engine at `425de3aa42` solves 14 of 16 frozen diagnostic
inputs within the matched ten-second limit; msolve solves all 16. All 28 pairs
of completed reduced bases agree coefficient-for-coefficient. Hex times out on
both eco-10 inputs in both AB/BA blocks. This is a measured coverage and speed
gap, not a fastest-open-source result or evidence that language changes are
necessary.

The [summary](hexgroebner-msolve-425de3aa42.json) and
[complete evidence archive](hexgroebner-msolve-425de3aa42.tar.gz) retain the
frozen suite, all 64 scheduled timing records, complete outputs, comparisons,
source/driver hashes, build configuration, manifests, licenses, host context
and diagnostic profiles. The archive also retains the first timer attempt's
exception and output: its Python lacked `os.pidfd_open`, so it produced no
usable timing row. The corrected timer uses libc's pidfd interface and `wait4`.
No completed sample is removed because of host activity.

## Matched diagnostic baseline

The host is `chungus2`, AMD EPYC 9455, with one automatically leased logical
CPU (32), one computational thread and a 16 GiB address-space limit per child.
Each input runs in adjacent AB then BA order, with A = Hex and B = msolve.
Every process includes startup, parsing and complete reduced-basis output;
Hex's internal candidate time is also retained separately. Certificate
production, independent native verification and kernel checking are absent.
Outputs have a common 64 MiB file limit. Runtime limits, failures, RSS and
host load are retained. Small-case ratios include substantial startup cost.

Both fields use ordinary polynomial rings and grevlex in the written variable
order, with no implicit field equations. The two moduli are 32,003 and
2,147,483,647. Public input files come from the pinned GamBa repository revision
and are converted without changing variable precedence or coefficients modulo
the stated prime; exact source hashes are in the suite. The additional dense
quadratic case has five variables and a fixed LCG seed of 10,987. `kat6` is the
public file name and has six variables.

msolve is version 0.11.0 at `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built
with GCC 16.2, `-O3 -march=native`, GMP and FLINT 3.6.0. All 71 upstream tests
pass. The invocation is `-g 2 -t 1 -l 2`: exact sparse elimination and the full
reduced grevlex basis, with no FGLM or root-solving pipeline. Its source is
GPL-2.0-or-later. Hex uses Lean `v4.35.0-rc3`, default generated C, packed
portable accessors and the existing native wide-word arithmetic primitives.
The same host ISA is available to both programs; Hex has no new SIMD kernel.

The following are geometric means of the two paired **Hex/msolve whole-process
wall-time ratios**, separately for each input and field. A ratio above one is
a loss for Hex. No family-balanced leadership statistic is computed from this
incomplete solved coverage.

| Input | p = 32,003 | p = 2,147,483,647 |
| --- | ---: | ---: |
| cyclic-5 | 2.71 | 2.84 |
| cyclic-6 | 11.91 | 12.87 |
| kat6 | 3.64 | 4.10 |
| eco-10 | timeout | timeout |
| noon-4 | 2.31 | 2.48 |
| Reimer-5 | 77.98 | 79.59 |
| MinRank(2,2,3,2) | 1.93 | 1.99 |
| dense quadratic, 5 variables | 2.58 | 2.76 |

For eco-10, msolve completes in 136–140 ms at the smaller prime and 80–85 ms
at the larger prime; all four Hex calls hit ten seconds. Reimer-5 takes
1.17–1.34 seconds in Hex versus 14–17 ms in msolve. Whole-process peak RSS is
67,516–82,980 KiB for Hex and 11,716–13,432 KiB for msolve. These observations
include runtime/setup storage and do not equal the API's packed-payload counter.

This small diagnostic suite has six public families plus dense quadratic
systems. It does not replace the SPEC's hard public cases, held-out inputs,
finite-extension coverage, minimum comparator set or parallel sweeps.

## Removing repeated literal parsing

A ten-second eco-10 profile on separately leased CPU 58 locates 20.61% of
samples in the generated elimination loop, 11.94% in GMP decimal parsing,
7.93% in a GMP conversion helper, and further costs in monomial operations,
reference counting and allocation. These are diagnostic samples, not timing
arms. A debugger stop at the thousandth GMP decimal parse shows the string
`4294967296`, called from `MonomialTable.internOwned`'s exponent loop.

Generated C emits `lean_cstr_to_nat("4294967296")` each time it evaluates the
bound. This is the already reported compiler issue
[lean4#16007](https://github.com/leanprover/lean4/issues/16007). The equivalent
`> 4294967295` guard avoids the parse. Packed exponent checks and sums compare
native UInt64 values; their coordinates are at most 2^32−1, so a sum fits in
UInt64 before the representation check. Nat index guards use the equivalent
upper bound as well. Overflow/collision/order conformance continues to pass.
The only remaining large literal in the monomial module's generated C is a
once-initialized 2^64 degree bound.

An adjacent AB/BA lean-bench comparison isolates this change on fixed
candidate calls over p = 65,537. A uses source fingerprint `aab7c5780f68`;
B uses `d481e4329e7e`. The latter also clarifies error types and oracle modes;
those error paths are not taken by these calls. Each arm retains three
repetitions with a 0.5-second inner calibration floor, including full output
hashing. Both arms have identical basis hashes at every repetition.

| Case | AB medians, A → B | BA medians, A → B | Paired geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-6 | 177.021 → 142.035 ms | 200.969 → 152.244 ms | 0.780 |
| Katsura-3 | 0.602 → 0.515 ms | 0.513 → 0.421 ms | 0.838 |

The 24 retained samples show an observed reduction of roughly 22% and 16% on
these two cases. Absolute times are host-specific. This is a local workaround
for a compiler cost, not an argument that upstream changes are prerequisites.

The comparison's [metadata and exact measuring script](hexgroebner-literals-aab7c5780f68-d481e4329e7e.measurement.json),
[before manifest](hexgroebner-literals-before-aab7c5780f68.manifest),
[after manifest](hexgroebner-literals-after-d481e4329e7e.manifest)
and eight matching `-b{0,1}-{cyclic6,katsura3}-{A,B}.json` / `.log` exports
retain commands, all samples, hashes, memory and variability.

Outstanding costs include weak pair installation, boxed multiplied-exponent
scratch arrays, scalar checked byte access and fresh matrix workspaces. These
require algorithm and representation work, including useful native kernels.
There is no demonstrated language-impossibility barrier. Complete certificates,
theory and the remaining performance acceptance work stay with
[#10987](https://github.com/kim-em/hex-dev/issues/10987).
