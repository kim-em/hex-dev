# HexKroneckerMathlib performance

## Result

30/46 paired comparisons have a median-margin magnitude no
larger than their median absolute deviation and are **unresolved at this
measurement resolution**. The numerical median comparison and this description
of variation are reported separately; no sample is discarded or replaced.

The complete sweep contains 23 accepted identities and 7
preflight declines. 15/23 accepted cases have a smaller per-arm
baseline-subtracted median than both `ring` and `grobner`. The comparison across
all accepted cases is **not passed**.
The absolute candidate ceilings are **passed**.
The [opt-in shipping condition](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#fresh-module-comparisons-and-shipping-bar)
requires the complete family table and passing absolute ceilings. Its status
is **passed**. No default tactic chain changes.

Of the seven grid cases that lost to `ring` in the shipping table, 4/7 are now at or below its median. 1/5 determinant medians are no larger than the shipping values. The numerical optimization bar is **not passed**. These are fresh-module comparisons; controlled kernel attribution is reported separately. The previously losing small cases still above `ring` are `GridK1D8`, `GridK2D2`, `GridK4D2`.

The smallest case's controlled kernel median is 3.715 ms (all six samples
below 5 ms), and all five determinant kernel medians improve. Reflection
still costs about 4 ms in the instrumented smallest-case session, principally
Sym.Arith canonicalization and instance classification. That remaining work
can keep the total tactic cost above `ring` even after the kernel improvement;
the fresh-module measurements below determine the numerical bar separately.

## Protocol and provenance

The measured checkout is `237ad74f70ab885fb4c168a64c948f4d16810196`, using
`leanprover/lean4:v4.34.0`. The record includes the pinned dependency
revisions and SHA-256 hashes of the complete measured source closure.
The Kronecker implementation, proof probes, and sweep runner match those
measured sources. The measured Lake file is preserved in the source archive.

[Raw samples, source hashes, artifacts, and profiles](data/hex-kronecker-mathlib/sweep-translation.json.gz) retain every
completed sample. Six adjacent three-arm blocks use Ring/Kronecker/Grobner
order in odd rounds and its reverse in even rounds. The middle candidate is
adjacent to both references, giving each comparison six alternating AB/BA
pairs. Each arm has its own adjacent fresh import-only baseline, with
baseline/proof order also alternating. Baselines are subtracted round by
round; negative differences are retained. Paired margins are reference delta
minus candidate delta, so a positive value favors Kronecker.

All arms use identical propositions and shared construction modules. The
runner removes each measured module's artifacts before `lake build` and warms
only dependencies. It uses one automatically leased CPU on the shared host.
Host load, CPU accounting, raw compiler output, RSS and axiom audits are
recorded per sample. An interrupted schedule resumes missing arm samples
without replacing any completed sample; execution segments preserve the
original runner hashes, CPU and environment. A resumption never replaces
completed samples.

The preregistered ceilings are 30 seconds per accepted grid case, 60 seconds
per accepted determinant case, and a 180-second cleanup timeout. Ceilings
apply to raw candidate wall time, including imports. The table reports
baseline-subtracted per-arm medians in milliseconds. Ratios are Kronecker
divided by the reference median and are shown only when both are positive.
The numerical comparison uses these per-arm medians; paired-margin signs
remain supplementary evidence. Losing cases stay in the table and do not
prevent explicitly opt-in shipping under the SPEC's shared exception.

## Shared-host execution context

The first sweep of the final implementation overlapped another full sweep and local
verification builds, including the full proof-probe target. Those builds
were started as part of this work and contributed concurrent activity.
The recorded whole-host Lake/Lean process count had median 14
and maximum 105. It includes other work on the shared host, so these
counts do not identify the origin of every process. All observations remain
evidence under the shared-host policy.

The shipping sweep recorded median 3 and maximum 16 concurrent Lake/Lean processes.


## reflected-identities and determinant-identities

| Case | D | N | Kronecker ms | ring ms | grobner ms | K/ring | K/grobner | Ceiling |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| GridK1D2 | 3 | 14 | 56.614 | 91.401 | 84.032 | 0.619 | 0.674 | pass |
| GridK1D4 | 5 | 34 | 38.117 | 156.907 | 96.305 | 0.243 | 0.396 | pass |
| GridK1D8 | 9 | 98 | 122.751 | 58.769 | 83.510 | 2.089 | 1.470 | pass |
| GridK1D16 | 17 | 322 | 210.310 | 67.542 | 93.969 | 3.114 | 2.238 | pass |
| GridK2D2 | 9 | 44 | 60.329 | 45.293 | 7.464 | 1.332 | 8.083 | pass |
| GridK2D4 | 25 | 174 | 12.839 | 31.096 | 77.891 | 0.413 | 0.165 | pass |
| GridK2D8 | 81 | 890 | 33.795 | 93.273 | 128.587 | 0.362 | 0.263 | pass |
| GridK2D16 | 289 | 5490 | -261.058 | 298.547 | 158.620 | — | — | pass |
| GridK3D2 | 27 | 161 | 42.896 | 237.485 | 32.825 | 0.181 | 1.307 | pass |
| GridK3D4 | 125 | 1124 | 261.600 | -66.889 | -20.988 | — | — | pass |
| GridK3D8 | 729 | 10934 | 40.548 | 146.797 | 546.110 | 0.276 | 0.074 | pass |
| GridK3D16 | 4913 | 137563 | 278.760 | 3234.030 | 4887.749 | 0.086 | 0.057 | pass |
| GridK4D2 | 81 | 566 | 757.947 | 153.258 | -126.878 | 4.946 | — | pass |
| GridK4D4 | 625 | 6874 | 131.443 | 257.721 | 425.958 | 0.510 | 0.309 | pass |
| GridK4D8 | 6561 | 124658 | 171.904 | 1610.389 | 4477.787 | 0.107 | 0.038 | pass |
| GridK6D2 | 729 | 5831 | -51.122 | 74.249 | -85.398 | — | — | pass |
| GridK6D4 | 15625 | 203124 | 360.024 | 478.487 | 2128.336 | 0.752 | 0.169 | pass |
| GridK8D2 | 6561 | 59048 | -58.112 | 93.207 | 163.884 | — | — | pass |
| DetN3K2D1 | 16 | 176 | 48.877 | 337.032 | 316.537 | 0.145 | 0.154 | pass |
| DetN4K3D1 | 125 | 2125 | 10.468 | 917.588 | 736.116 | 0.011 | 0.014 | pass |
| DetN3K3D2 | 343 | 4116 | 271.796 | 268.518 | 289.564 | 1.012 | 0.939 | pass |
| DetN4K2D2 | 81 | 1296 | 408.356 | 560.107 | 549.567 | 0.729 | 0.743 | pass |
| DetN5K3D1 | 216 | 4968 | 357.454 | 17372.332 | 8824.961 | 0.021 | 0.041 | pass |

## Per-case before/after

Before values come from the [retained shipping sweep](data/hex-kronecker-mathlib/sweep-shipping.json.gz); after values come from the complete new sweep above. These historical wall-time columns use different execution segments and are not adjacent before/after pairs. Controlled kernel attribution is reported separately. Every value is retained, including negative baseline-subtracted medians.

| Case | Before K ms | After K ms | Before ring ms | After ring ms | Before grobner ms | After grobner ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| GridK1D2 | 77.508 | 56.614 | 47.322 | 91.401 | 79.267 | 84.032 |
| GridK1D4 | 76.461 | 38.117 | 73.423 | 156.907 | 90.167 | 96.305 |
| GridK1D8 | 83.617 | 122.751 | 77.616 | 58.769 | 81.752 | 83.510 |
| GridK1D16 | 86.323 | 210.310 | 88.315 | 67.542 | 140.768 | 93.969 |
| GridK2D2 | 35.474 | 60.329 | 4.705 | 45.293 | 82.358 | 7.464 |
| GridK2D4 | 81.034 | 12.839 | 83.305 | 31.096 | 86.879 | 77.891 |
| GridK2D8 | 85.279 | 33.795 | 86.260 | 93.273 | 95.422 | 128.587 |
| GridK2D16 | 86.199 | -261.058 | 110.181 | 298.547 | 175.130 | 158.620 |
| GridK3D2 | 93.528 | 42.896 | 74.798 | 237.485 | 85.212 | 32.825 |
| GridK3D4 | 84.871 | 261.600 | 97.783 | -66.889 | 87.148 | -20.988 |
| GridK3D8 | 101.741 | 40.548 | 194.479 | 146.797 | 320.780 | 546.110 |
| GridK3D16 | 275.352 | 278.760 | 1392.564 | 3234.030 | 2704.733 | 4887.749 |
| GridK4D2 | 100.410 | 757.947 | 94.206 | 153.258 | 97.439 | -126.878 |
| GridK4D4 | 93.211 | 131.443 | 113.287 | 257.721 | 183.785 | 425.958 |
| GridK4D8 | 285.440 | 171.904 | 894.794 | 1610.389 | 2452.135 | 4477.787 |
| GridK6D2 | 97.084 | -51.122 | 92.294 | 74.249 | 107.098 | -85.398 |
| GridK6D4 | 186.995 | 360.024 | 295.516 | 478.487 | 1293.175 | 2128.336 |
| GridK8D2 | 97.890 | -58.112 | 100.023 | 93.207 | 122.009 | 163.884 |
| DetN3K2D1 | 46.952 | 48.877 | 102.599 | 337.032 | 110.265 | 316.537 |
| DetN4K3D1 | 156.469 | 10.468 | 662.976 | 917.588 | 685.631 | 736.116 |
| DetN3K3D2 | 90.542 | 271.796 | 183.618 | 268.518 | 192.447 | 289.564 |
| DetN4K2D2 | 106.877 | 408.356 | 387.077 | 560.107 | 307.353 | 549.567 |
| DetN5K3D1 | 279.116 | 357.454 | 9210.743 | 17372.332 | 6701.527 | 8824.961 |

## Measured regimes

The determinant-shaped group wins 4/5 comparisons against both references. The accepted multivariate expansion grid with degree at least four wins 8/9. These are the measured winning regimes; the full table also shows individual wins outside them.

The losing cases are `GridK1D8`, `GridK1D16`, `GridK2D2`, `GridK3D2`, `GridK3D4`, `GridK4D2`, `GridK6D2`, `DetN3K3D2`. The detailed tables retain their numerical ordering and measurement spread. The resolution table below distinguishes the numerical ordering from shared-host variation. No dispatch threshold or default-chain entry is inferred from small unresolved differences.

The grid has atom counts `1, 2, 3, 4, 6, 8` and degrees `2, 4, 8, 16`.
Accepted powers of sums are compared with independently expanded SymPy
integer polynomials. The one-atom rows use `(x + 1)^d` so that they also exercise expansion.
Historical source states and workloads remain in the retained records;
no completed sample is discarded.
The determinant family varies matrix dimension, shared
atom count, and entry degree; its left side explicitly expands the Leibniz
formula, and its right side is independently expanded with SymPy.

## dense-box-declines

Grid points outside the budget check preflight directly without constructing
an expanded right side. The independent-atom case has 25 linear entry atoms
in a `5 × 5` determinant and invokes the tactic under a guarded diagnostic.
It must report the dense-box decline before any packing.

| Case | Dense digits (saturated) | Packed bits (saturated) | Before decline ms | After decline ms |
| --- | ---: | ---: | ---: | ---: |
| GridK4D16 | 65537 | 2923234 | 7.021 | -230.023 |
| GridK6D8 | 65537 | 12223142 | 44.509 | 93.993 |
| GridK6D16 | 65537 | 16777217 | 1.648 | 140.452 |
| GridK8D4 | 65537 | 5859374 | 3.340 | 266.600 |
| GridK8D8 | 65537 | 16777217 | 1.824 | 634.134 |
| GridK8D16 | 65537 | 16777217 | 10.342 | -38.302 |
| IndependentN5 | 65537 | 16777217 | 76.336 | -22.580 |

A saturated count is a certified lower bound, not an exact size. Scope
outside the accepted dense-box regime is recorded as delegated scope and is
not counted as a packed success.

## Serialized proofs and trust

The sizes below are `.olean` bytes for the proof modules, including their
module metadata. Source and `.ilean` sizes are in the raw record.
Every accepted theorem's axiom set is a subset of `propext`, `Classical.choice`,
and `Quot.sound`. The same audit is run for all six public soundness theorems
and the uniform-ring and characteristic-seven examples.

| Case | Kronecker bytes | ring bytes | grobner bytes |
| --- | ---: | ---: | ---: |
| GridK1D2 | 13304 | 39728 | 20352 |
| GridK1D4 | 14320 | 65104 | 22840 |
| GridK1D8 | 16352 | 130584 | 27816 |
| GridK1D16 | 20416 | 321136 | 37768 |
| GridK2D2 | 14112 | 44112 | 20232 |
| GridK2D4 | 15512 | 79592 | 23168 |
| GridK2D8 | 18312 | 175360 | 28848 |
| GridK2D16 | 23912 | 461512 | 40208 |
| GridK3D2 | 15752 | 60688 | 26008 |
| GridK3D4 | 19552 | 175872 | 36544 |
| GridK3D8 | 31496 | 886352 | 69856 |
| GridK3D16 | 73296 | 8376040 | 188456 |
| GridK4D2 | 17648 | 83504 | 30336 |
| GridK4D4 | 26088 | 377336 | 56680 |
| GridK4D8 | 66480 | 4733048 | 187104 |
| GridK6D2 | 22208 | 146576 | 41656 |
| GridK6D4 | 50320 | 1441848 | 141152 |
| GridK8D2 | 27792 | 238032 | 56144 |
| DetN3K2D1 | 23960 | 355984 | 63032 |
| DetN4K3D1 | 45000 | 3903152 | 173336 |
| DetN3K3D2 | 28872 | 543184 | 86088 |
| DetN4K2D2 | 33880 | 1767544 | 138480 |
| DetN5K3D1 | 85480 | 32957584 | 450080 |

## Comparison resolution

MAD is the median absolute deviation of the six paired margins from their median. An ordering is marked unresolved when the magnitude of that median does not exceed its MAD. This descriptive comparison does not add a sampling filter or change the preregistered numerical bar. Small tactic costs can be obscured by variation in the adjacent import-dominated builds.

| Case | Margin vs ring ms | MAD ms | Margin vs grobner ms | MAD ms | Resolution |
| --- | ---: | ---: | ---: | ---: | --- |
| GridK1D2 | 13.506 | 61.855 | 43.281 | 88.177 | unresolved: ring, grobner |
| GridK1D4 | 140.457 | 200.861 | 152.428 | 141.177 | unresolved: ring |
| GridK1D8 | 1.042 | 225.677 | -14.436 | 83.323 | unresolved: ring, grobner |
| GridK1D16 | -184.822 | 290.913 | -209.512 | 147.685 | unresolved: ring |
| GridK2D2 | -22.557 | 75.216 | -5.946 | 374.423 | unresolved: ring, grobner |
| GridK2D4 | 20.335 | 102.911 | -4.977 | 73.520 | unresolved: ring, grobner |
| GridK2D8 | 59.478 | 422.590 | 44.588 | 239.440 | unresolved: ring, grobner |
| GridK2D16 | 559.605 | 718.828 | 476.650 | 376.706 | unresolved: ring |
| GridK3D2 | -6.290 | 553.434 | 92.339 | 706.362 | unresolved: ring, grobner |
| GridK3D4 | -511.284 | 624.844 | -40.649 | 186.779 | unresolved: ring, grobner |
| GridK3D8 | 89.262 | 1591.331 | 583.212 | 129.219 | unresolved: ring |
| GridK3D16 | 2315.542 | 1450.190 | 4092.328 | 2376.831 | margin exceeds MAD |
| GridK4D2 | -863.803 | 1974.588 | -1321.177 | 1177.776 | unresolved: ring |
| GridK4D4 | 113.543 | 113.461 | 283.573 | 375.863 | unresolved: grobner |
| GridK4D8 | 1553.385 | 753.669 | 4420.783 | 1033.928 | margin exceeds MAD |
| GridK6D2 | -107.858 | 491.401 | -30.562 | 374.131 | unresolved: ring, grobner |
| GridK6D4 | 121.628 | 770.637 | 1861.950 | 329.735 | unresolved: ring |
| GridK8D2 | 353.963 | 1075.383 | 151.685 | 278.714 | unresolved: ring, grobner |
| DetN3K2D1 | 273.948 | 283.907 | 197.944 | 156.949 | unresolved: ring |
| DetN4K3D1 | 848.245 | 418.484 | 608.054 | 282.411 | margin exceeds MAD |
| DetN3K3D2 | 181.491 | 200.743 | 81.753 | 162.355 | unresolved: ring, grobner |
| DetN4K2D2 | 367.162 | 521.601 | 250.233 | 375.809 | unresolved: ring, grobner |
| DetN5K3D1 | 16740.797 | 5329.477 | 8514.689 | 322.215 | margin exceeds MAD |

## Paired signs

Each sign records one completed reference-minus-candidate margin in trial order. Positive favors Kronecker, negative favors the reference, and zero is a tie. Small baseline-subtracted differences may be dominated by shared-host variation; all signs and negative baseline differences are retained.

| Case | vs ring | vs grobner |
| --- | --- | --- |
| GridK1D2 | + + − − + − | + + + − − + |
| GridK1D4 | + + + + + − | + + + + − + |
| GridK1D8 | − + − + + − | + − + + − − |
| GridK1D16 | + − − − + + | + − − − − + |
| GridK2D2 | − − − − + + | − − − + + + |
| GridK2D4 | + + + + − − | + − + + − − |
| GridK2D8 | + + − + + − | + − − + + + |
| GridK2D16 | − + − + + + | − + + + + + |
| GridK3D2 | + − − + − + | + − + + − + |
| GridK3D4 | + − − − − − | − + + + − − |
| GridK3D8 | + + + − + − | + + + + + + |
| GridK3D16 | + + + + + + | + + + + + + |
| GridK4D2 | + + − − − − | + − − + − − |
| GridK4D4 | + − + + + − | + + + + − − |
| GridK4D8 | + + + + + + | + + + + + + |
| GridK6D2 | + − − + − + | + − + − − + |
| GridK6D4 | + + − − + + | + + + + + + |
| GridK8D2 | + + + + − − | + + + + − − |
| DetN3K2D1 | + − + + + + | + + + − + + |
| DetN4K3D1 | + − + + + + | + + + + − + |
| DetN3K3D2 | − + − + + + | + + − + + + |
| DetN4K2D2 | + + − + + − | − + − + + + |
| DetN5K3D1 | + + + + + + | + + + + + + |

## Kernel-only profiles

The accepted-family profiles replay `Kernel.exprEq` through
`decide +kernel`, using the quoted trees from their shared construction
modules. They exclude reflection, proof production, and the `fromGrind`
translation reduced by the actual tactic certificate. The decline-family
profile evaluates only preflight: it intentionally performs no packed
certificate check. Raw profiler output is retained in the record.

| Family | Representative | Kernel type checking ms | Fresh module wall ms | Axioms |
| --- | --- | ---: | ---: | --- |
| reflected-identities | GridK3D8 | 29.900 | 7104.342 | propext |
| determinant-identities | DetN4K3D1 | 44.200 | 3837.659 | propext |
| dense-box-declines | IndependentN5 | 347.000 | 4100.263 | none |

[Kernel profiles and their source hashes](data/hex-kronecker-mathlib/kernel-profiles-translation-repeat.json.gz) record the dedicated fresh profile runs. The kernel column is Lean’s aggregate type-checking timer. The separate fresh-module wall time includes imports and compilation. The decline profile proves the preflight result using `decide +kernel`; it performs no packed evaluation. Earlier compiled-guard diagnostics remain in the historical sweep records and are not used as kernel profiles.

The three profiles were repeated once, before the unchanged full sweep. The first observations are retained below. These are unpaired single profiles on the shared host, so their differences do not establish an implementation regression. In particular, the unchanged decline checker varies substantially between observations.

| Case | First kernel ms | Repeated kernel ms |
| --- | ---: | ---: |
| GridK3D8 | 24.400 | 29.900 |
| DetN4K3D1 | 30.100 | 44.200 |
| IndependentN5 | 485.000 | 347.000 |

[First profiles](data/hex-kronecker-mathlib/kernel-profiles-translation.json.gz) preserve their full logs and source hashes.

The Mathlib-free [computational report](hex-kronecker-performance.md) supplies
complexity evidence in the packed bit size, operation profiles and the full
plain/signed product comparison. These proof probes measure total tactic
cost, including reflection, emitted literals, and synchronous kernel checking.

## Kernel attribution

[All attribution samples, compiler logs, runner text, and measured source archives](data/hex-kronecker-mathlib/attribution-kernel.tar.gz)
are retained. Each controlled comparison uses six adjacent AB/BA pairs on one
automatically leased CPU. Tables report Lean's aggregate `type checking` timer
in milliseconds, with `profiler.threshold=0`. No import baseline is subtracted
from this timer. The paired gain is reference minus candidate; MAD describes
variation across the six gains. Different comparisons ran on different leased
CPUs and execution segments, so their absolute medians are not additive.

The cap comparison changes only the diagnostic budget from 16,777,216 to
65,536 bits on the original checker; all seven identities fit both budgets.
This isolates the large threshold literal without changing the shipping
budget or probes. Root-only replay then removes size reporting and budget
checking entirely. Direct recursion also uses primitive arithmetic and the
bit-length preflight, whose equality with the public size report is proved.
The final translation comparison changes only `fromGrind` to a direct recursor.

### Threshold literal: original budget → diagnostic smaller cap

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| GridK1D2 | 8.720 | 6.595 | 1.195 | 0.500 |
| GridK1D4 | 11.565 | 13.850 | -2.770 | 4.160 |
| GridK1D8 | 30.950 | 34.350 | 8.250 | 7.350 |
| GridK2D2 | 12.450 | 11.135 | -0.385 | 5.415 |
| GridK3D2 | 19.600 | 21.450 | 0.535 | 4.700 |
| GridK4D2 | 24.100 | 24.700 | 0.100 | 6.050 |
| GridK6D2 | 37.450 | 29.100 | 4.500 | 5.950 |

### Kernel form: original checker → root-only replay

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| GridK1D2 | 6.530 | 3.290 | 2.650 | 0.895 |
| GridK1D4 | 7.070 | 6.685 | 2.325 | 2.300 |
| GridK1D8 | 14.000 | 9.260 | 4.865 | 0.490 |
| GridK2D2 | 12.475 | 6.050 | 2.870 | 1.315 |
| GridK3D2 | 17.200 | 14.150 | 5.820 | 11.445 |
| GridK4D2 | 16.050 | 14.450 | 4.715 | 5.600 |
| GridK6D2 | 30.450 | 24.200 | 6.100 | 7.400 |

### Traversals: root-only replay → direct recursors and primitives

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| GridK1D2 | 5.020 | 2.935 | 1.375 | 1.005 |
| GridK1D4 | 5.310 | 4.100 | 0.980 | 0.365 |
| GridK1D8 | 18.000 | 14.050 | 3.880 | 2.615 |
| GridK2D2 | 6.725 | 6.065 | 1.040 | 2.160 |
| GridK3D2 | 9.730 | 5.735 | 1.845 | 3.120 |
| GridK4D2 | 31.650 | 27.350 | -2.235 | 12.650 |
| GridK6D2 | 72.800 | 48.150 | 3.200 | 26.750 |

### Translation: equation compiler → direct `fromGrind` recursor

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| GridK1D2 | 3.305 | 2.900 | 0.395 | 0.165 |
| GridK1D4 | 4.540 | 3.870 | 0.690 | 0.135 |
| GridK1D8 | 7.055 | 6.190 | 0.925 | 0.040 |
| GridK2D2 | 4.200 | 3.715 | 0.485 | 0.090 |
| GridK3D2 | 7.070 | 6.395 | 0.675 | 0.170 |
| GridK4D2 | 11.650 | 9.995 | 1.590 | 0.100 |
| GridK6D2 | 23.550 | 20.600 | 2.350 | 0.200 |

### Determinants: original checker → direct root-only replay

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| DetN3K2D1 | 24.550 | 13.300 | 11.600 | 2.300 |
| DetN4K3D1 | 78.700 | 41.550 | 34.450 | 4.400 |
| DetN3K3D2 | 39.950 | 24.050 | 13.850 | 19.600 |
| DetN4K2D2 | 58.000 | 35.650 | 18.300 | 10.650 |
| DetN5K3D1 | 264.000 | 153.000 | 130.000 | 31.000 |

### Determinants: original checker → final translation and replay

| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |
| --- | ---: | ---: | ---: | ---: |
| DetN3K2D1 | 28.950 | 12.850 | 15.950 | 0.550 |
| DetN4K3D1 | 104.500 | 49.800 | 57.900 | 5.450 |
| DetN3K3D2 | 51.900 | 20.450 | 32.250 | 6.050 |
| DetN4K2D2 | 71.350 | 28.500 | 43.750 | 3.100 |
| DetN5K3D1 | 318.500 | 129.500 | 190.000 | 8.500 |

The final `GridK2D2` kernel median is **3.715 ms** (range 3.700–3.930 ms). The 5 ms kernel-median target is **passed**. Individual shared-host observations remain in the record. 5/5 determinant kernel medians are no larger in the final controlled comparison. The full final sweep supplies the shipping fresh-module results.

### Plan selection and reflection

Exploratory single profiles compared recomputing the root plan against passing
its degree vector and digit width and validating them. `GridK2D2` took 3.09 ms
with recomputation and 3.58 ms with the supplied plan; other cases were mixed.
The implementation recomputes the plan, avoiding a larger certificate without
a demonstrated consistent gain. These exploratory observations are not six-pair
estimates; the archive retains every baseline, root, direct, recomputed, and
supplied-plan profile and its source state.

The instrumented `GridK2D2` reflection profile totals about **3.92 ms** across
exclusive nested timers: session/setup/sealing 0.155 ms, left reification
0.984 ms, right reification 0.254 ms, `contextExpr` 0.032 ms, Sym.Arith
canonicalization 1.04 ms, and Sym.Arith instance inference 1.45 ms. Within
instance inference, the recorded calls include `Grind.CommRing` 0.026 ms,
`IsCharP` 0.167 ms, `NatModule` 0.107 ms, `NoNatZeroDivisors` 0.814 ms,
and `Field` 0.218 ms. Repeated `CommRing` queries cost only 0.0044 and
0.0027 ms. The outer Mathlib `CommRing` query costs another 0.098 ms.
These numbers are from the retained `attribution-recomputed/GridK2D2.log`;
the nested instance entries are components, not additional costs to sum.

The session already shares classification and atoms across both sides.
Removing characteristic, zero-divisor, or field classification would alter
Sym.Arith's retained ring classification; it is not an avoidable duplicate
session cost under hex-reflect's contract. Context construction is negligible.
No reflection contract or default tactic chain changes. The remaining roughly
4 ms reflection cost explains why reducing kernel work alone need not put
every small identity below `ring`; the full table reports that outcome without
changing any probe.


## Retained source states

Every completed sweep is retained. Historical `candidate_faster` fields in the older raw records describe paired-margin medians; the verdict above is recomputed from per-arm medians. Source archives preserve the measured closure, including experimental states. The checkout commit is the base revision; recorded working-tree changes are identified by the full source hashes and preserved in those archives.

| Record | Checkout commit | Dirty checkout | Completed arm pairs | Source archive |
| --- | --- | --- | ---: | --- |
| [sweep-direct.json.gz](data/hex-kronecker-mathlib/sweep-direct.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-direct.tar.gz) |
| [sweep-final.json.gz](data/hex-kronecker-mathlib/sweep-final.json.gz) | `3c789a3f6876cfc3cdbaf5bf78a3eee1b2ab5b88` | True | 456 | [sources](data/hex-kronecker-mathlib/source-final.tar.gz) |
| [sweep-integrated.json.gz](data/hex-kronecker-mathlib/sweep-integrated.json.gz) | `658822cad7ea5a54b9398cd67f2a5c00af44f642` | False | 456 | [sources](data/hex-kronecker-mathlib/source-integrated.tar.gz) |
| [sweep-kernel.json.gz](data/hex-kronecker-mathlib/sweep-kernel.json.gz) | `237ad74f70ab885fb4c168a64c948f4d16810196` | True | 456 | [sources](data/hex-kronecker-mathlib/source-kernel.tar.gz) |
| [sweep-optimized.json.gz](data/hex-kronecker-mathlib/sweep-optimized.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-optimized.tar.gz) |
| [sweep-reviewed.json.gz](data/hex-kronecker-mathlib/sweep-reviewed.json.gz) | `dea5fef0ad36b3d0837545d027c76cf575dae642` | False | 456 | [sources](data/hex-kronecker-mathlib/source-reviewed.tar.gz) |
| [sweep-shipping.json.gz](data/hex-kronecker-mathlib/sweep-shipping.json.gz) | `dfc5a2266fda50de82dec94cf07cb6b98a98b07a` | False | 456 | [sources](data/hex-kronecker-mathlib/source-shipping.tar.gz) |
| [sweep-translation.json.gz](data/hex-kronecker-mathlib/sweep-translation.json.gz) | `237ad74f70ab885fb4c168a64c948f4d16810196` | True | 456 | [sources](data/hex-kronecker-mathlib/source-translation.tar.gz) |
| [sweep.json.gz](data/hex-kronecker-mathlib/sweep.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-baseline.tar.gz) |
