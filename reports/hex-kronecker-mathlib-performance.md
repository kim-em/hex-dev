# HexKroneckerMathlib performance

## Result

26/46 paired comparisons have a median-margin magnitude no
larger than their median absolute deviation and are **unresolved at this
measurement resolution**. The numerical median comparison and this description
of variation are reported separately; no sample is discarded or replaced.

The complete sweep contains 23 accepted identities and 7
preflight declines. 14/23 accepted cases have a smaller per-arm
baseline-subtracted median than both `ring` and `grobner`. The comparison across
all accepted cases is **not passed**.
The absolute candidate ceilings are **passed**.
The [opt-in shipping condition](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#fresh-module-comparisons-and-shipping-bar)
requires the complete family table and passing absolute ceilings. Its status
is **passed**. No default tactic chain changes.

Of the seven grid cases that lost to `ring` in the shipping table, 4/7 are now at or below its median. 3/5 determinant medians are no larger than the shipping values. The numerical optimization bar is **not passed**. These are fresh-module comparisons; controlled kernel attribution is reported separately. The previously losing small cases still above `ring` are `GridK1D2`, `GridK3D2`, `GridK4D2`.

The smallest case's controlled kernel median is 3.715 ms (all six samples
below 5 ms), and all five determinant kernel medians improve. Reflection
still costs about 4 ms in the instrumented smallest-case session, principally
Sym.Arith canonicalization and instance classification. That remaining work
can keep the total tactic cost above `ring` even after the kernel improvement;
the fresh-module measurements below determine the numerical bar separately.

## Protocol and provenance

The measured checkout is `4b59351263e48e34946af4ce3c757d303408ee3a`, using
`leanprover/lean4:v4.34.0`. The record includes the pinned dependency
revisions and SHA-256 hashes of the complete measured source closure.
The Kronecker implementation, proof probes, and sweep runner match those
measured sources. The measured Lake file is preserved in the source archive.

[Raw samples, source hashes, artifacts, and profiles](data/hex-kronecker-mathlib/sweep-translation-repeat.json.gz) retain every
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

After 30/46 first-sweep comparisons were unresolved, the identical registered six-pair protocol was repeated once. Local builds and other measurements from this work finished before the repeat; the CPU was automatically leased without an idle-host criterion. The repeat recorded median 6 and maximum 182 concurrent Lake/Lean processes. Both complete sweeps are retained and compared below; no observation is filtered and the numerical bar is unchanged.


## reflected-identities and determinant-identities

| Case | D | N | Kronecker ms | ring ms | grobner ms | K/ring | K/grobner | Ceiling |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| GridK1D2 | 3 | 14 | 79.230 | 67.941 | 62.213 | 1.166 | 1.274 | pass |
| GridK1D4 | 5 | 34 | 51.245 | 88.912 | 33.737 | 0.576 | 1.519 | pass |
| GridK1D8 | 9 | 98 | 48.813 | 77.555 | 13.743 | 0.629 | 3.552 | pass |
| GridK1D16 | 17 | 322 | 86.700 | 25.445 | 319.768 | 3.407 | 0.271 | pass |
| GridK2D2 | 9 | 44 | 54.872 | 82.237 | 19.141 | 0.667 | 2.867 | pass |
| GridK2D4 | 25 | 174 | 42.467 | 68.743 | 89.420 | 0.618 | 0.475 | pass |
| GridK2D8 | 81 | 890 | 82.031 | 75.059 | 66.476 | 1.093 | 1.234 | pass |
| GridK2D16 | 289 | 5490 | -51.941 | 242.683 | 102.959 | — | — | pass |
| GridK3D2 | 27 | 161 | 79.304 | 0.698 | 22.822 | 113.583 | 3.475 | pass |
| GridK3D4 | 125 | 1124 | 39.180 | 154.925 | 111.713 | 0.253 | 0.351 | pass |
| GridK3D8 | 729 | 10934 | 90.180 | 383.011 | 312.236 | 0.235 | 0.289 | pass |
| GridK3D16 | 4913 | 137563 | 170.660 | 1437.011 | 3366.664 | 0.119 | 0.051 | pass |
| GridK4D2 | 81 | 566 | 438.122 | 90.446 | -158.360 | 4.844 | — | pass |
| GridK4D4 | 625 | 6874 | 141.930 | 126.556 | 232.466 | 1.121 | 0.611 | pass |
| GridK4D8 | 6561 | 124658 | 303.793 | 2903.742 | 3930.848 | 0.105 | 0.077 | pass |
| GridK6D2 | 729 | 5831 | 26.580 | 223.472 | 119.990 | 0.119 | 0.222 | pass |
| GridK6D4 | 15625 | 203124 | 186.543 | 834.609 | 1752.868 | 0.224 | 0.106 | pass |
| GridK8D2 | 6561 | 59048 | 53.741 | 74.219 | 217.859 | 0.724 | 0.247 | pass |
| DetN3K2D1 | 16 | 176 | 75.745 | 98.489 | 105.248 | 0.769 | 0.720 | pass |
| DetN4K3D1 | 125 | 2125 | 150.697 | 690.684 | 748.984 | 0.218 | 0.201 | pass |
| DetN3K3D2 | 343 | 4116 | 135.755 | 137.549 | 240.285 | 0.987 | 0.565 | pass |
| DetN4K2D2 | 81 | 1296 | 43.385 | 640.220 | 367.367 | 0.068 | 0.118 | pass |
| DetN5K3D1 | 216 | 4968 | 199.278 | 12622.661 | 7935.570 | 0.016 | 0.025 | pass |

## Per-case before/after

Before values come from the [retained shipping sweep](data/hex-kronecker-mathlib/sweep-shipping.json.gz); after values come from the complete new sweep above. These historical wall-time columns use different execution segments and are not adjacent before/after pairs. Controlled kernel attribution is reported separately. Every value is retained, including negative baseline-subtracted medians.

| Case | Before K ms | After K ms | Before ring ms | After ring ms | Before grobner ms | After grobner ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| GridK1D2 | 77.508 | 79.230 | 47.322 | 67.941 | 79.267 | 62.213 |
| GridK1D4 | 76.461 | 51.245 | 73.423 | 88.912 | 90.167 | 33.737 |
| GridK1D8 | 83.617 | 48.813 | 77.616 | 77.555 | 81.752 | 13.743 |
| GridK1D16 | 86.323 | 86.700 | 88.315 | 25.445 | 140.768 | 319.768 |
| GridK2D2 | 35.474 | 54.872 | 4.705 | 82.237 | 82.358 | 19.141 |
| GridK2D4 | 81.034 | 42.467 | 83.305 | 68.743 | 86.879 | 89.420 |
| GridK2D8 | 85.279 | 82.031 | 86.260 | 75.059 | 95.422 | 66.476 |
| GridK2D16 | 86.199 | -51.941 | 110.181 | 242.683 | 175.130 | 102.959 |
| GridK3D2 | 93.528 | 79.304 | 74.798 | 0.698 | 85.212 | 22.822 |
| GridK3D4 | 84.871 | 39.180 | 97.783 | 154.925 | 87.148 | 111.713 |
| GridK3D8 | 101.741 | 90.180 | 194.479 | 383.011 | 320.780 | 312.236 |
| GridK3D16 | 275.352 | 170.660 | 1392.564 | 1437.011 | 2704.733 | 3366.664 |
| GridK4D2 | 100.410 | 438.122 | 94.206 | 90.446 | 97.439 | -158.360 |
| GridK4D4 | 93.211 | 141.930 | 113.287 | 126.556 | 183.785 | 232.466 |
| GridK4D8 | 285.440 | 303.793 | 894.794 | 2903.742 | 2452.135 | 3930.848 |
| GridK6D2 | 97.084 | 26.580 | 92.294 | 223.472 | 107.098 | 119.990 |
| GridK6D4 | 186.995 | 186.543 | 295.516 | 834.609 | 1293.175 | 1752.868 |
| GridK8D2 | 97.890 | 53.741 | 100.023 | 74.219 | 122.009 | 217.859 |
| DetN3K2D1 | 46.952 | 75.745 | 102.599 | 98.489 | 110.265 | 105.248 |
| DetN4K3D1 | 156.469 | 150.697 | 662.976 | 690.684 | 685.631 | 748.984 |
| DetN3K3D2 | 90.542 | 135.755 | 183.618 | 137.549 | 192.447 | 240.285 |
| DetN4K2D2 | 106.877 | 43.385 | 387.077 | 640.220 | 307.353 | 367.367 |
| DetN5K3D1 | 279.116 | 199.278 | 9210.743 | 12622.661 | 6701.527 | 7935.570 |

## Single unchanged repeat

The [first complete sweep](data/hex-kronecker-mathlib/sweep-translation.json.gz) and the repeat have identical measured source hashes. Each column uses all six per-arm baseline-subtracted observations from its own cohort. These cohorts are not adjacent before/after pairs. Negative medians are retained.

The first cohort put 4/7 previously losing small cases at or below `ring` and 1/5 determinant medians at or below the historical shipping values. Its numerical bar and the repeat's numerical bar are kept distinct.

| Case | First K ms | Repeat K ms | First ring ms | Repeat ring ms | First grobner ms | Repeat grobner ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| GridK1D2 | 56.614 | 79.230 | 91.401 | 67.941 | 84.032 | 62.213 |
| GridK1D4 | 38.117 | 51.245 | 156.907 | 88.912 | 96.305 | 33.737 |
| GridK1D8 | 122.751 | 48.813 | 58.769 | 77.555 | 83.510 | 13.743 |
| GridK1D16 | 210.310 | 86.700 | 67.542 | 25.445 | 93.969 | 319.768 |
| GridK2D2 | 60.329 | 54.872 | 45.293 | 82.237 | 7.464 | 19.141 |
| GridK2D4 | 12.839 | 42.467 | 31.096 | 68.743 | 77.891 | 89.420 |
| GridK2D8 | 33.795 | 82.031 | 93.273 | 75.059 | 128.587 | 66.476 |
| GridK2D16 | -261.058 | -51.941 | 298.547 | 242.683 | 158.620 | 102.959 |
| GridK3D2 | 42.896 | 79.304 | 237.485 | 0.698 | 32.825 | 22.822 |
| GridK3D4 | 261.600 | 39.180 | -66.889 | 154.925 | -20.988 | 111.713 |
| GridK3D8 | 40.548 | 90.180 | 146.797 | 383.011 | 546.110 | 312.236 |
| GridK3D16 | 278.760 | 170.660 | 3234.030 | 1437.011 | 4887.749 | 3366.664 |
| GridK4D2 | 757.947 | 438.122 | 153.258 | 90.446 | -126.878 | -158.360 |
| GridK4D4 | 131.443 | 141.930 | 257.721 | 126.556 | 425.958 | 232.466 |
| GridK4D8 | 171.904 | 303.793 | 1610.389 | 2903.742 | 4477.787 | 3930.848 |
| GridK6D2 | -51.122 | 26.580 | 74.249 | 223.472 | -85.398 | 119.990 |
| GridK6D4 | 360.024 | 186.543 | 478.487 | 834.609 | 2128.336 | 1752.868 |
| GridK8D2 | -58.112 | 53.741 | 93.207 | 74.219 | 163.884 | 217.859 |
| DetN3K2D1 | 48.877 | 75.745 | 337.032 | 98.489 | 316.537 | 105.248 |
| DetN4K3D1 | 10.468 | 150.697 | 917.588 | 690.684 | 736.116 | 748.984 |
| DetN3K3D2 | 271.796 | 135.755 | 268.518 | 137.549 | 289.564 | 240.285 |
| DetN4K2D2 | 408.356 | 43.385 | 560.107 | 640.220 | 549.567 | 367.367 |
| DetN5K3D1 | 357.454 | 199.278 | 17372.332 | 12622.661 | 8824.961 | 7935.570 |

| Case | First decline ms | Repeat decline ms |
| --- | ---: | ---: |
| GridK4D16 | -230.023 | 2.388 |
| GridK6D8 | 93.993 | -285.332 |
| GridK6D16 | 140.452 | 28.573 |
| GridK8D4 | 266.600 | 37.118 |
| GridK8D8 | 634.134 | 4.637 |
| GridK8D16 | -38.302 | -199.226 |
| IndependentN5 | -22.580 | 43.283 |

## Measured regimes

The determinant-shaped group wins 5/5 comparisons against both references. The accepted multivariate expansion grid with degree at least four wins 7/9. These are the measured winning regimes; the full table also shows individual wins outside them.

The losing cases are `GridK1D2`, `GridK1D4`, `GridK1D8`, `GridK1D16`, `GridK2D2`, `GridK2D8`, `GridK3D2`, `GridK4D2`, `GridK4D4`. The detailed tables retain their numerical ordering and measurement spread. The resolution table below distinguishes the numerical ordering from shared-host variation. No dispatch threshold or default-chain entry is inferred from small unresolved differences.

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
| GridK4D16 | 65537 | 2923234 | 7.021 | 2.388 |
| GridK6D8 | 65537 | 12223142 | 44.509 | -285.332 |
| GridK6D16 | 65537 | 16777217 | 1.648 | 28.573 |
| GridK8D4 | 65537 | 5859374 | 3.340 | 37.118 |
| GridK8D8 | 65537 | 16777217 | 1.824 | 4.637 |
| GridK8D16 | 65537 | 16777217 | 10.342 | -199.226 |
| IndependentN5 | 65537 | 16777217 | 76.336 | 43.283 |

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
| GridK1D2 | -13.904 | 47.538 | -28.241 | 350.892 | unresolved: ring, grobner |
| GridK1D4 | 1.048 | 37.938 | 23.529 | 85.471 | unresolved: ring, grobner |
| GridK1D8 | 2.188 | 382.594 | -44.175 | 215.890 | unresolved: ring, grobner |
| GridK1D16 | -43.044 | 123.873 | 138.509 | 169.346 | unresolved: ring, grobner |
| GridK2D2 | 1.259 | 16.758 | -0.929 | 20.923 | unresolved: ring, grobner |
| GridK2D4 | 10.796 | 43.355 | 42.855 | 36.733 | unresolved: ring |
| GridK2D8 | 40.501 | 63.503 | -23.676 | 74.035 | unresolved: ring, grobner |
| GridK2D16 | 294.624 | 243.760 | 153.777 | 62.725 | margin exceeds MAD |
| GridK3D2 | -24.568 | 54.033 | -39.491 | 49.523 | unresolved: ring, grobner |
| GridK3D4 | 12.877 | 50.133 | 66.323 | 154.130 | unresolved: ring, grobner |
| GridK3D8 | 134.224 | 157.415 | 286.066 | 38.482 | unresolved: ring |
| GridK3D16 | 1289.785 | 76.392 | 3189.928 | 616.229 | margin exceeds MAD |
| GridK4D2 | -32.922 | 350.218 | -596.482 | 486.401 | unresolved: ring |
| GridK4D4 | -382.416 | 288.332 | 107.559 | 70.078 | margin exceeds MAD |
| GridK4D8 | 2355.676 | 1141.162 | 3627.054 | 1536.209 | margin exceeds MAD |
| GridK6D2 | 196.892 | 345.972 | 172.537 | 521.023 | unresolved: ring, grobner |
| GridK6D4 | 403.781 | 250.709 | 1327.441 | 170.803 | margin exceeds MAD |
| GridK8D2 | 61.216 | 66.391 | 340.577 | 201.512 | unresolved: ring |
| DetN3K2D1 | 29.211 | 32.497 | 65.029 | 47.507 | unresolved: ring |
| DetN4K3D1 | 416.726 | 163.592 | 617.804 | 262.834 | margin exceeds MAD |
| DetN3K3D2 | 5.274 | 78.189 | 133.596 | 72.894 | unresolved: ring |
| DetN4K2D2 | 394.103 | 640.050 | 305.184 | 486.373 | unresolved: ring, grobner |
| DetN5K3D1 | 12424.813 | 3014.414 | 7296.462 | 783.856 | margin exceeds MAD |

## Paired signs

Each sign records one completed reference-minus-candidate margin in trial order. Positive favors Kronecker, negative favors the reference, and zero is a tie. Small baseline-subtracted differences may be dominated by shared-host variation; all signs and negative baseline differences are retained.

| Case | vs ring | vs grobner |
| --- | --- | --- |
| GridK1D2 | − + − − + − | − + − − + − |
| GridK1D4 | − + − − + + | − − − + + + |
| GridK1D8 | − − + − + + | − − − − + + |
| GridK1D16 | − + − − + + | + + + − + + |
| GridK2D2 | + − − + + − | + + − + − − |
| GridK2D4 | − − + + + + | − − + + + + |
| GridK2D8 | + − − + + + | − + − + − − |
| GridK2D16 | + + + + + + | + + + + + + |
| GridK3D2 | + + − − − − | − + − − + − |
| GridK3D4 | + + + + − − | + + + + − − |
| GridK3D8 | + + + − + + | + + + − + + |
| GridK3D16 | + + + + + + | + + + + + + |
| GridK4D2 | + + − − + − | − − − − − − |
| GridK4D4 | − − + + − − | + + + + + − |
| GridK4D8 | + + + + + + | + + + + + + |
| GridK6D2 | − − + + + − | − + + + − + |
| GridK6D4 | + + + + + + | + + + + + + |
| GridK8D2 | + + + + + − | + + + − + + |
| DetN3K2D1 | + + + + − + | + + + + − + |
| DetN4K3D1 | + + + − + + | + + + + + + |
| DetN3K3D2 | + + + − − + | + − + + + + |
| DetN4K2D2 | + + + − + + | + + + − + + |
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
| [sweep-translation-repeat.json.gz](data/hex-kronecker-mathlib/sweep-translation-repeat.json.gz) | `4b59351263e48e34946af4ce3c757d303408ee3a` | True | 456 | [sources](data/hex-kronecker-mathlib/source-translation-repeat.tar.gz) |
| [sweep-translation.json.gz](data/hex-kronecker-mathlib/sweep-translation.json.gz) | `237ad74f70ab885fb4c168a64c948f4d16810196` | True | 456 | [sources](data/hex-kronecker-mathlib/source-translation.tar.gz) |
| [sweep.json.gz](data/hex-kronecker-mathlib/sweep.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-baseline.tar.gz) |
