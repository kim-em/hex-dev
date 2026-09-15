# HexKroneckerMathlib performance

## Result

The complete sweep contains 23 accepted identities and 7
preflight declines. 16/23 accepted cases have a smaller per-arm
baseline-subtracted median than both `ring` and `grobner`. The comparison across
all accepted cases is **not passed**.
The absolute candidate ceilings are **passed**.
The [opt-in shipping condition](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#fresh-module-comparisons-and-shipping-bar)
requires the complete family table and passing absolute ceilings. Its status
is **passed**. No default tactic chain changes.

20/46 paired comparisons have a median-margin magnitude no
larger than their median absolute deviation and are **unresolved at this
measurement resolution**. The numerical median comparison and this description
of variation are reported separately; no sample is discarded or replaced.

## Protocol and provenance

The measured checkout is `dfc5a2266fda50de82dec94cf07cb6b98a98b07a`, using
`leanprover/lean4:v4.34.0`. The record includes the pinned dependency
revisions and SHA-256 hashes of the complete measured source closure.
The Kronecker implementation, proof probes, and sweep runner match those
measured sources. The current Lake registration also includes unrelated
primality and determinantal-ideal targets; the measured Lake file is preserved
in the source archive. The updated `HexMatrix/Lists.lean` adds `rowLists` and
three observation lemmas, none used by Kronecker; its existing declarations
are unchanged. `HexReflect/Session.lean` adds an unused `proofNodeCount`, and
`HexReflect/Budget.lean` exposes the unchanged default budget definition.
These four files are the only source-hash differences from the measurement;
none changes the operations executed by the measured tactic.

[Raw samples, source hashes, artifacts, and profiles](data/hex-kronecker-mathlib/sweep-shipping.json.gz) retain every
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
original runner hashes, CPU and environment. This is not an unchanged rerun.

The preregistered ceilings are 30 seconds per accepted grid case, 60 seconds
per accepted determinant case, and a 180-second cleanup timeout. Ceilings
apply to raw candidate wall time, including imports. The table reports
baseline-subtracted per-arm medians in milliseconds. Ratios are Kronecker
divided by the reference median and are shown only when both are positive.
The numerical comparison uses these per-arm medians; paired-margin signs
remain supplementary evidence. Losing cases stay in the table and do not
prevent explicitly opt-in shipping under the SPEC's shared exception.

## reflected-identities and determinant-identities

| Case | D | N | Kronecker ms | ring ms | grobner ms | K/ring | K/grobner | Ceiling |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| GridK1D2 | 3 | 14 | 77.508 | 47.322 | 79.267 | 1.638 | 0.978 | pass |
| GridK1D4 | 5 | 34 | 76.461 | 73.423 | 90.167 | 1.041 | 0.848 | pass |
| GridK1D8 | 9 | 98 | 83.617 | 77.616 | 81.752 | 1.077 | 1.023 | pass |
| GridK1D16 | 17 | 322 | 86.323 | 88.315 | 140.768 | 0.977 | 0.613 | pass |
| GridK2D2 | 9 | 44 | 35.474 | 4.705 | 82.358 | 7.539 | 0.431 | pass |
| GridK2D4 | 25 | 174 | 81.034 | 83.305 | 86.879 | 0.973 | 0.933 | pass |
| GridK2D8 | 81 | 890 | 85.279 | 86.260 | 95.422 | 0.989 | 0.894 | pass |
| GridK2D16 | 289 | 5490 | 86.199 | 110.181 | 175.130 | 0.782 | 0.492 | pass |
| GridK3D2 | 27 | 161 | 93.528 | 74.798 | 85.212 | 1.250 | 1.098 | pass |
| GridK3D4 | 125 | 1124 | 84.871 | 97.783 | 87.148 | 0.868 | 0.974 | pass |
| GridK3D8 | 729 | 10934 | 101.741 | 194.479 | 320.780 | 0.523 | 0.317 | pass |
| GridK3D16 | 4913 | 137563 | 275.352 | 1392.564 | 2704.733 | 0.198 | 0.102 | pass |
| GridK4D2 | 81 | 566 | 100.410 | 94.206 | 97.439 | 1.066 | 1.030 | pass |
| GridK4D4 | 625 | 6874 | 93.211 | 113.287 | 183.785 | 0.823 | 0.507 | pass |
| GridK4D8 | 6561 | 124658 | 285.440 | 894.794 | 2452.135 | 0.319 | 0.116 | pass |
| GridK6D2 | 729 | 5831 | 97.084 | 92.294 | 107.098 | 1.052 | 0.906 | pass |
| GridK6D4 | 15625 | 203124 | 186.995 | 295.516 | 1293.175 | 0.633 | 0.145 | pass |
| GridK8D2 | 6561 | 59048 | 97.890 | 100.023 | 122.009 | 0.979 | 0.802 | pass |
| DetN3K2D1 | 16 | 176 | 46.952 | 102.599 | 110.265 | 0.458 | 0.426 | pass |
| DetN4K3D1 | 125 | 2125 | 156.469 | 662.976 | 685.631 | 0.236 | 0.228 | pass |
| DetN3K3D2 | 343 | 4116 | 90.542 | 183.618 | 192.447 | 0.493 | 0.470 | pass |
| DetN4K2D2 | 81 | 1296 | 106.877 | 387.077 | 307.353 | 0.276 | 0.348 | pass |
| DetN5K3D1 | 216 | 4968 | 279.116 | 9210.743 | 6701.527 | 0.030 | 0.042 | pass |

## Measured regimes

The determinant-shaped group wins 5/5 comparisons against both references. The accepted multivariate expansion grid with degree at least four wins 9/9. These are the measured winning regimes; the full table also shows individual wins outside them.

The losing cases are `GridK1D2`, `GridK1D4`, `GridK1D8`, `GridK2D2`, `GridK3D2`, `GridK4D2`, `GridK6D2`. They lie in the small-grid regime, where fixed invocation work is a large fraction of tactic cost. The resolution table below distinguishes the numerical ordering from shared-host variation. No dispatch threshold or default-chain entry is inferred from small unresolved differences.

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

| Case | Dense digits (saturated) | Packed bits (saturated) | Decline median ms |
| --- | ---: | ---: | ---: |
| GridK4D16 | 65537 | 2923234 | 7.021 |
| GridK6D8 | 65537 | 12223142 | 44.509 |
| GridK6D16 | 65537 | 16777217 | 1.648 |
| GridK8D4 | 65537 | 5859374 | 3.340 |
| GridK8D8 | 65537 | 16777217 | 1.824 |
| GridK8D16 | 65537 | 16777217 | 10.342 |
| IndependentN5 | 65537 | 16777217 | 76.336 |

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
| GridK1D2 | 13784 | 39728 | 20352 |
| GridK1D4 | 14800 | 65104 | 22840 |
| GridK1D8 | 16832 | 130584 | 27816 |
| GridK1D16 | 20896 | 321136 | 37768 |
| GridK2D2 | 14592 | 44112 | 20232 |
| GridK2D4 | 15992 | 79592 | 23168 |
| GridK2D8 | 18792 | 175360 | 28848 |
| GridK2D16 | 24392 | 461512 | 40208 |
| GridK3D2 | 16232 | 60688 | 26008 |
| GridK3D4 | 20032 | 175872 | 36544 |
| GridK3D8 | 31976 | 886352 | 69856 |
| GridK3D16 | 73776 | 8376040 | 188456 |
| GridK4D2 | 18128 | 83504 | 30336 |
| GridK4D4 | 26568 | 377336 | 56680 |
| GridK4D8 | 66960 | 4733048 | 187104 |
| GridK6D2 | 22688 | 146576 | 41656 |
| GridK6D4 | 50800 | 1441848 | 141152 |
| GridK8D2 | 28272 | 238032 | 56144 |
| DetN3K2D1 | 24440 | 355984 | 63032 |
| DetN4K3D1 | 45480 | 3903152 | 173336 |
| DetN3K3D2 | 29352 | 543184 | 86088 |
| DetN4K2D2 | 34360 | 1767544 | 138480 |
| DetN5K3D1 | 85960 | 32957584 | 450080 |

## Comparison resolution

MAD is the median absolute deviation of the six paired margins from their median. An ordering is marked unresolved when the magnitude of that median does not exceed its MAD. This descriptive comparison does not add a sampling filter or change the preregistered numerical bar. Small tactic costs can be obscured by variation in the adjacent import-dominated builds.

| Case | Margin vs ring ms | MAD ms | Margin vs grobner ms | MAD ms | Resolution |
| --- | ---: | ---: | ---: | ---: | --- |
| GridK1D2 | -25.936 | 30.910 | 8.276 | 12.861 | unresolved: ring, grobner |
| GridK1D4 | -0.275 | 5.274 | 9.887 | 13.985 | unresolved: ring, grobner |
| GridK1D8 | -8.080 | 8.371 | 5.589 | 15.413 | unresolved: ring, grobner |
| GridK1D16 | -2.662 | 5.175 | 56.438 | 40.448 | unresolved: ring |
| GridK2D2 | -0.452 | 7.355 | 3.376 | 32.209 | unresolved: ring, grobner |
| GridK2D4 | -8.987 | 48.219 | -3.378 | 23.036 | unresolved: ring, grobner |
| GridK2D8 | 4.356 | 8.632 | 17.382 | 39.811 | unresolved: ring, grobner |
| GridK2D16 | 22.645 | 17.410 | 95.609 | 10.692 | margin exceeds MAD |
| GridK3D2 | -17.625 | 19.489 | -8.066 | 6.278 | unresolved: ring |
| GridK3D4 | 3.889 | 44.884 | 3.345 | 13.758 | unresolved: ring, grobner |
| GridK3D8 | 87.620 | 22.097 | 210.668 | 21.011 | margin exceeds MAD |
| GridK3D16 | 1109.241 | 12.442 | 2434.982 | 9.838 | margin exceeds MAD |
| GridK4D2 | -7.420 | 14.454 | -6.693 | 3.780 | unresolved: ring |
| GridK4D4 | 22.127 | 16.536 | 91.213 | 13.963 | margin exceeds MAD |
| GridK4D8 | 612.902 | 8.756 | 2182.997 | 31.867 | margin exceeds MAD |
| GridK6D2 | -6.867 | 7.966 | 5.331 | 14.550 | unresolved: ring, grobner |
| GridK6D4 | 112.349 | 27.194 | 1103.433 | 31.239 | margin exceeds MAD |
| GridK8D2 | -1.649 | 9.953 | 26.343 | 14.497 | unresolved: ring |
| DetN3K2D1 | 23.522 | 14.700 | 64.770 | 38.274 | margin exceeds MAD |
| DetN4K3D1 | 501.458 | 19.155 | 499.066 | 16.365 | margin exceeds MAD |
| DetN3K3D2 | 101.342 | 13.209 | 106.642 | 2.958 | margin exceeds MAD |
| DetN4K2D2 | 287.476 | 4.283 | 200.868 | 9.879 | margin exceeds MAD |
| DetN5K3D1 | 8934.980 | 82.750 | 6413.116 | 28.916 | margin exceeds MAD |

## Paired signs

Each sign records one completed reference-minus-candidate margin in trial order. Positive favors Kronecker, negative favors the reference, and zero is a tie. Small baseline-subtracted differences may be dominated by shared-host variation; all signs and negative baseline differences are retained.

| Case | vs ring | vs grobner |
| --- | --- | --- |
| GridK1D2 | − + + − + − | + + + − + − |
| GridK1D4 | + + − − + − | − + − + + + |
| GridK1D8 | − − − + − + | − + + + − + |
| GridK1D16 | − + + − − − | + + + + + + |
| GridK2D2 | + + − + − − | − + + + − − |
| GridK2D4 | − + − − + + | − + + − − − |
| GridK2D8 | − + + + + − | + + + − + − |
| GridK2D16 | + + + + + + | + + + + + + |
| GridK3D2 | − + − − − − | − + + − − − |
| GridK3D4 | + − + − + + | + + + − + + |
| GridK3D8 | + + + + + + | + + + + + + |
| GridK3D16 | + + + + + + | + + + + + + |
| GridK4D2 | − − − + − + | + − − − − + |
| GridK4D4 | + − + + + + | + − + + + + |
| GridK4D8 | + + + + + + | + + + + + + |
| GridK6D2 | − + − − + − | + + − − + + |
| GridK6D4 | + + + + + + | + + + + + + |
| GridK8D2 | − + + + − − | + + + + + + |
| DetN3K2D1 | + + + + + + | + + + + − + |
| DetN4K3D1 | + + + + + + | + + + + + + |
| DetN3K3D2 | + + + + + + | + + + + + + |
| DetN4K2D2 | + + + + + + | + + + + + + |
| DetN5K3D1 | + + + + + + | + + + + + + |

## Kernel-only profiles

The accepted-family profiles replay `checkExprEq = true` through
`decide +kernel`, using the quoted trees from their shared construction
modules. They exclude reflection, proof production, and the `fromGrind`
translation reduced by the actual tactic certificate. The decline-family
profile evaluates only preflight: it intentionally performs no packed
certificate check. Raw profiler output is retained in the record.

| Family | Representative | Kernel type checking ms | Fresh module wall ms | Axioms |
| --- | --- | ---: | ---: | --- |
| reflected-identities | GridK3D8 | 38.600 | 2621.220 | propext |
| determinant-identities | DetN4K3D1 | 48.300 | 2632.388 | propext |
| dense-box-declines | IndependentN5 | 223.000 | 2920.961 | propext |

[Kernel profiles and their source hashes](data/hex-kronecker-mathlib/kernel-profiles-shipping.json.gz) record the dedicated fresh profile runs. The kernel column is Lean’s aggregate type-checking timer. The separate fresh-module wall time includes imports and compilation. The decline profile proves the preflight result using `decide +kernel`; it performs no packed evaluation. Earlier compiled-guard diagnostics remain in the historical sweep records and are not used as kernel profiles.

The Mathlib-free [computational report](hex-kronecker-performance.md) supplies
complexity evidence in the packed bit size, operation profiles and the full
plain/signed product comparison. These proof probes measure total tactic
cost, including reflection, emitted literals, and synchronous kernel checking.

## Retained source states

Every completed sweep is retained. Historical `candidate_faster` fields in the older raw records describe paired-margin medians; the verdict above is recomputed from per-arm medians. Source archives preserve the measured closure, including experimental states. The checkout commit is the base revision; recorded working-tree changes are identified by the full source hashes and preserved in those archives.

| Record | Checkout commit | Dirty checkout | Completed arm pairs | Source archive |
| --- | --- | --- | ---: | --- |
| [sweep-direct.json.gz](data/hex-kronecker-mathlib/sweep-direct.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-direct.tar.gz) |
| [sweep-final.json.gz](data/hex-kronecker-mathlib/sweep-final.json.gz) | `3c789a3f6876cfc3cdbaf5bf78a3eee1b2ab5b88` | True | 456 | [sources](data/hex-kronecker-mathlib/source-final.tar.gz) |
| [sweep-integrated.json.gz](data/hex-kronecker-mathlib/sweep-integrated.json.gz) | `658822cad7ea5a54b9398cd67f2a5c00af44f642` | False | 456 | [sources](data/hex-kronecker-mathlib/source-integrated.tar.gz) |
| [sweep-optimized.json.gz](data/hex-kronecker-mathlib/sweep-optimized.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-optimized.tar.gz) |
| [sweep-reviewed.json.gz](data/hex-kronecker-mathlib/sweep-reviewed.json.gz) | `dea5fef0ad36b3d0837545d027c76cf575dae642` | False | 456 | [sources](data/hex-kronecker-mathlib/source-reviewed.tar.gz) |
| [sweep-shipping.json.gz](data/hex-kronecker-mathlib/sweep-shipping.json.gz) | `dfc5a2266fda50de82dec94cf07cb6b98a98b07a` | False | 456 | [sources](data/hex-kronecker-mathlib/source-shipping.tar.gz) |
| [sweep.json.gz](data/hex-kronecker-mathlib/sweep.json.gz) | `b6cc624916d948df1c1f6e57d385109cb8ad5bea` | True | 456 | [sources](data/hex-kronecker-mathlib/source-baseline.tar.gz) |
