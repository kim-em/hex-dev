# Symbolic determinant proof performance

The symbolic `det` handler and `det%` ship by importing HexPolyDetMathlib.
The symbolic simproc remains opt-in: no default `Hex.norm_det` dispatch is
enabled. This uses the SPEC’s opt-in exception; fallback preserves scope but
does not establish a performance win.

The fixed schedule completed all 840 arm samples (70 cases × two arms × six
trials) and 14 attribution profiles. All failures and timeouts remain in the
[raw record](bench-results/hex-poly-det-mathlib-sweep.json.gz).
Candidate outcomes: `{'Mathlib': {'complete': 354, 'timeout': 54, 'failed': 12}, 'Hex': {'complete': 364, 'timeout': 56}}`.
Source commit: `87ced16f06c0d3f2f91987d874ce31691c0bbb1f`. Sources remained
unchanged; the initial worktree and dependency checkouts were clean. The data
record every imported repository source hash, the manifest, toolchain, host
observations, CPU accounting, compiler output, axiom audits and artifact sizes.

## Method

The unmodified pinned Mathlib `norm_det`, followed by residual `ring`, is
compared with the complete Hex `det` invocation on identical targets. Every
proof build has its own adjacent import-only baseline. The six trial-major
rounds rotate cases and alternate both arm and baseline order. Only the
measured module artifacts are cleared. Both baseline and proof builds have
the preregistered 45-second cap. The fixed schedule continues after failures.
Runs use one Lean worker on automatically leased CPU 12 of chungus2
(AMD EPYC 9455, Lean 4.34.0-rc2). Host activity is recorded without filtering
or waiting for a quiet CPU. No completed sample is discarded or replaced.

Medians below subtract the adjacent import-only baseline from each proof
sample before taking the median. All six samples must complete. A ratio is
shown only when both medians are positive; near-zero or negative differences
are retained as observations, not interpreted as speedups. Tracing is enabled
on Hex probes and matched Hex baselines; its cost is part of this comparison.

### Closed-form ring solver comparison

The exact core invocation which enables only the commutative-ring solver is
`grobner`. In the pinned Lean source its elaborator starts from
`Grind.GrobnerConfig`; that structure extends `Grind.NoopConfig`, whose
E-matching, splitting, linear arithmetic, AC, order and model-based combination
facilities are disabled, and re-enables only `ring := true`. Thus the comparison
uses `ring` against `grobner`, not unrestricted `grind`.

The focused comparison takes the polynomial equality left after the `n ≤ 3`
closed determinant formula as its target, without repeating formula construction.
Integer, rational-coefficient and
fixed-numeral-power families each have `n = 1, 2, 3` representatives. Six
fresh-module rounds rotate the cases, keep each pair adjacent, alternate
`ring`/`grobner` as AB/BA, pin one Lean worker to automatically leased CPU 92,
and retain all completed samples. The complete record is
[hex-poly-det-ring-solver-cd82ae658bde-chungus2.json.gz](bench-results/hex-poly-det-ring-solver-cd82ae658bde-chungus2.json.gz),
measured on chungus2 at source commit
`cd82ae658bde34b97dd42ba20189a7d93a90573c`; provenance is clean and all 108
builds completed. Wall columns are raw, import-dominated fresh-module medians;
their spread exceeds the normalizer-scale difference and they are not used in
the switching decision. Kernel and
elaboration columns are separate medians of Lean's cumulative `type checking`
and `elaboration` profiler counters. All table values are milliseconds. These are whole-module
counters, including statement elaboration and first-use tactic initialization,
not isolated production `det.small.ring` spans. No common baseline is subtracted.
The raw record's source commit and hashes pin the measured harness and theorem
statements. The table renderer reads those retained samples; capability evidence
is recorded separately, without modifying the timing data.

| Family / n | ring wall | grobner wall | ring kernel | grobner kernel | ring elaboration | grobner elaboration |
|---|---:|---:|---:|---:|---:|---:|
| integer / 1 | 9607.60 | 9053.48 | 1.825 | 1.495 | 75.950 | 66.100 |
| integer / 2 | 10623.27 | 11417.72 | 12.400 | 26.850 | 54.950 | 84.750 |
| integer / 3 | 7780.82 | 7126.02 | 4.160 | 13.335 | 45.600 | 33.450 |
| rational / 1 | 7690.19 | 6531.40 | 3.380 | 24.350 | 56.750 | 53.650 |
| rational / 2 | 6815.29 | 5880.75 | 13.200 | 11.600 | 128.500 | 29.350 |
| rational / 3 | 6983.31 | 9328.02 | 12.300 | 80.150 | 62.700 | 141.500 |
| fixed powers / 1 | 9708.69 | 8330.89 | 26.100 | 25.100 | 61.750 | 54.250 |
| fixed powers / 2 | 8001.62 | 9162.98 | 5.650 | 21.950 | 59.750 | 45.600 |
| fixed powers / 3 | 9158.66 | 10470.75 | 8.080 | 7.900 | 92.150 | 46.850 |

The kernel result splits: `grobner` has the smaller median on four of nine
targets, while `ring` has the smaller median on five, including the rational
`n = 3` target and two of the three integer targets. It therefore
does not meet the all-families switching condition, and the production
closed-form route remains on `ring`.

Two compile-time capability probes delimit this result. With
`h : α ^ 2 = 2` in the local context, `grobner` closes
`α * α - 1 * 2 = 0`, which `ring` alone does not close. This intersects the
SPEC's stated limitation on using local atom relations, but no production path
or advertised scope is enabled by that observation. Conversely, `grobner` does not close
`(x ^ k) * (x ^ k) = x ^ (2 * k)` for variable `k`: those powers are distinct
atoms outside the fixed-numeral exponent fragment (`Grind.CommRing.Power.k : Nat`).
`ring` closes that target, so substituting `grobner` would also lose an existing
variable-exponent capability. Both boundaries are guarded in compile-time probes
which CI builds explicitly without building the full symbolic performance ladder.
Their fresh builds, complete compiler output, exact axiom audits and source
fingerprints are retained in
[hex-poly-det-ring-capabilities-f3626cc1352e-chungus2.json](bench-results/hex-poly-det-ring-capabilities-f3626cc1352e-chungus2.json)
at clean source commit `f3626cc1352e58e149ee79fa4e4224278d0b2e00`.
`scripts/bench/det_ring_solver_sweep.py --table <timing-record>` regenerates the
table verbatim; `--capabilities <output.json>` records fresh capability builds
without rerunning the timing comparison.

The main 2/4/8 ladder has 48 feasible cases and 33 infeasible support requests.
Three 3×3 cases measure the closed-form route. The remaining cases cover
rational, singular, closed-algebraic, pivot-swap, structured, function/array
literal and specialization surfaces. N-prefixed cases scale rows of seeded
integer matrices by sparse polynomials: entries within one row are correlated.
The exceptional N2K4D1S1 case uses four independent entries. These cases do
not model independent random dense polynomial matrices. Executable benchmark
matrices use different terms and integer rows even when parameter labels agree.

Hex modules enable route tracing. Retained events identify attempted routes,
successful routes and fallback reasons. Some high-degree, four-variable 8×8 cases are declined by the
conservative support preflight before elimination. Their measured times include
the complete fallback. An absence of trace output after a timeout is reported
as unobserved, not inferred to be a certificate attempt or success.

## Fresh-module medians

The N-prefixed rows in this table use the correlated row-scaled family above
(except N2K4D1S1). Times are milliseconds; M/H is Mathlib divided by Hex.

| Case | Mathlib ms | Hex ms | M/H | Completed M/H | Hex route |
|---|---:|---:|---:|---:|---|
| N2K1D1S1 | 41.33 | 89.80 | 0.460 | 6/6 | closed-form |
| N2K1D2S1 | 3.04 | 110.29 | 0.028 | 6/6 | closed-form |
| N2K1D4S1 | 74.68 | 102.87 | 0.726 | 6/6 | closed-form |
| N2K1D4S4 | 187.01 | 256.81 | 0.728 | 6/6 | closed-form |
| N2K2D1S1 | 90.42 | 103.44 | 0.874 | 6/6 | closed-form |
| N2K2D2S1 | 92.18 | 106.16 | 0.868 | 6/6 | closed-form |
| N2K2D2S4 | 112.02 | 188.86 | 0.593 | 6/6 | closed-form |
| N2K2D4S1 | 89.59 | 100.17 | 0.894 | 6/6 | closed-form |
| N2K2D4S4 | 198.88 | 286.75 | 0.694 | 6/6 | closed-form |
| N2K4D1S1 | 44.69 | 65.44 | 0.683 | 6/6 | unobserved |
| N2K4D1S4 | 101.81 | 157.70 | 0.646 | 6/6 | closed-form |
| N2K4D2S1 | 74.55 | 98.74 | 0.755 | 6/6 | closed-form |
| N2K4D2S4 | 190.64 | 197.10 | 0.967 | 6/6 | closed-form |
| N2K4D4S1 | 92.16 | 104.74 | 0.880 | 6/6 | closed-form |
| N2K4D4S4 | 188.84 | 197.71 | 0.955 | 6/6 | closed-form |
| N2K4D4S16 | 2788.30 | 1895.34 | 1.471 | 6/6 | closed-form |
| N4K1D1S1 | 101.54 | 297.30 | 0.342 | 6/6 | certificate |
| N4K1D2S1 | 279.68 | 412.29 | 0.678 | 6/6 | certificate |
| N4K1D4S1 | 240.79 | 406.35 | 0.593 | 6/6 | certificate |
| N4K1D4S4 | 1191.72 | 2005.28 | 0.594 | 6/6 | certificate |
| N4K2D1S1 | 103.55 | 293.17 | 0.353 | 6/6 | certificate |
| N4K2D2S1 | 291.93 | 481.72 | 0.606 | 6/6 | certificate |
| N4K2D2S4 | 1121.42 | 2293.34 | 0.489 | 6/6 | certificate |
| N4K2D4S1 | 293.59 | 426.24 | 0.689 | 6/6 | certificate |
| N4K2D4S4 | 2100.48 | 4077.43 | 0.515 | 6/6 | certificate |
| N4K4D1S1 | 150.07 | 288.65 | 0.520 | 6/6 | certificate |
| N4K4D1S4 | 692.92 | 1800.87 | 0.385 | 6/6 | certificate |
| N4K4D2S1 | 288.94 | 486.34 | 0.594 | 6/6 | certificate |
| N4K4D2S4 | 2098.92 | 4668.53 | 0.450 | 6/6 | certificate |
| N4K4D4S1 | 287.76 | 495.23 | 0.581 | 6/6 | certificate |
| N4K4D4S4 | 2256.02 | 4804.17 | 0.470 | 6/6 | certificate |
| N4K4D4S16 | — | — | — | 0/0 | unobserved |
| N8K1D1S1 | 690.61 | 999.66 | 0.691 | 6/6 | certificate |
| N8K1D2S1 | 2693.22 | 3196.05 | 0.843 | 6/6 | certificate |
| N8K1D4S1 | 2699.85 | 3146.19 | 0.858 | 6/6 | certificate |
| N8K1D4S4 | 36220.70 | — | — | 6/4 | fallback |
| N8K2D1S1 | 1074.74 | 1007.27 | 1.067 | 6/6 | certificate |
| N8K2D2S1 | 3049.37 | 3190.55 | 0.956 | 6/6 | certificate |
| N8K2D2S4 | — | — | — | 0/0 | unobserved |
| N8K2D4S1 | 2993.95 | 3207.48 | 0.933 | 6/6 | certificate |
| N8K2D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D1S1 | 2066.74 | 1097.77 | 1.883 | 6/6 | certificate |
| N8K4D1S4 | — | — | — | 0/0 | unobserved |
| N8K4D2S1 | 4090.38 | 4253.46 | 0.962 | 6/6 | fallback |
| N8K4D2S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S1 | 4010.25 | 4254.07 | 0.943 | 6/6 | fallback |
| N8K4D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S16 | — | — | — | 0/0 | unobserved |
| N3K1D1S1 | 86.70 | 194.35 | 0.446 | 6/6 | closed-form |
| N3K2D2S4 | 392.63 | 595.00 | 0.660 | 6/6 | closed-form |
| N3K4D4S16 | — | — | — | 0/0 | unobserved |
| Rational2 | 175.98 | 207.96 | 0.846 | 6/6 | closed-form |
| Singular2 | 65.41 | 84.25 | 0.776 | 6/6 | closed-form |
| Algebraic2 | 2.02 | 83.58 | 0.024 | 6/6 | closed-form |
| Rational3 | 400.42 | 504.31 | 0.794 | 6/6 | closed-form |
| Singular3 | -0.62 | 191.08 | — | 6/6 | closed-form |
| Algebraic3 | 1.46 | 106.08 | 0.014 | 6/6 | closed-form |
| Rational4 | 2191.95 | 2395.61 | 0.915 | 6/6 | certificate |
| Singular4 | 103.02 | 259.09 | 0.398 | 6/6 | certificate |
| Algebraic4 | 104.85 | 293.94 | 0.357 | 6/6 | certificate |
| Rational8 | — | — | — | 0/0 | unobserved |
| Singular8 | 985.34 | 909.28 | 1.084 | 6/6 | certificate |
| Algebraic8 | 214.23 | 651.98 | 0.329 | 6/6 | certificate |
| Swaps | 90.46 | 195.88 | 0.462 | 6/6 | certificate |
| Tridiagonal | 91.97 | 197.33 | 0.466 | 6/6 | certificate |
| Function4 | — | 199.96 | — | 0/6 | certificate |
| Array4 | — | 190.34 | — | 0/6 | certificate |
| AlgebraicScope | 97.61 | 105.21 | 0.928 | 6/6 | unobserved |
| Valuation | 38.42 | 86.67 | 0.443 | 6/6 | closed-form |
| Valuation4 | 47.03 | 197.61 | 0.238 | 6/6 | certificate |

Complete paired medians are available for 57 of 69 shared cases;
4 have a smaller positive Hex median. The all-shared-cases-faster
predicate is `false`. This does not clear the strict shipping bar.

The unmodified Mathlib calls in `Function4` and `Array4` fail because
`simp only [norm_det]` makes no progress on those literal forms. The matched
imports are present. Their failed builds have no accepted theorem or median;
the Hex certificate route closes those targets.

Per-case faster medians are observations for these inputs; they do not enable
a default size regime. Capped or failing cases remain obligations outside any
performance claim. The complete fallback invocation is measured on declines.

## Attribution and proof size

These are separate fresh-module profiler builds, not samples added to the
median table. Values are Lean’s cumulative profiler counters in milliseconds.
Reification, conversion, producer, list conversion, compiled self-check, entry
identification, auxiliary kernel wrapper, total type checking and elaboration
are retained separately. Nested spans are not summed: in particular the
producer invokes list conversion and the compiled self-check callback. The
auxiliary kernel wrapper counter alone is not the entire proof-checking cost.
Small closed-form cases have no polynomial producer or list checker; their
formula and `ring` counters are reported separately in the raw profile.

| Case | State | Reify | Convert | Producer | Lists | Self-check | Identify | Aux kernel | Type check | Elaboration |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| N2K1D1S1 | complete | — | — | — | — | — | — | — | 2.98 | 34.7 |
| N3K2D2S4 | complete | — | — | — | — | — | — | — | 42.1 | 448 |
| N4K2D2S4 | complete | 5.65 | 1.73 | 91.4 | 0.53 | 6.61 | 51.6 | 24.1 | 1.32e+03 | 2.44e+03 |
| N8K4D4S16 | timeout | — | — | — | — | — | — | — | — | — |
| Rational4 | complete | 2.73 | 4.79 | 91.1 | 0.469 | 6.62 | 59.5 | 32.3 | 1.48e+03 | 2.63e+03 |
| Singular4 | complete | 1.34 | 1.22 | 0.8 | 0.0733 | 0.109 | 9.77 | 3.27 | 37.9 | 182 |
| Algebraic4 | complete | 3.01 | 1.18 | 0.936 | 0.0935 | 0.153 | 6.26 | 3.72 | 40.5 | 206 |
| Swaps | complete | 1.5 | 1.08 | 0.763 | 0.0854 | 0.139 | 5.33 | 2.35 | 33.2 | 119 |
| Tridiagonal | complete | 1.42 | 1.09 | 0.973 | 0.0941 | 0.163 | 5.8 | 2.76 | 38.5 | 132 |
| Valuation | complete | — | — | — | — | — | — | — | 2.45 | 29 |
| Valuation4 | complete | 1.29 | 1.07 | 0.839 | 0.0857 | 0.136 | 4.86 | 2.06 | 35.1 | 116 |
| Function4 | complete | 1.17 | 1.07 | 1.12 | 0.0972 | 0.179 | 7.97 | 2.36 | 36.9 | 143 |
| Array4 | complete | 1.46 | 1.1 | 0.964 | 0.0931 | 0.165 | 5.63 | 2.92 | 43.8 | 129 |
| AlgebraicScope | complete | — | — | — | — | — | — | — | 2.35 | 62.4 |

| Small case | Formula ms | Aux kernel ms | Ring ms |
|---|---:|---:|---:|
| N2K1D1S1 | 0.906 | — | 0.0289 |
| N3K2D2S4 | 7.33 | — | 0.0367 |
| Valuation | 0.588 | — | 0.0306 |
| AlgebraicScope | 0.92 | — | 0.0309 |

| Case | Certificate nodes | Ring nodes | Max minor support | Max minor degree | Coefficient bits | Hex .olean bytes |
|---|---:|---:|---:|---:|---:|---:|
| N2K1D1S1 | — | 50033 | — | — | — | 58680 |
| N3K2D2S4 | — | ≥1000001 | — | — | — | 1029088 |
| N4K2D2S4 | 246797 | — | 36 | 8 | 14 | 90632 |
| N8K4D4S16 | — | — | — | — | — | — |
| Rational4 | 395845 | — | 36 | 8 | 14 | 132784 |
| Singular4 | 118025 | — | 1 | 3 | 7 | 42136 |
| Algebraic4 | 153091 | — | 3 | 4 | 3 | 44776 |
| Swaps | 104917 | — | 2 | 4 | 1 | 38208 |
| Tridiagonal | 104927 | — | 3 | 4 | 2 | 39632 |
| Valuation | — | 19029 | — | — | — | 44864 |
| Valuation4 | 100201 | — | 2 | 4 | 1 | 42112 |
| Function4 | 111717 | — | 2 | 1 | 3 | 31008 |
| Array4 | 104147 | — | 3 | 4 | 2 | 37160 |
| AlgebraicScope | — | — | — | — | — | 29720 |

Node counting stops at 1,000,001; that saturated value is a lower bound,
not an exact size. Missing route events and small auxiliary-kernel counters
remain missing in the report rather than being inferred from the implementation.

The closed-algebraic shared targets treat α as an independent atom. The
separate `AlgebraicScope` probe confirms that neither tactic uses α² = 2
to close the zero target; its final theorem then supplies that relation
explicitly. It is not an algebraic-number scope win. Reduced-Nat residue
kernel tests remain non-tests pending #10257. Integer transport remains sound
over arbitrary commutative rings; characteristic-aware conversion mismatches
decline and preserve fallback.

The [earlier certificate experiment](hex-symbolic-det-experiment.md) retains
all 732 samples and ten profiles from the implementation before relocation
and the small closed-form route. The diagnostic pilot is also retained.
Those datasets are separate experiments, not adjacent paired before/after evidence.
Compiled producer/checker observations are in
[the executable report](hex-poly-det-performance.md).
