# Symbolic determinant proof performance

The symbolic `det` handler and `det%` ship by importing HexPolyDetMathlib.
The symbolic simproc remains opt-in: no default `Hex.norm_det` dispatch is
enabled. This uses the SPEC’s opt-in exception; fallback preserves scope but
does not establish a performance win.

## Historical list-entry packed certificate comparison

The packed arm is available through the opt-in symbolic handler. Its fixed
crossover table contains 50 product keys from 14 witnesses whose packed
fresh-module median is positive and smaller than the term-list median with
six completed paired observations per arm. The selection rule compares the
six-sample medians, not each individual pair. Every product in a witness must
be covered; otherwise the entire witness uses term lists. Kronecker's mode
table selects plain multiplication. No family enters the default simp chain:
full dispatched calls do not establish a family-wide improvement over Mathlib.

The [classification](bench-results/hex-det-packed/classification.json.gz),
[forced comparison](bench-results/hex-det-packed/forced.json.gz),
[fixed crossover keys](bench-results/hex-det-packed/crossover.json), and
[automatic-dispatch comparison](bench-results/hex-det-packed/dispatch.json.gz)
retain the preregistered grid, source hashes, clean-checkout provenance, host
activity, routes, bounds, proof nodes, artifacts and complete compiler output.
Each timing schedule contains 2,064 observations (172 cases, two arms, six
trial-major rounds), with adjacent arms alternating AB/BA on an automatically
leased CPU. Cleanup and proof ceilings are 45 seconds. Classification precedes
timing; forced packing never runs for a known ineligible witness. The dispatch comparison uses the same fixture population as table fitting,
with fresh samples; it is in-sample and does not establish generalisation to
unseen matrices. Product keys are a conservative heuristic, not independent
per-product speed guarantees. The table is
fixed from the forced run before dispatch is measured against unmodified
`norm_det`, followed by the same residual `ring` normalization.

Forced residue term-list samples omit quotient preparation; their archived
`decline_reason` is `residue quotient payload unavailable`, while their
verified certificate route is `term-list`. Bounds recorded without a quotient
payload are preliminary integer-product bounds, not acceptance evidence for
modular packing. They can only cause a decline; acceptance recomputes the full
modular bound with the actual quotient.

Forced outcomes are 1,060 complete, 571 timeout, 426 expected-decline and seven
unexpected-route observations. Those seven are frontend proof-node budget
declines after an eligible product preflight, with successful Mathlib fallback;
they receive no forced-certificate timing or crossover credit. Dispatch has
583 complete and 449 timeout observations; Mathlib has 573 complete, 447 timeout
and 12 failed observations. The failures are its two literal scope cases in
all six rounds. The [route audit](bench-results/hex-det-packed/dispatch-audit.json) verifies all
84 packed observations against the fixed product keys, and checks completed
term-list selections. All 14 representative kernel profiles completed. Of 78 compiled
phase runs, 76 completed and two timed out. No observations are discarded.

The grid preserves all 70 original cases and extends dimensions to 4, 8, 16,
atom counts to 1, 2, 3, 4 and degrees to 2, 4, 8, 16 with the original support
ladder. N-prefixed matrices have correlated row-scaled entries; their timings
are not evidence for arbitrary independent dense matrices. `Independent5`
has 17 independent linear atoms in a dense 4×4 block and its last diagonal.
Its fifth product reports at least 65,537 dense digits (saturated above the
65,536 limit), 917,503 packed bits and the per-atom degrees, then succeeds via
term lists. The two residue cases use primes 3 and 2,147,483,647 with quotient
support three; missing-payload variants exercise term-list fallback.

`N4K2D2S4` falls from 2,385.82 ms for forced term lists to 1,500.38 ms for forced
packing. Its automatic profile has a 681 ms synchronous kernel check.
`Rational4` also selects packing and beats Mathlib in dispatch, but its family
contains losing small cases and an incomplete larger case. The handful of
faster rungs do not define a validated family-wide default regime. Function
and array literals establish additional scope but have no successful Mathlib
comparator. Residue packing loses on these small witnesses, so automatic
selection retains term lists and records `no measured packed regime`.

The preregistered rule has no effect-size floor. `N4K2D8S1` gains only about
0.6% in its six-sample median, which is not evidence of a robust speedup.
Per-winner ranges below expose this uncertainty. Residue quotient preparation
runs within explicit term, coefficient and certificate budgets before selection;
the measured 4×4 costs do not establish its cost at dimensions eight or sixteen.
The product classifier approximates frontend preparation budgets; final proof-node
checks still decide whether the full certificate is affordable.

Family columns below aggregate completed case medians independently; different
completion counts mean they must not be divided to claim a speedup. Median M/D
uses only matched cases with positive six-sample medians in both dispatch arms.
The full ladder retains every incomplete case. The AlgebraicScope control
supplies its algebraic relation explicitly after both tactics decline the zero
target; it is not a certificate or algebraic-number scope win.

Times are medians in milliseconds of six-sample, import-baseline-subtracted
fresh-module medians. Counts show cases with all six successful samples;
incomplete cases remain in the denominator and in the full ladder below.

| Family | Term lists | Packed | Dispatch | Mathlib | Median M/D | Complete cases L/P/D/M | Decision |
|---|---:|---:|---:|---:|---:|---|---|
| dense-row-scaled | 793.99 | 499.86 | 773.59 | 549.42 | 0.884 | 72/59/72/72 of 147 | opt-in |
| rational | 501.03 | 507.54 | 501.05 | 400.14 | 0.976 | 3/3/3/3 of 4 | opt-in |
| singular | 241.04 | 227.83 | 189.51 | 98.63 | 0.823 | 4/4/4/4 of 4 | opt-in |
| closed-algebraic | 194.56 | 202.79 | 199.18 | 77.04 | 0.397 | 4/4/4/4 of 4 | opt-in |
| pivot-swap | 191.71 | 202.95 | 201.68 | 89.84 | 0.445 | 1/1/1/1 of 1 | opt-in |
| structured | 196.11 | 203.21 | 199.65 | 100.70 | 0.504 | 1/1/1/1 of 1 | opt-in |
| literal-function | 198.35 | 223.25 | 202.60 | — | — | 1/1/1/0 of 1 | opt-in |
| literal-array | 197.10 | 199.40 | 203.18 | — | — | 1/1/1/0 of 1 | opt-in |
| closed-algebraic-scope | 110.74 | 99.50 | 100.33 | 98.64 | 0.983 | 1/1/1/1 of 1 | opt-in |
| valuation | 144.58 | 151.45 | 146.10 | 95.79 | 0.760 | 2/2/2/2 of 2 | opt-in |
| independent-atoms | 837.97 | — | 806.64 | 304.22 | 0.377 | 1/0/1/1 of 1 | opt-in |
| block-diagonal | 199.38 | 211.82 | 198.08 | 98.59 | 0.498 | 1/1/1/1 of 1 | opt-in |
| residue-quotient | 200.83 | 290.73 | 194.31 | 100.49 | 0.518 | 2/2/2/2 of 2 | opt-in |
| residue-missing | 200.44 | — | 202.25 | 98.25 | 0.486 | 2/0/2/2 of 2 | opt-in |

Classification: 27 closed-form, 74 eligible, 66 overall-decline, 4 packed-decline, 1 producer-timeout.
The manifest also retains 57 infeasible support requests.

| Case | Classification | Term lists | Packed | Dispatch | Mathlib | Mathlib / dispatch | Observed dispatch |
|---|---|---:|---:|---:|---:|---:|---|
| N2K1D1S1 | closed-form | 89.54 | 98.30 | 101.45 | 95.94 | 0.946 | closed-form-ring |
| N2K1D2S1 | closed-form | 108.45 | 107.64 | 101.49 | 101.30 | 0.998 | closed-form-ring |
| N2K1D4S1 | closed-form | 100.88 | 96.88 | 104.16 | 103.27 | 0.991 | closed-form-ring |
| N2K1D4S4 | closed-form | 275.59 | 280.99 | 266.78 | 201.08 | 0.754 | closed-form-ring |
| N2K2D1S1 | closed-form | 92.23 | 96.73 | 95.24 | 90.80 | 0.953 | closed-form-ring |
| N2K2D2S1 | closed-form | 115.38 | 105.19 | 105.88 | 98.47 | 0.930 | closed-form-ring |
| N2K2D2S4 | closed-form | 189.76 | 188.61 | 199.28 | 197.03 | 0.989 | closed-form-ring |
| N2K2D4S1 | closed-form | 104.57 | 105.19 | 96.35 | 98.88 | 1.026 | closed-form-ring |
| N2K2D4S4 | closed-form | 291.93 | 295.91 | 296.71 | 199.89 | 0.674 | closed-form-ring |
| N2K4D1S1 | closed-form | 94.73 | 94.12 | 86.22 | 90.05 | 1.044 | unobserved |
| N2K4D1S4 | closed-form | 196.92 | 209.56 | 158.47 | 100.98 | 0.637 | closed-form-ring |
| N2K4D2S1 | closed-form | 109.29 | 92.02 | 87.69 | 95.27 | 1.086 | closed-form-ring |
| N2K4D2S4 | closed-form | 204.72 | 203.93 | 212.57 | 199.29 | 0.938 | closed-form-ring |
| N2K4D4S1 | closed-form | 117.40 | 109.31 | 102.81 | 92.41 | 0.899 | closed-form-ring |
| N2K4D4S4 | closed-form | 209.79 | 207.37 | 199.13 | 199.63 | 1.003 | closed-form-ring |
| N2K4D4S16 | closed-form | 1981.49 | 1991.50 | 1990.37 | 2805.10 | 1.409 | closed-form-ring |
| N4K1D1S1 | eligible | 288.92 | 296.89 | 259.96 | 100.62 | 0.387 | term-list |
| N4K1D2S1 | eligible | 456.38 | 497.74 | 426.42 | 294.67 | 0.691 | term-list |
| N4K1D4S1 | eligible | 486.39 | 492.29 | 439.97 | 295.26 | 0.671 | term-list |
| N4K1D4S4 | eligible | 2054.73 | 1664.57 | 1679.27 | 1202.46 | 0.716 | packed/plain |
| N4K2D1S1 | eligible | 286.57 | 297.89 | 253.41 | 105.64 | 0.417 | term-list |
| N4K2D2S1 | eligible | 492.21 | 501.33 | 448.74 | 293.05 | 0.653 | term-list |
| N4K2D2S4 | eligible | 2385.82 | 1500.38 | 1497.36 | 1103.35 | 0.737 | packed/plain |
| N4K2D4S1 | eligible | 485.70 | 498.76 | 452.31 | 292.25 | 0.646 | term-list |
| N4K2D4S4 | eligible | 4202.67 | 2292.82 | 2292.49 | 2101.50 | 0.917 | packed/plain |
| N4K4D1S1 | eligible | 303.43 | 316.83 | 298.34 | 111.50 | 0.374 | term-list |
| N4K4D1S4 | eligible | 1930.89 | 1176.78 | 1115.67 | 700.46 | 0.628 | packed/plain |
| N4K4D2S1 | eligible | 496.82 | 499.86 | 498.90 | 294.00 | 0.589 | term-list |
| N4K4D2S4 | eligible | 4952.69 | 2386.36 | 2413.11 | 2192.17 | 0.908 | packed/plain |
| N4K4D4S1 | eligible | 471.30 | 504.07 | 500.27 | 283.45 | 0.567 | term-list |
| N4K4D4S4 | eligible | 5105.21 | 2529.04 | 2579.20 | 2304.29 | 0.893 | packed/plain |
| N4K4D4S16 | eligible | — | — | — | — | — | unobserved |
| N8K1D1S1 | eligible | 1001.14 | 1122.55 | 998.04 | 704.58 | 0.706 | term-list |
| N8K1D2S1 | eligible | 3222.61 | 3324.93 | 3214.57 | 2700.83 | 0.840 | term-list |
| N8K1D4S1 | eligible | 3216.36 | 3379.61 | 3247.87 | 2701.85 | 0.832 | term-list |
| N8K1D4S4 | eligible | — | — | — | — | — | fallback |
| N8K2D1S1 | eligible | 1077.77 | 1202.91 | 1085.80 | 1106.14 | 1.019 | term-list |
| N8K2D2S1 | eligible | 3291.14 | 3416.79 | 3296.52 | 3101.52 | 0.941 | term-list |
| N8K2D2S4 | eligible | — | — | — | — | — | unobserved |
| N8K2D4S1 | eligible | 3273.69 | 3453.77 | 3439.98 | 3254.99 | 0.946 | term-list |
| N8K2D4S4 | eligible | — | — | — | — | — | unobserved |
| N8K4D1S1 | eligible | 1103.88 | 1304.48 | 1101.60 | 2115.95 | 1.921 | term-list |
| N8K4D1S4 | eligible | — | — | — | — | — | unobserved |
| N8K4D2S1 | overall-decline | 4440.69 | — | 4341.36 | 4154.86 | 0.957 | fallback |
| N8K4D2S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D4S1 | overall-decline | 4561.12 | — | 4262.51 | 4154.46 | 0.975 | fallback |
| N8K4D4S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D4S16 | overall-decline | — | — | — | — | — | unobserved |
| N3K1D1S1 | closed-form | 195.50 | 185.64 | 191.79 | 100.82 | 0.526 | closed-form-ring |
| N3K2D2S4 | closed-form | 586.84 | 590.76 | 549.13 | 398.38 | 0.725 | closed-form-ring |
| N3K4D4S16 | closed-form | — | — | — | — | — | unobserved |
| Rational2 | closed-form | 211.56 | 203.68 | 203.93 | 199.01 | 0.976 | closed-form-ring |
| Singular2 | closed-form | 93.13 | 98.60 | 94.63 | 97.96 | 1.035 | closed-form-ring |
| Algebraic2 | closed-form | 98.86 | 98.96 | 96.15 | 18.76 | 0.195 | closed-form-ring |
| Rational3 | closed-form | 501.03 | 507.54 | 501.05 | 400.14 | 0.799 | closed-form-ring |
| Singular3 | closed-form | 197.21 | 167.04 | 156.43 | 95.45 | 0.610 | closed-form-ring |
| Algebraic3 | closed-form | 108.61 | 110.51 | 102.21 | 55.64 | 0.544 | closed-form-ring |
| Rational4 | eligible | 2499.83 | 1610.07 | 1604.88 | 2208.19 | 1.376 | packed/plain |
| Singular4 | eligible | 284.88 | 288.62 | 222.59 | 99.30 | 0.446 | term-list |
| Algebraic4 | eligible | 280.52 | 295.08 | 296.15 | 98.44 | 0.332 | term-list |
| Rational8 | eligible | — | — | — | — | — | unobserved |
| Singular8 | eligible | 970.79 | 985.45 | 918.82 | 1004.75 | 1.094 | term-list |
| Algebraic8 | eligible | 655.62 | 795.82 | 653.12 | 301.50 | 0.462 | term-list |
| Swaps | eligible | 191.71 | 202.95 | 201.68 | 89.84 | 0.445 | term-list |
| Tridiagonal | eligible | 196.11 | 203.21 | 199.65 | 100.70 | 0.504 | term-list |
| Function4 | eligible | 198.35 | 223.25 | 202.60 | — | — | term-list |
| Array4 | eligible | 197.10 | 199.40 | 203.18 | — | — | term-list |
| AlgebraicScope | closed-form | 110.74 | 99.50 | 100.33 | 98.64 | 0.983 | unobserved |
| Valuation | closed-form | 96.07 | 98.86 | 93.53 | 98.26 | 1.050 | closed-form-ring |
| Valuation4 | eligible | 193.08 | 204.04 | 198.67 | 93.33 | 0.470 | term-list |
| N4K1D8S1 | eligible | 451.38 | 493.47 | 462.49 | 297.50 | 0.643 | term-list |
| N4K1D8S4 | eligible | 2801.96 | 1939.62 | 1920.49 | 1600.16 | 0.833 | packed/plain |
| N4K1D16S1 | eligible | 457.43 | 492.57 | 448.12 | 297.22 | 0.663 | term-list |
| N4K1D16S4 | eligible | 4001.84 | 2402.75 | 2404.42 | 2104.63 | 0.875 | packed/plain |
| N4K1D16S16 | eligible | — | 33001.54 | — | — | — | term-list |
| N4K2D8S1 | eligible | 502.57 | 499.36 | 499.67 | 302.11 | 0.605 | packed/plain |
| N4K2D8S4 | eligible | 4892.50 | 2660.65 | 2683.76 | 2696.86 | 1.005 | packed/plain |
| N4K2D8S16 | eligible | — | — | — | — | — | unobserved |
| N4K2D16S1 | eligible | 473.81 | 494.06 | 484.66 | 294.18 | 0.607 | term-list |
| N4K2D16S4 | eligible | 5351.70 | 3162.28 | 3056.01 | 3011.73 | 0.986 | packed/plain |
| N4K2D16S16 | eligible | — | — | — | — | — | unobserved |
| N4K3D2S1 | eligible | 491.96 | 495.73 | 464.12 | 298.10 | 0.642 | term-list |
| N4K3D2S4 | eligible | 3074.86 | 1612.68 | 1648.91 | 1299.90 | 0.788 | packed/plain |
| N4K3D4S1 | eligible | 490.44 | 492.44 | 493.54 | 300.11 | 0.608 | term-list |
| N4K3D4S4 | eligible | 3305.13 | 1716.64 | 1726.70 | 1364.68 | 0.790 | packed/plain |
| N4K3D4S16 | eligible | — | — | — | — | — | unobserved |
| N4K3D8S1 | eligible | 488.11 | 495.73 | 499.00 | 297.47 | 0.596 | term-list |
| N4K3D8S4 | overall-decline | 1483.84 | — | 1461.30 | 1401.64 | 0.959 | fallback |
| N4K3D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N4K3D16S1 | eligible | 500.36 | 512.21 | 490.11 | 301.05 | 0.614 | term-list |
| N4K3D16S4 | overall-decline | 1405.33 | — | 1413.36 | 1391.28 | 0.984 | fallback |
| N4K3D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N4K4D8S1 | eligible | 495.97 | 507.40 | 520.71 | 294.64 | 0.566 | term-list |
| N4K4D8S4 | overall-decline | 2388.62 | — | 2502.54 | 2450.16 | 0.979 | fallback |
| N4K4D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N4K4D16S1 | packed-decline | 496.24 | — | 499.58 | 296.64 | 0.594 | term-list |
| N4K4D16S4 | overall-decline | 2386.50 | — | 2401.13 | 2300.41 | 0.958 | fallback |
| N4K4D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K1D8S1 | eligible | 3199.69 | 3352.88 | 3214.04 | 2697.37 | 0.839 | term-list |
| N8K1D8S4 | eligible | — | — | — | — | — | unobserved |
| N8K1D16S1 | eligible | 3203.59 | 3396.34 | 3206.20 | 2704.82 | 0.844 | term-list |
| N8K1D16S4 | eligible | — | — | — | — | — | unobserved |
| N8K1D16S16 | eligible | — | — | — | — | — | unobserved |
| N8K2D8S1 | overall-decline | 3352.32 | — | 3290.33 | 3103.14 | 0.943 | fallback |
| N8K2D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K2D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K2D16S1 | overall-decline | 3321.35 | — | 3300.08 | 3101.84 | 0.940 | fallback |
| N8K2D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K2D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D2S1 | eligible | 3291.19 | 3406.09 | 3236.90 | 3596.45 | 1.111 | term-list |
| N8K3D2S4 | eligible | — | — | — | — | — | unobserved |
| N8K3D4S1 | overall-decline | 3810.18 | — | 3798.95 | 3597.19 | 0.947 | fallback |
| N8K3D4S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D4S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D8S1 | overall-decline | 3903.20 | — | 3851.21 | 3639.56 | 0.945 | fallback |
| N8K3D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D16S1 | overall-decline | 3916.00 | — | 3771.33 | 3608.43 | 0.957 | fallback |
| N8K3D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K3D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D8S1 | overall-decline | 4394.64 | — | 4456.98 | 4157.59 | 0.933 | fallback |
| N8K4D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D16S1 | overall-decline | 4452.30 | — | 4491.92 | 4157.92 | 0.926 | fallback |
| N8K4D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N8K4D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K1D2S1 | eligible | — | — | — | — | — | unobserved |
| N16K1D4S1 | eligible | — | — | — | — | — | unobserved |
| N16K1D4S4 | eligible | — | — | — | — | — | unobserved |
| N16K1D8S1 | eligible | — | — | — | — | — | unobserved |
| N16K1D8S4 | eligible | — | — | — | — | — | unobserved |
| N16K1D16S1 | eligible | — | — | — | — | — | unobserved |
| N16K1D16S4 | eligible | — | — | — | — | — | unobserved |
| N16K1D16S16 | producer-timeout | — | — | — | — | — | unobserved |
| N16K2D2S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D2S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D4S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D4S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D8S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D16S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K2D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D2S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D2S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D4S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D4S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D4S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D8S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D16S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K3D16S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D2S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D2S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D4S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D4S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D4S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D8S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D8S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D8S16 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D16S1 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D16S4 | overall-decline | — | — | — | — | — | unobserved |
| N16K4D16S16 | overall-decline | — | — | — | — | — | unobserved |
| Independent5 | packed-decline | 837.97 | — | 806.64 | 304.22 | 0.377 | term-list |
| Block4 | eligible | 199.38 | 211.82 | 198.08 | 98.59 | 0.498 | term-list |
| Residue3 | eligible | 200.34 | 300.53 | 202.22 | 102.20 | 0.505 | term-list |
| Residue3Missing | packed-decline | 200.75 | — | 201.84 | 97.81 | 0.485 | term-list |
| Residue2147483647 | eligible | 201.31 | 280.93 | 186.39 | 98.77 | 0.530 | term-list |
| Residue2147483647Missing | packed-decline | 200.13 | — | 202.65 | 98.69 | 0.487 | term-list |

Expected declines have no forced-packed timing. Closed-form rows are controls on
their unchanged route; their “Lists” and “Packed” column labels denote options,
not certificate execution. Raw records retain timeouts, errors, host context,
compiler output, routes, proof nodes, bounds, and artifact sizes.

### Crossover margins and spread

Median and minimum–maximum of six baseline-subtracted samples, milliseconds.
The preregistered admission rule has no effect-size floor; overlapping ranges
and very small median differences do not establish a robust speed advantage.

| Witness | List median | List range | Packed median | Packed range | Median reduction |
|---|---:|---|---:|---|---:|
| N4K1D4S4 | 2054.73 | 1997.97–2102.90 | 1664.57 | 1606.20–1697.36 | 18.99% |
| N4K2D2S4 | 2385.82 | 2330.29–2424.78 | 1500.38 | 1442.37–1563.23 | 37.11% |
| N4K2D4S4 | 4202.67 | 4093.83–4502.78 | 2292.82 | 2209.39–2301.16 | 45.44% |
| N4K4D1S4 | 1930.89 | 1806.31–1979.92 | 1176.78 | 1119.69–1205.68 | 39.05% |
| N4K4D2S4 | 4952.69 | 4794.16–5109.91 | 2386.36 | 2374.28–2412.49 | 51.82% |
| N4K4D4S4 | 5105.21 | 4899.13–5181.47 | 2529.04 | 2491.56–2647.18 | 50.46% |
| Rational4 | 2499.83 | 2495.97–2657.08 | 1610.07 | 1600.79–1676.82 | 35.59% |
| N4K1D8S4 | 2801.96 | 2705.17–3087.80 | 1939.62 | 1895.82–2002.22 | 30.78% |
| N4K1D16S4 | 4001.84 | 3814.34–4387.24 | 2402.75 | 2393.05–2502.05 | 39.96% |
| N4K2D8S1 | 502.57 | 483.12–515.53 | 499.36 | 480.13–510.13 | 0.64% |
| N4K2D8S4 | 4892.50 | 4805.24–5604.22 | 2660.65 | 2593.68–2802.00 | 45.62% |
| N4K2D16S4 | 5351.70 | 5196.52–5969.89 | 3162.28 | 3023.00–3419.36 | 40.91% |
| N4K3D2S4 | 3074.86 | 2927.73–3498.52 | 1612.68 | 1600.34–1703.63 | 47.55% |
| N4K3D4S4 | 3305.13 | 3206.66–3695.56 | 1716.64 | 1682.29–1884.91 | 48.06% |

### Representative profiles

One automatic-dispatch profile per family; milliseconds, with no baseline subtraction.
Kernel is the synchronous declaration check, including certificate replay and transport.
For the closed-form AlgebraicScope control it is Lean’s final type-checking time.
Identification includes the residue matrix-identification phase. Elaboration includes
the whole module. Nested phases are not additive. A dash means not applicable.

| Case | Conversion | Lists | Quotients | Preflight | Identification | Kernel | Elaboration |
|---|---:|---:|---:|---:|---:|---:|---:|
| N4K2D2S4 | 1.860 | 0.476 | — | 5.240 | 50.900 | 681.000 | 1800.000 |
| Rational4 | 1.960 | 0.481 | — | 5.200 | 60.700 | 831.000 | 1980.000 |
| Singular4 | 1.390 | 0.078 | — | 1.190 | 10.000 | 39.900 | 194.000 |
| Algebraic4 | 1.720 | 0.098 | — | 1.930 | 6.300 | 42.100 | 196.000 |
| Swaps | 1.210 | 0.091 | — | 1.960 | 5.360 | 35.100 | 121.000 |
| Tridiagonal | 1.230 | 0.099 | — | 1.920 | 5.790 | 39.800 | 136.000 |
| Function4 | 1.190 | 0.103 | — | 1.910 | 8.210 | 39.700 | 149.000 |
| Array4 | 1.200 | 0.096 | — | 1.730 | 6.030 | 42.700 | 136.000 |
| AlgebraicScope | — | — | — | — | — | 2.360 | 63.200 |
| Valuation4 | 1.230 | 0.091 | — | 1.930 | 5.050 | 37.100 | 125.000 |
| Independent5 | 3.300 | 0.418 | — | 3.260 | 18.600 | 477.000 | 724.000 |
| Block4 | 1.250 | 0.099 | — | 1.720 | 5.670 | 40.100 | 133.000 |
| Residue3 | 24.700 | — | 0.222 | 1.660 | 21.570 | 28.400 | 144.000 |
| Residue3Missing | 24.700 | — | — | 1.560 | 21.640 | 28.200 | 142.000 |

### Compiled phases

Milliseconds for representative witnesses, with the large-prime case included.
Checker columns are medians of six adjacent AB/BA measurements; other phases
are single observations. Packing repeats each prefix and includes target and quotient lists.
All selected products use plain multiplication, so outer signed packing is inapplicable.

| Case | p | Quotient support | Quotients | Preflight | Packing | Multiplication | List Bool | Packed Bool |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| N4K2D2S4 | — | 0 | — | 1.6107 | 0.1013 | 0.0097 | 0.1174 | 0.5860 |
| Rational4 | — | 0 | — | 1.5894 | 0.1015 | 0.0096 | 0.1166 | 0.5872 |
| Singular4 | — | 0 | — | 0.8106 | 0.0037 | 0.0028 | 0.0013 | 0.1203 |
| Algebraic4 | — | 0 | — | 1.5645 | 0.0044 | 0.0028 | 0.0025 | 0.4616 |
| Swaps | — | 0 | — | 1.6535 | 0.0045 | 0.0033 | 0.0021 | 0.4630 |
| Tridiagonal | — | 0 | — | 1.6552 | 0.0044 | 0.0029 | 0.0031 | 0.4613 |
| Function4 | — | 0 | — | 1.6706 | 0.0044 | 0.0028 | 0.0037 | 0.4605 |
| Array4 | — | 0 | — | 1.6634 | 0.0045 | 0.0031 | 0.0031 | 0.4643 |
| Valuation4 | — | 0 | — | 1.6396 | 0.0043 | 0.0029 | 0.0021 | 0.4624 |
| Independent5 | — | 0 | — | 1.8002 | — | — | 0.0365 | — |
| Block4 | — | 0 | — | 1.5888 | 0.0046 | 0.0033 | 0.0027 | 0.4605 |
| Residue3 | 3 | 3 | 0.0072 | 1.5666 | 0.0058 | 0.0037 | 0.0029 | 0.4688 |
| Residue3Missing | 3 | 0 | — | 1.7103 | — | — | 0.0024 | — |
| Residue2147483647 | 2147483647 | 3 | 0.0102 | 2.9138 | 0.0128 | 0.0059 | 0.0032 | 1.6205 |
| Residue2147483647Missing | 2147483647 | 0 | — | 1.6140 | — | — | 0.0024 | — |

### Composed Mathlib fallback

Full dispatched invocations that emit a fallback event, including work before delegation.
Each median requires six completed samples; incomplete cases remain visible.

| Case | Dispatch ms | Mathlib ms | Completed D/M |
|---|---:|---:|---|
| N4K3D16S4 | 1413.36 | 1391.28 | 6/6 |
| N4K3D8S4 | 1461.30 | 1401.64 | 6/6 |
| N4K4D16S4 | 2401.13 | 2300.41 | 6/6 |
| N4K4D8S4 | 2502.54 | 2450.16 | 6/6 |
| N8K1D4S4 | — | — | 3/5 |
| N8K2D16S1 | 3300.08 | 3101.84 | 6/6 |
| N8K2D8S1 | 3290.33 | 3103.14 | 6/6 |
| N8K3D16S1 | 3771.33 | 3608.43 | 6/6 |
| N8K3D4S1 | 3798.95 | 3597.19 | 6/6 |
| N8K3D8S1 | 3851.21 | 3639.56 | 6/6 |
| N8K4D16S1 | 4491.92 | 4157.92 | 6/6 |
| N8K4D2S1 | 4341.36 | 4154.86 | 6/6 |
| N8K4D4S1 | 4262.51 | 4154.46 | 6/6 |
| N8K4D8S1 | 4456.98 | 4157.59 | 6/6 |

The [fresh residue proof sweep](bench-results/hex-det-packed/residue-list.json.gz)
completes all 18 proof builds and adjacent baselines with clean provenance and
only `propext`, `Classical.choice`, and `Quot.sound`. The standalone packed
kernel tests cover both branches, empty matrices, malformed payloads, budget
boundaries and corrupted quotients, including the characteristic-two carry
example. Closed forms at dimensions at most three are unchanged.

Diagnostic records in the same directory are explicitly excluded from table
selection: `forced-invalid-residue.json.gz` is incomplete and lacks provider
evidence for the large-prime fixture; `classification-invalid-inputs.json.gz`
has malformed driver inputs; `classification-before-provider-evidence.json.gz`
has obsolete source metadata; `timer-before-fix.json.gz` lacks the evaluation
barrier required by the compiled timer; `residue-list-diagnostic.json.gz` has
dirty-checkout provenance. They remain available for inspection and are not
combined with the complete accepted schedules.

## Term-list comparison record

This retained comparison uses the earlier dense monomial-count preflight.
The packed comparison above uses the minimum of that count and the sparse
`2 * B^2` intermediate bound, with `B ≤ n! * s^n` for entry support `s`.
It therefore measures some certificates that the earlier estimator declined;
the two records are not a paired before/after comparison.

The fixed schedule completed all 840 arm samples (70 cases × two arms × six
trials) and 14 attribution profiles. All failures and timeouts remain in the
[raw record](bench-results/hex-poly-det-mathlib-sweep.json.gz).
Candidate outcomes: `{'Mathlib': {'complete': 354, 'timeout': 54, 'failed': 12}, 'Hex': {'complete': 364, 'timeout': 56}}`.
Source commit: `87ced16f06c0d3f2f91987d874ce31691c0bbb1f`. Sources remained
unchanged; the initial worktree and dependency checkouts were clean. The data
record every imported repository source hash, the manifest, toolchain, host
observations, CPU accounting, compiler output, axiom audits and artifact sizes.

## Residue term-list certificates

The [focused residue record](bench-results/hex-det-residue-probes.json.gz)
measures the integer and residue term-list arms beside one another using
`scripts/bench/det_residue_sweep.py`. The 4×4 two-variable cases have the same
block-diagonal matrix and formal determinant `(x² - 1) * (y² - 1)` over `Int`
and `ZMod 3`. The third case retains the nonzero formal polynomial `X³ − X`
in a 4×4 determinant over `MvPolynomial (Fin 1) (ZMod 3)`.

Each probe has six trials and an immediately adjacent import-only baseline.
The fixed trial-major schedule rotates cases and alternates AB/BA order.
All 18 measured proof builds and 18 baselines completed, all 45-second ceilings
passed, and every theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`. Route traces require the integer certificate for `Integer4` and
the residue certificate for the other two; a closed formula or fallback cannot
satisfy the measurement check.

Source commit: `6c803e229b1e9a65275714eaf1e279e1a04a9f06`. Host: `chungus2`, AMD EPYC 9455 48-Core Processor,
leanprover/lean4:v4.34.0. One Lean worker used automatically leased logical CPU
50. Concurrent compilation and shared-host activity are retained as context.
There were no discarded samples, retries, or provenance exceptions.

The kernel column is the median synchronous `det.symbolic.kernel` declaration
check, including certificate replay and semantic transport. Nested profiling is
disabled within that check. Full-build columns include all elaboration and proof
construction. These absolute observations do not establish a performance win
or change default simproc dispatch.

`Residue.identify` identifies entries through structural list access, avoiding
definitional reduction of the evaluated residue polynomial matrix. The compiler
output and `phase_profile_ms` retain separate matrix-identification, entry-replay,
producer, certificate, and transport timings. The term-form regression test runs
under Lean's default heartbeat limit.

The [earlier revision](bench-results/hex-det-residue-initial.json.gz) retains
all 18 completed measurements with the generic identification theorem
(source `a73104154c6d77e8af813ade9cd7993e0ffa2596`). Its residue full-build
medians were 8.593 s and 8.774 s. These two revision sweeps are separate
shared-host observations, not an interleaved before/after comparison.

| Probe | Full build median/max (s) | Kernel check median (ms) | .olean bytes |
|---|---:|---:|---:|
| Integer4 | 4.217 / 8.290 | 61.200 | 40400 |
| Residue4 | 4.083 / 7.204 | 59.750 | 48072 |
| ResidueFrobenius | 3.675 / 4.769 | 30.700 | 46928 |

Matrix-identification medians for the residue probes: Residue4 21.800 ms, ResidueFrobenius 19.600 ms.

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
explicitly. It is not an algebraic-number scope win. The canonical Nat residue
term-list arm has kernel tests and the focused measurements above. Integer
transport remains sound over arbitrary commutative rings; composite-characteristic
requests use the universal integer certificate when residue capability conditions
fail, preserving the existing certificate scope.

The [earlier certificate experiment](hex-symbolic-det-experiment.md) retains
all 732 samples and ten profiles from the implementation before relocation
and the small closed-form route. The diagnostic pilot is also retained.
Those datasets are separate experiments, not adjacent paired before/after evidence.
Compiled producer/checker observations are in
[the executable report](hex-poly-det-performance.md).
