# HexHensel Performance Report

The lift-schedule remediation was measured at revision
`4b1c96d04f366771a569257e197a5f6efa4e1656` on `chungus2` (AMD EPYC
9455, Linux x86-64). Each affected rung has three independent outer trials.
The six unaffected headline results remain from the clean nine-target export
at revision `0b95505b7c926911a9f487bac56676a8c7da48f6`.

## Bench targets

The nine Phase-4 performance registrations are:

| registration | model | family |
|---|---|---|
| `runModPChecksum` | `n` | bridge operations |
| `runLiftToZChecksum` | `n` | bridge operations |
| `runReduceModPowChecksum` | `n` | bridge operations |
| `runLinearHenselStepChecksum` | `n²` | linear Hensel |
| `runHenselLiftChecksum` | `n²k` at `k = 64` | linear Hensel |
| `runQuadraticHenselStepChecksum` | `n²` | quadratic Hensel |
| `runPolyProductChecksum` | `n²` | multifactor lifting |
| `runMultifactorLiftChecksum` | `n²k` at `k = 64` | multifactor lifting |
| `runMultifactorLiftQuadraticChecksum` | `n² log k` at `k = 64` | multifactor lifting |

The retained-fold and product-tree registrations are branch-attribution
comparisons for the ordered-product dispatcher. They do not add operations to
the Phase-4 API coverage above. The fixed FLINT endpoints are comparator and
protocol anchors; they make no complexity claim and have no mode.

## Verdicts

All nine Phase-4 registrations use mode 1, two-sided parametric. Their models
are derived from the operations performed on the registered families rather
than selected from the measurements. The lift models are unchanged by this
remediation: fixing `k = 64` turns `n²k` and `n² log k` into controlled degree
ladders while retaining the largest precision of the former mixed schedule.

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| `runModPChecksum` | `n` | 131072 | 9.601 ms | consistent |
| `runLiftToZChecksum` | `n` | 131072 | 2.582 ms | consistent |
| `runReduceModPowChecksum` | `n` | 131072 | 733.006 µs | consistent |
| `runLinearHenselStepChecksum` | `n²` | 512 | 15.568 ms | consistent |
| `runHenselLiftChecksum` | `n²k` | `(400,64)` | 1.213 s | consistent |
| `runQuadraticHenselStepChecksum` | `n²` | 512 | 8.481 ms | consistent |
| `runPolyProductChecksum` | `n²` | 1024 | 161.314 ms | consistent |
| `runMultifactorLiftChecksum` | `n²k` | `(400,64)` | 1.208 s | consistent |
| `runMultifactorLiftQuadraticChecksum` | `n² log k` | `(400,64)` | 173.486 ms | consistent |

After the leading warmup rung, the normalized-cost intervals are
`118.472–123.960`, `117.461–121.917`, and `180.461–201.098`, respectively.
The evaluated encoded-parameter range is shorter than the harness's minimum
log-range for a residual regression, so the mode-1 verdict uses its declared
tight ratio criterion. All 24 measurements for each registration completed;
the largest outer-trial spreads were 7.85%, 1.08%, and 6.21%.

Raw lift export:
`reports/bench-results/hex-hensel-4b1c96d0-lift-schedules-chungus2.json`
(SHA-256
`d810e0c2809e2c0b0e7865de33e4d69d2aa4de9a60fafbc70db94f775bc5a3ff`).

The covered input families are `bridge-operations`, `linear-hensel`,
`quadratic-hensel`, and `multifactor-lifting`.

## Diagnosis

The three failures were family and schedule failures, not evidence for fitted
models.

- The old encoded ladder changed precision several times while holding degree
  fixed. Since lean-bench regresses residuals against the scalar encoding
  `n * 1000 + k`, those precision changes had almost no horizontal separation
  and did not form a valid scaling experiment.
- The old iterated-linear fixture kept one factor linear. That did not exercise
  the intended degree-growing correction products. The replacement uses dense
  monic `g` and `q` and sets `h = gq + 1`; the explicit Bezout relation
  `h - qg = 1` guarantees coprimeness while both factor degrees grow.
- The direct and linear-multifactor paths share the corrected fixture and the
  fixed-precision degree ladder. Their nearly identical normalized intervals
  agree with `multifactorLift` delegating the two-factor case to the direct
  linear lift.
- The quadratic path already passed the former mixed ladder on current main,
  after the exact-exponent and canonical-output improvements. Its old
  high-precision discontinuity was therefore implementation history, not a
  remaining defect. The controlled ladder still removes the encoding
  ambiguity and passes the independently derived model.

The degree domain `(144..400)` stays within one implementation regime. Above
it, the optimized high-degree multifactor path intentionally changes the
finite ladder's constant; mixing that transition into the same scalar
experiment recreates the original schedule error.

## Profile

Sampling profiles cover the largest completed rung `(400,64)`. All three have
two timed regions, zero off-thread samples, and passing confidence and ±5 ms
sensitivity diagnostics.

| Target | retained samples | classified leaf cost | principal inclusive attribution |
|---|---:|---:|---|
| iterated linear | 3,957 | 99.29% | `linearHenselStep` 99.55%; `DensePoly.mulImpl` 90.45% |
| linear multifactor | 6,190 | 99.74% | `henselLift` 99.47%; `DensePoly.mulImpl` 90.45% |
| quadratic multifactor | 2,958 | 99.53% | `henselLiftFactorsImpl` 95.91%; `liftExactImpl` 67.99%; `divModMonicModSquareImpl` 67.61% |

The linear leaf classifications are dominated by allocation (47.97%/52.18%),
Lean runtime (25.27%/22.65%), own code (17.72%/16.27%), and GMP
(8.34%/8.64%). The quadratic profile is dominated by allocation (52.06%),
Lean runtime (25.25%), and GMP (19.61%); its bignum quadratic step accounts
for 45.67% inclusively. These profiles attribute the declared quadratic
degree work to the executable phases that actually dominate it.

## Comparator Ratios

The declared informational comparator is
`FLINT nmod_poly_hensel_lift_* via python-flint`. The five retained
python-flint exports under
`reports/bench-results/hex-hensel-*-flint-5c371a5a-chungus2.json` record the
comparator protocol. python-flint does not expose native
`nmod_poly_hensel_lift_*`; the iterated comparator is an `fmpz_poly`
emulation, so these ratios remain informational rather than a native-FLINT
performance claim. All 71 Hex and comparator registrations pass `verify` with
python-flint present.

## Concerns

None.
