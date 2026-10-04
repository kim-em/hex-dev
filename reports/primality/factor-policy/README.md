# Pocklington construction: native factor-search experiments

A bounded native Hex policy matched PrimeCert+SymPy's **two successes out of
eight 512-bit subjects**, under a common 180-second process limit. On the two
common successes, four adjacent alternating comparisons gave generation-time
medians of **68.4 vs 134.6 seconds** and **3.37 vs 9.08 seconds**. Both systems'
generated certificates passed Lean kernel replay.

This is exploratory evidence on a previously inspected corpus. It does not
establish coverage on unseen primes, a success probability, or a universally
faster policy. Production defaults are unchanged. The experiments live in
`bench/HexPrimality/FactorExperiment.lean`; the computational executable imports
no Mathlib. Frozen kernel replay lives separately in
`bench/HexPrimalityMathlib/ProofProbe/FactorExperiment.lean`, built by the existing
`HexPrimalityMathlibProofProbe` CI target.

## What changed

Pocklington certificates prove an integer prime using certified prime factors
of its predecessor and modular identities. Finding those factors can dominate
construction. Elliptic-curve factorization (ECM) supplies factors to that search;
the resulting primality proof here still uses Pocklington. These experiments do
not use elliptic-curve primality proving (ECPP).

Hex already implements square-root and cube-root Pocklington certificates,
including the additional checks required by the cube-root criterion. Supplying
only the predecessor factor lists discovered by PrimeCert let Hex's unchanged
constructor prove both primes. That diagnostic identifies factor discovery as
a sufficient explanation of the earlier failures.

The experiments supply **no factors, witnesses or certificates** to construction.
They reuse Hex's existing Pollard, ECM, subset-selection, witness-search and
checker implementations. Each successful construction passes `checkPrime` and
binds the result to the original subject; the frozen proofs then replay the
same certificate text through `natPrime_of_checkPrimeAt` in the Lean kernel.

The experimental policies vary preliminary factoring resources, ECM curve
schedules, construction dispatch and stopping conditions. The staged family
also screens each residual for probable primality before ECM; the current
provider can retain an untested prime when its core allowance is exhausted.
The staged family does not implement SQUFOF rescue, which is disabled in all
these profiles. Their relative timings measure the complete policies. They do not
isolate a single bound or the effect of random curve parameters.

| Profile | Preliminary factoring | ECM rounds | Dispatch / stopping |
| --- | --- | --- | --- |
| `baseline` | Current construction budget | 64 consecutive parameters, bounds 32768/524288 | Current core-first pass, then one registered-provider retry |
| `baseline-single` | Current construction budget | Same as baseline | One combined-provider pass; dispatch control |
| `fixed` | Current construction budget | 64 consecutive parameters, bounds 10000/1000000 | One combined-provider pass |
| `short` | p−1 bounds 64, 512, 4096; two rho restarts of 8192 steps | Same as `fixed` | One combined-provider pass |
| `staged` | Same as `short` | 50 consecutive parameters at 10000/1000000, then 200 at 50000/4000000 | One combined-provider pass |
| `random` | Same as `short` | Same bounds/counts as `staged`, with reproducible parameters drawn from the shared random state | One combined-provider pass |
| `mixed` | Same as `short` | First random round, current 64-curve consecutive round, then larger random round | One combined-provider pass |
| `efficient` | Same as `short` | Same as `mixed` | Also stops between residuals when the constructor's own sufficient-factor test accepts the known product |
| `balanced` | Adds p−1 bound 32768 to `short` | Same as `efficient` | Same as `efficient` |
| `random-retry` | Current construction budget | Same as `random` | Current core-first pass, then retry; extension-dispatch control |

All current profiles retain the 1024-attempt shared construction limit, 521-bit
input limit and depth 32. Attempt counts are bookkeeping limits: one stage at
larger bounds can cost much more than one at smaller bounds. Wall times are the
performance measurements. A historical `extended` pilot raised only the attempt
limit to 4096 and changed neither successful result; it is retained in
`construction-screen-v1.json` and has been removed from the current driver.

The larger ECM round stays below Hex's existing stage-2 endpoint cap. SymPy
1.14.0's corresponding second round uses endpoint 5000000; this experiment uses
4000000. It is a bounded approximation to that schedule, with a different
generator and arithmetic implementation. Random ECM consumes the shared state,
so it also changes subsequent rho/witness draws. No ideal randomness claim is
made. These policies are experiments outside the existing production schedule's
consecutive-parameter contract.

`efficient` reuses the constructor's private `sufficient` function through a
test-only `import all`; it does not duplicate the cube-root arithmetic. Before
each residual it computes the exact known factor product, leaving all remaining
components in the residual if it stops. A production API would need to expose
that condition and pass the caller's actual construction budget.

## Matched generation timings

`paired-v1.json` contains four timing trials per subject, ordered Hex/PrimeCert,
PrimeCert/Hex, Hex/PrimeCert, PrimeCert/Hex. Each subject has its own leased CPU;
its two arms run adjacent. The Hex arm is `random`. Each trial repeats the same
seed and therefore the same search, rather than adding a coverage observation.

| Subject | Hex times (s) | PrimeCert+SymPy times (s) | Ratio of medians, PrimeCert / Hex |
| --- | --- | --- | --- |
| ordinary-4 | 81.64, 70.04, 66.66, 63.49 | 128.75, 140.42, 142.63, 109.73 | 1.97 |
| difficult-0 | 3.24, 3.49, 4.28, 3.25 | 8.66, 9.10, 9.50, 9.07 | 2.70 |

These subjects were selected because both systems proved them. The timing
comparison is conditional on that common success set. It excludes kernel replay
and dependency compilation; it includes process startup, automatic search and
certificate formatting. Hex also performs its final native checker acceptance
test during construction. End-to-end tactic elaboration was not measured.

This compares the tools as shipped, including their different leaf tables:
Hex certifies table primes below 100000 directly, while this PrimeCert generator
uses its small-prime table through 3000. PrimeCert launches a separate
`uv`/Python/SymPy process to factor each larger recursive predecessor: 13 calls
for ordinary-4 and 22 for difficult-0. The times include all those repeated
environment, interpreter and import costs. They do not compare only factoring
arithmetic.

PrimeCert is unmodified upstream commit
`0803c2f6bd289c09704c7d352bb8fcf770cbb9b2`, using its Python generator and SymPy
1.14.0 with Python integer arithmetic. Its proof replay uses its pinned Lean
4.33.0 and Mathlib. Hex uses Lean 4.35.0-rc3. Exact versions, sources, binary
hashes, commands, CPU assignments, load observations and raw output are retained.
Shared-host activity never caused a sample to be dropped or repeated.

## Coverage at the common operational ceiling

`coverage-v1.json` and `primecert-coverage-v1.json` retain one automatic attempt
per subject with a 180-second wall limit and no supplied factors. These are the
eight previously frozen holdout subjects from
`reports/ecpp/native512/corpus-v1.json`; they are now tuning data for these
policies. The ceiling describes operational capability, not mathematical
impossibility when a run exhausts or times out.

| Subject | Hex `random` | PrimeCert+SymPy |
| --- | --- | --- |
| ordinary-0 | Exhausted | Timeout |
| ordinary-1 | Exhausted | Timeout |
| ordinary-2 | Exhausted | Timeout |
| ordinary-3 | Exhausted | Timeout |
| ordinary-4 | Proved | Proved |
| ordinary-5 | Timeout | Timeout |
| difficult-0 | Proved | Proved |
| difficult-1 | Timeout | Timeout |

`efficient-coverage-v1.json` has the same two successes. Four failures exhaust
their finite curve schedule before the shared attempt limit; the two timeouts
remain censored. Increasing only the attempt limit does not extend that schedule.
Timeout/exhaustion classification near a wall limit can vary with host load.

The `efficient` policy also proved both common successes with seeds `n+1` and
`n+2`, in addition to the subject-derived seed `n`. The six subject/seed
observations are retained in the coverage and seed reports. They test robustness
on these two subjects and do not estimate a general success probability.

## Standard field primes and policy tradeoffs

Simply replacing consecutive curves with the `random` profile substantially
regressed secp256k1 and P-384. The mixed schedule restored their useful existing
curves, and stopping after enough factors were available removed substantial
unnecessary work. A modestly longer p−1 ladder further improved Curve448.

`balanced-fields-v1.json` contains two adjacent baseline/balanced timing trials
in opposite orders. All six subjects succeeded in both arms. Times below are
medians including process startup; particularly small values include a material
startup component.

| Subject | Current baseline (s) | Experimental `balanced` (s) |
| --- | --- | --- |
| Curve25519 | 0.487 | 1.592 |
| secp256k1 | 23.074 | 16.563 |
| P-256 | 0.053 | 0.045 |
| P-384 | 26.857 | 1.208 |
| Curve448 | 17.970 | 2.173 |
| P-521 | 1.407 | 0.175 |

The Curve25519 regression remains. The more conservative `balanced` profile
also took about 98 seconds on ordinary-4, compared with the earlier `random`
profile's matched median of 68 seconds. Those different-policy runs were not
paired, so this is a tradeoff observation rather than another speedup estimate.
Registering a new fallback provider alone would not reproduce the direct-pass
measurements: current tactic dispatch first runs the original core budget.
`dispatch-controls-v1.json` separates that issue from the ECM schedule.
In one control run, retaining that core-first dispatch and its full preliminary
factoring allocation, then using the staged random provider, proved ordinary-4
in 52.62 seconds and difficult-0 in 7.49 seconds. The single-pass current provider
exhausted on both. This is a promising fallback candidate; these single control
runs are not the four-trial paired comparison above.

## Replay and retained evidence

`kernel-certificates.json` identifies each distinct successful Hex certificate
by SHA-256 and its guarded theorem in the frozen probe. `replay-links.json` links
every successful measured row to that proof. The guard allows only `propext`,
`Classical.choice` and `Quot.sound`. `primecert-kernel-replay.json` retains the two
upstream kernel replays. Generated theorem names are shortened in those modules,
while the exact `prime_cert%` term is preserved. Both the generated output and
the extracted certificate term have SHA-256 links; each fresh term counted here
is identical to the term in its replayed module. A generator's textual success alone never
counts as a proof.

The SymPy traces show the actual ECM escalation at the earlier bottlenecks.
`sympy-curves-difficult0.log` records its eighth curve finding the 19-digit factor;
`hex-sympy-same-curve.json` shows Hex finding the same factor on that exact curve.
This is an arithmetic diagnostic, with no factor or curve injected into any
automatic construction experiment.

All pilots remain evidence. `screen-v1.json` contains a driver-entry-point
failure and is excluded from measurements. `fields-v1.json` is exploratory only:
a rebuild changed the executable for a late sample, so its initial binary hash
cannot attest the complete schedule. Later field comparisons use frozen copies
of their executables, checked before every sample. The four paired `random`
native trials used their recorded original binary; it was restored before the
last native trial. Raw records preserve the original source versions, including
earlier driver limitations.

## Reproduction and remaining experiments

Build the executable and the CI-reachable frozen proof target:

```sh
lake build hexprimality_factor_experiment HexPrimalityMathlibProofProbe
```

Run a new comparison into a new output path; the runner refuses to overwrite
existing results and freezes the binary before measuring:

```sh
python3 scripts/bench/primality_factor_experiment.py \
  --output /tmp/pocklington-paired.json --mode construct \
  --subjects successes --profiles random primecert --trials 4 \
  --timeout 180 --jobs 2 --primecert /path/to/PrimeCert
python3 scripts/bench/primality_factor_experiment.py \
  --output /tmp/pocklington-fields.json --mode construct \
  --subjects fields --profiles baseline balanced --trials 2
```

For exact historical reproduction, use the driver and Lean source snapshots
stored in that run's JSON with its recorded dependency revision. Current source
includes later controls and stopping policies. `--seed-offset` selects additional
seeds separately from repeated timing trials. Kernel replay is a separate build,
with generated certificate hashes linked to the run records.

Before selecting a production policy, freeze a fresh independent corpus, test
several seeds, measure the actual proposed tactic dispatch, and resolve the
remaining Curve25519 regression. Preserve the existing sound checker and kernel
replay throughout. No library phase counter, production allocation or release
admission changes on the strength of this exploratory sample.
