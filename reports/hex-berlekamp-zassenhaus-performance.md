# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-polynomial factorization
entry point. Standalone classical and lattice entries remain development
diagnostics, not alternative public implementations.

The mode-selection audit was run on `chungus2` (AMD EPYC 9455, NixOS 26.11,
Linux x86-64). Clean parametric sweeps at revision `5b3efbc7` establish why
the former modes fail. The clean `e51066e1` calibration fixes absolute budgets
before the initial `609465e8` acceptance run, and the clean inclusive audit
below establishes phase attribution. A clean current-main acceptance run at
`b5cbd08d` reconfirms that all twenty-two selected mode-3 registrations pass.
The direct dependencies are now through Phase 4 or later (`HexBerlekamp` 7,
`HexHensel` 4, and `HexLLL` 7), so the Phase-4 dependency gate is met. The
cross-system Hex record remains the clean revision `7425e083` run on
verified-idle core 19; the external systems retain their 2026-08-01
same-protocol record on the same host. The committed 392-row corpus has SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`. Services
were persistent and warmed; each call had a ten-second cutoff; rows below one
second used the median of five calls, and slower rows one call.

## Bench Targets

The fixed registrations in `bench/HexBerlekampZassenhaus/Bench.lean` and the
adversarial ladder cover the six declared `phase4.input_families`, which are
the coverage contract for this report:

- `public-factor-combinator`: `runFactorChecksum` at `smokeInput 24` and
  `runFactorCompareChecksum` at `smokeInput 8`, both using the public
  `ZPoly.factorize` cascade.
- `fallback-probe`: `runFactorFallbackProbeChecksum` at the historical
  degree-24 `(X-1)...(X-24)` probe. The current cascade takes proposal replay;
  it does not enter the trial fallback.
- `exhaustive-slow-backstop`: `runFactorSlowChecksum` and
  `runFactorSlowCompareChecksum` at `smokeInput 8`, the unconditional exact
  `factorTrial` backstop.
- `degree-height-matrix`: public factorization at `(degree, height) = (6, 32)`
  and trial factorization at `(4, 8)`.
- `cld-fast-path`: `runFastPathPrecisionLocalChecksum` at
  `(degree, height, precision, local factors) = (8, 32, 128, 8)`. This is
  fast-path setup, not a complete `factorLattice` call.
- `ho2-adversarial-recombination`: `runFactorAdvX4Plus1Checksum`,
  `runFactorAdvQuadSqrt2Sqrt3Checksum`, `runFactorAdvPhi15Checksum`,
  `runFactorFastSetupAdvX4Plus1Checksum`, `runFactorFastSetupAdvPhi15Checksum`,
  `runAdvSwinnertonDyerSD3ModularSplitChecksum`, and the full-lattice
  `runFactorLatticeAdvSwinnertonDyerSD3/SD4Checksum` checks.

Six product-adoption targets are also fixed: the schoolbook and dispatch pairs
at 64 lifted factors, 32 dense reassembly factors, and 256 skew factors. The
`runIsabelle*` registrations are the scheduled-hardware pairing
harness for the external comparator and carry the `[scheduled-hardware]` tag.
The 392-row corpus sweep (`scripts/bench/factor_sweep.py`) is the source of
record for cross-system evidence; `list` and `verify` run in CI on every PR.

## Verdicts

### Complexity-mode audit

Every formerly parametric factor and product registration, together with the
eight fixed adversarial performance registrations, selects **mode 3**.
Asymptotic regression detection is deliberately given up for these operations;
the fixed targets detect absolute regressions on canonical hard inputs instead.

Mode 1 is unavailable for the five public/setup factor candidates. The public
cascade selects input-dependent prime plans, proposal replay, classical
recombination, CLD, trial fallback, and early exits, while the precision target
times setup only. A clean sweep of all eight former factor registrations at
`5b3efbc7` gives `inconclusive` in every case, recorded in
`reports/bench-results/hex-berlekamp-zassenhaus-parametric-audit-5b3efbc7-chungus2.json`
(SHA-256 `ecb6c3932abeadeacea757318297b136943c089215f3b2ed1dc7befd79cb0fc6`).

Mode 2 also fails. The available version of Belabas, van Hoeij, Klüners, and
Steel, [*Factoring polynomials over global fields*](https://doi.org/10.5802/jtnb.655),
states the `O(n^9 + n^7 h^2)` classical-arithmetic result as Corollary 5.3
(the directive refers to Corollary 5.9) and identifies LLL basis reduction as
the dominant step. Inclusive attribution of the top former rungs gives:

| Registration | Production route | Largest inclusive phases | Lattice basis reduction |
|---|---|---|---|
| `runFactorChecksum` | proposal replay | proposal 54%, prime walk 42% | not executed |
| `runFactorFallbackProbeChecksum` | proposal replay | proposal 54%, prime walk 41% | not executed |
| `runFactorCompareChecksum` | classical | Hensel 45%, prime walk 28%, recombination 15% | not executed |
| `runFactorDegreeHeightChecksum` | classical | Hensel 50%, prime walk 26%, recombination 12% | not executed |
| `runFastPathPrecisionLocalChecksum` | setup only | Hensel 75%, precision cap 23%, checksum <1% | not executed |

The clean inclusive export is
`reports/bench-results/hexbz-complexity-audit-2dbfd1d3-chungus2.json`
(SHA-256 `83b48dd70ed7524a38e6027b4e1c0f252b918dcae9f9f29505d48f4207a3f8d1`),
generated by `scripts/bench/hexbz_complexity_audit.py`. It retains one whole
median-total execution per case, so the phase shares are not assembled from
different calls. The precision/local profile includes the result checksum as
well as every computational phase. No phase covered by the cited lattice
analysis controls any measured family.

The inclusive command was
`python3 scripts/bench/hexbz_complexity_audit.py --output
reports/bench-results/hexbz-complexity-audit-2dbfd1d3-chungus2.json --cpu auto
--warmup 1 --repeats 5 --cutoff 30`. The parametric exports use the eight factor
or six product target names printed in their JSON, respectively, with
`taskset -c "$(python3 scripts/bench/idle_core.py)"
.lake/build/bin/hexbz_bench run ... --export-file <cited-path>`; their exact
parameter schedules and runner configuration are embedded in every result.

The three slow targets time `factorTrial`, not modular-factor subset
recombination. `positiveDivisors` and `integerRootCandidates` scan every integer
through the absolute constant coefficient before the residual coefficient-vector
search. Consequently `smokeInput n` scans through `(n+1)!`, and a degree/height
input scans through `(height+1)^degree * degree!`; the former `2^n` declaration
described a different algorithm. The short ladders also cross the quadratic
integer-root shortcut, so no tight one-parameter family is justified.

The six product ladders likewise have no passing parametric mode. Their clean
audit at `5b3efbc7` is
`reports/bench-results/hex-berlekamp-zassenhaus-product-parametric-audit-5b3efbc7-chungus2.json`
(SHA-256 `b27cb9b71cdc4b43606eb706bba4c64c97948237a14200f1c98b536f96eff3f3`):
the balanced and reassembly pairs grow about `n^(2.45..2.58)` against `n^2`,
while the skew pair grows about `n^1.49`. The coefficient bit width grows with
the product, so the old coefficient-operation argument does not derive a tight
bit-complexity law.

### Mode-3 budgets

The absolute budgets are operation-specific measured-baseline ceilings, not
the harness default. The clean `e51066e1` calibration export
`reports/bench-results/hex-berlekamp-zassenhaus-fixed-e51066e1-chungus2.json`
(SHA-256 `6d3b8ebb2eff4b8909a809a74268c0d349d1a0496f9c173398e8ac2e9d1d94b2`)
was recorded before these ceilings were chosen. Each budget rounds upward to
at least ten times the calibration maximum. The lifted-product pair uses a
50x margin to admit observed shared-runner scheduling pauses. The
byte-identical trial split/compare targets share the 800 ms budget derived from
their worse 75.715 ms calibration maximum.

The eight adversarial inputs use the earlier clean fixed calibration
`reports/bench-results/hex-berlekamp-zassenhaus-fixed-0b95505b-gcd-hensel-chungus2.json`
(SHA-256 `82ddd9e54cfafcfefc936ffeb1f1c8bb7e926e7545cd2b992ecfbc508e1ee78d`).
That export predates budget selection and contains precisely the eight
adversarial registrations, all successful with agreeing hashes. The six
micro-check budgets round upward to 5 ms; the SD3 and SD4 full lattice budgets
round upward to 25 ms and 400 ms. Every ceiling is at least ten times its
calibration maximum.

This margin admits allocator and shared-runner noise while still rejecting
operation-specific order-of-magnitude regressions. The trial target's
variability is part of the implementation being measured: `positiveDivisors`
materializes all 362,881 candidates for `smokeInput 8`. Expected output hashes
make every fixed check semantic as well as temporal.

| Target/input | Clean median | Budget |
|---|---:|---:|
| public split, `smokeInput 24` | 3.746 ms | 50 ms |
| historical fallback probe, degree 24 | 3.486 ms | 50 ms |
| trial split, `smokeInput 8` | 2.305 ms | 800 ms |
| public compare, `smokeInput 8` | 0.259 ms | 5 ms |
| trial compare, `smokeInput 8` | 2.296 ms | 800 ms |
| public degree/height `(6, 32)` | 0.174 ms | 5 ms |
| trial degree/height `(4, 8)` | 0.819 ms | 100 ms |
| precision/local `(8, 32, 128, 8)` | 1.028 ms | 20 ms |
| lifted products, 64 factors (reference / dispatch) | 9.620 / 9.615 ms | 500 ms |
| dense reassembly, 32 factors (reference / dispatch) | 112.077 / 111.851 ms | 1.2 s |
| skew products, 256 factors (reference / dispatch) | 79.759 / 79.758 ms | 900 ms |
| `X^4 + 1`, public / fast setup | 0.033 / 0.017 ms | 5 / 5 ms |
| `(X^2-2)(X^2-3)`, public | 0.033 ms | 5 ms |
| `Phi_15`, public / fast setup | 0.084 / 0.019 ms | 5 / 5 ms |
| SD3 modular split | 0.008 ms | 5 ms |
| SD3 / SD4 full lattice | 1.601 / 29.985 ms | 25 / 400 ms |

The clean current-main export
`reports/bench-results/hex-berlekamp-zassenhaus-fixed-b5cbd08d-chungus2.json`
(SHA-256 `cc80ca3666b1ae090f25f8f7dc3b04835e3291787b5bcf1a6ff5c6f76434eb26`)
records all twenty-two mode-3 registrations passing the independently fixed
budgets, with all five repeats successful, no budget truncation, and every
expected hash matching. The
`runIsabelle*` fixed endpoints remain comparator anchors; they make no
complexity claim and do not replace performance coverage.

CPU 1 was returned idle with all SMT siblings idle immediately before the
current run. Its exact command was:

```sh
taskset -c 1 .lake/build/bin/hexbz_bench run \
  Hex.BerlekampZassenhausBench.runFactorChecksum \
  Hex.BerlekampZassenhausBench.runFactorFallbackProbeChecksum \
  Hex.BerlekampZassenhausBench.runFactorSlowChecksum \
  Hex.BerlekampZassenhausBench.runFactorCompareChecksum \
  Hex.BerlekampZassenhausBench.runFactorSlowCompareChecksum \
  Hex.BerlekampZassenhausBench.runFactorDegreeHeightChecksum \
  Hex.BerlekampZassenhausBench.runFactorSlowDegreeHeightChecksum \
  Hex.BerlekampZassenhausBench.runFastPathPrecisionLocalChecksum \
  Hex.BerlekampZassenhausBench.runTrialProductSchoolbookChecksum \
  Hex.BerlekampZassenhausBench.runTrialProductChecksum \
  Hex.BerlekampZassenhausBench.runReassemblyProductSchoolbookChecksum \
  Hex.BerlekampZassenhausBench.runReassemblyProductChecksum \
  Hex.BerlekampZassenhausBench.runSkewProductSchoolbookChecksum \
  Hex.BerlekampZassenhausBench.runSkewProductChecksum \
  Hex.BerlekampZassenhausBench.runFactorAdvX4Plus1Checksum \
  Hex.BerlekampZassenhausBench.runFactorFastSetupAdvX4Plus1Checksum \
  Hex.BerlekampZassenhausBench.runFactorAdvQuadSqrt2Sqrt3Checksum \
  Hex.BerlekampZassenhausBench.runFactorAdvPhi15Checksum \
  Hex.BerlekampZassenhausBench.runFactorFastSetupAdvPhi15Checksum \
  Hex.BerlekampZassenhausBench.runAdvSwinnertonDyerSD3ModularSplitChecksum \
  Hex.BerlekampZassenhausBench.runFactorLatticeAdvSwinnertonDyerSD3Checksum \
  Hex.BerlekampZassenhausBench.runFactorLatticeAdvSwinnertonDyerSD4Checksum \
  --export-file \
  reports/bench-results/hex-berlekamp-zassenhaus-fixed-b5cbd08d-chungus2.json
```

### Phase 5–7 re-attestation

The Phase-5 conformance evidence remains current: the clean 107-case FLINT
oracle pass retained by `dfefdfac2` covers production source that has not
changed since, a fresh `hexbz_emit_fixtures` emission is byte-identical to that
committed fixture, and `bz_trace_gate.py` accepts all 55 production dispatch
traces. The published trust-surface check also confirms zero `sorry`, `axiom`,
or `native_decide` occurrences.

The Phase-6 API audit from `2f43d702b` established clean Batteries docstring
and theorem lint, complete public/non-obvious-helper docstrings, no dead
declarations, native Lean execution, and Lean-checked irreducibility
certificates. Production library source is byte-identical to that audited
state; subsequent library-tree changes affect only the SPEC, README, and
quickstart test. Against the previous committed mode-3 acceptance baseline
`609465e8`, the fourteen shared medians range from `0.380x` to `1.013x`; there
is no performance regression. The eight adversarial registrations compare
against their clean `0b95505b` baseline and remain within their independently
fixed budgets.

For Phase 7, `check_phase7.py` confirms the reference chapter and anchored
prime-splitting tutorial, both of which build in `HexManual`. The released
manifest checker separately confirms the README shape, and
`HexBerlekampZassenhaus.FactorTacticTests` build-checks its quickstart. The
manual-split checker confirms the chapter remains in its published location.

## Comparator Ratios

The declared comparator is the
**verified Isabelle BZ (AFP Berlekamp_Zassenhaus; Haskell extraction of factor_int_poly via Factorization_External_Interface)**,
class `gating`. Current Hex record:
`reports/bench-results/hexbz-factor-sweep-7425e083-hex-chungus2-cpu19.json`
(SHA-256
`3c166d993e7847bac66667338407630d273e7d015472f09968719484e71bcef0`);
external record:
`reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`. Tables
regenerated by `python3 scripts/bench/factor_sweep_table.py` (newest record
per system). Every answering system agreed with the committed factor-degree
oracle or with the other systems on rows without one; the sweep's
cross-check reports no mismatches.

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 383 | 9 | 267.797 us | 6.546 ms | 3.793 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

On eligible common rows (both sides above ten times their protocol
overhead), Hex divided by verified Isabelle BZ has median `0.508x`,
p10-p90 `0.311x-1.421x`, and a 171-36 win split. The optimized unverified
libraries remain substantially faster: median Hex ratios are `6.125x`
against FLINT, `6.237x` against PARI, and `2.725x` against NTL on 81, 86,
and 148 eligible pairs.

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.429x | 9 |
| Conway | 79 | 0.442x | 60 |
| Cyclotomic | 24 | 0.462x | 20 |
| Cyclotomic products | 18 | 0.582x | 16 |
| Laguerre | 12 | 0.601x | 12 |
| Legendre | 13 | 0.493x | 12 |
| Random products | 26 | 0.464x | 25 |
| Swinnerton-Dyer products | 7 | 0.628x | 5 |
| Swinnerton-Dyer | 6 | 0.590x | 6 |
| Wilkinson | 13 | 1.082x | 6 |

**The gating goal is met.** Small/medium-r classical-tier rows sit well
within a small constant of the verified reference (aggregate median
`0.508x`, i.e. Hex ahead), and the lattice-backed tail strictly beats it:
Hex wins all six eligible Swinnerton-Dyer pairs, and on the 160-row combined
mixture Hex solves 151 rows against Isabelle BZ's 141 with the worst
cumulative Hex/Isabelle ratio over ranks 125-140 at `0.667x` (rank 133),
below the `0.85x` acceptance bound at every rank
(`python3 scripts/bench/cactus_rank_table.py --lo 125 --hi 140`).

**Across the classical/lattice seam.** The committed dispatch baseline
(`conformance-fixtures/HexBerlekampZassenhaus/bz-trace-baseline.json`,
enforced by `scripts/oracle/bz_trace_gate.py` on every PR) records the
production tier per Swinnerton-Dyer rung: the last classical rung is the
SD3 family (`adv/swinnerton_dyer_sd3`, `method: classical`, r = 4), and the
first lattice-backed rung is the SD5 pair (`adv/swinnerton_dyer_sd5_pair`,
`method: lattice`, r = 32), with SD6 carried by the quadratic-norm
certificate tier of the lattice-backed tail (`method: quadraticNorm`,
r = 32). Scheduled-hardware wall-clock across that seam, from the current
record: `sd4` 823 µs, `sd5` 6.546 ms, `sd6` 26.282 ms, `sd7` 190.206 ms,
all solved under the cap, while verified Isabelle BZ times out on all three
`sd6` variants (recorded as solved-under-cap versus timeout, not a finite
ratio). Per the SPEC's algorithm-class caveat, Isabelle's classical
exhaustive recombination is asymptotically weaker than the BHKS van Hoeij
CLD tier, and the wall-clock advantage above is that asymptotic difference
made measurable.

The nine Hex timeouts are three Swinnerton-Dyer products
(`sd5_x_sd5shift1`, `sd6_x_phi105`, `sd6_x_sd6shift1`) and six
Hoeij-Zimmermann rows (`hoeij_F192`, `hoeij_F256`, `hoeij_F351`,
`hoeij_F630`, `hoeij_P7`, `hoeij_S9`); there is no common answered
Hoeij-Zimmermann row with verified Isabelle BZ, so those record as
timeout-versus-timeout, not ratios. Open recombination proposals (#9151,
#9152, #9153) remain measurement-gated future work on that tail; their
motivating profiles predate the quadratic-norm certificate, so the rows
that still reach recombination must be re-profiled before any of the three
changes production.

## Profile

The mode-selection evidence is the inclusive phase table above, not sampling
leaf categories. Historical sampling profiles were captured at clean
`f396965d` for one representative
compiled case of each parametric family with samply 0.13.1 at interval
1.001 ms (~999 Hz), through `scripts/profile/run_profile.sh`
(lean-bench-samply orchestrator, timed-region filtered, target 3 s). The
leaf-cost categorisation is committed as
`reports/bench-results/hexbz-leafcost-f396965d-chungus2.txt` (SHA-256
`869bc76d71c02d1b1522b07e841669727acf5f113b21f680d56b3f47a8f811e0`); raw
`*.json.gz` profiles are developer-local per SPEC/profiling.md.

| Capture | own code | Lean runtime | allocator | GMP | libc |
|---|---:|---:|---:|---:|---:|
| `public-factor-combinator`, n=8 (2100 samples) | 23.7% | 29.3% | 32.0% | 6.0% | 8.5% |
| `cld-fast-path`, 4_004_016_004 (2321 samples) | 26.4% | 27.6% | 26.1% | 8.2% | 11.2% |
| `exhaustive-slow-backstop`, n=8 (2019 samples) | 19.3% | 29.4% | 49.9% | 0.2% | 0.0% |
| `degree-height-matrix`, 4x2 encoding (2087 samples) | 12.9% | 34.2% | 34.5% | 7.5% | 10.6% |
| `fallback-probe`, n=8 (2989 samples) | 30.0% | 30.0% | 34.0% | 2.5% | 3.0% |

These secondary profiles match the algorithms: the cascade families are
allocation-and-refcount dominated (the dispatcher builds and discards
candidate structures; `mi_free`/`mi_malloc_small` lead every capture), GMP
appears exactly where big-integer lift moduli and CLD bounds are computed
(the cld-fast-path and degree-height captures), and the exact backstop is
the most allocator-bound (49.9%), consistent with its integer-candidate
churn. No capture shows a dominant cost in a function the SPEC does not
name as hot; no audit-found issue was filed from these captures.

The `ho2-adversarial-recombination` family's registered cases are fixed checks
with tuned timing floors over µs-ms bodies; the lean-bench child emits no
timed-region sidecar for fixed dispatch, so the orchestrator cannot capture
them. Its shape coverage is carried by the `public-factor-combinator`
capture, which exercises the same production cascade code path, and its
timing evidence by the fixed adversarial ladder in Verdicts and the
committed dispatch baseline above. This is the declared scope of profile
coverage for that family, not an omission.

## Concerns

None.
