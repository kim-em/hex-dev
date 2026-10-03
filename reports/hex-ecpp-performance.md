# HexECPP performance

## Bench targets

The compiled core is Mathlib-free. `lake build hexecpp_bench` builds the
LeanBench executable; `hexecpp_bench list` and `verify` check registration
wiring and content hashes. Arithmetic acceptance is distinct from the
companion's kernel primality proof. The latter's existing fresh-module
measurements remain in [reports/ecpp/README.md](ecpp/README.md).

| Advertised compiled operation | Targets | Strongest justified mode |
| --- | --- | --- |
| Checked affine scalar replay, inverse consumption | `runReplay`, `runScalarReplay`, `runSizedReplay`, `runModulusReplay` | 1: large-scalar bit-copy and bounded-width caller regimes; 2: actual modulus-width arithmetic |
| Scalar transcript proposal | `runProposal`, `runScalarProposal`, `runSizedProposal`, `runModulusProposal` | 1: the same bit-copy/bounded-width regimes; 2: classical Euclidean inverse and ring upper bounds at variable modulus widths |
| `parsePari` and text scanning/decoding | `Hex.ECPPBench.runParse`; `runParse512` | 1: linear fixed-width row ladder; 3: full wide-integer endpoint |
| Parsed-input `preflight` | `Hex.ECPPBench.runPreflight` | 1: linear fixed-width row traversal |
| `check`, `checkAt`, local `checkStep`, size inequality and terminal replay | `runCheck65`, `runCheck256`, `runCheck512`, `runNativeCheck` | 3: complete accepted chains with explicit terminal certificates |
| `convert`, `convertRow`, `convertText`, normalization and inverse generation | `runConvert65`, `runConvert256`, `runConvert512`, `runNativeConvert` | 3: complete supplied conversion plus checker acceptance |
| `convertCounted`, including endpoint construction | `runCountedConvert65` | 3: supplied 65-bit vector, seed one, endpoint fuel 200 |
| CM roots, norms, traces and all portfolio twists | `runCM128`, `runCM256` | 3: roots and integer norm equations, with all exceptional twists checked |
| `produce` and stateful bounded native `search` | `runNative128`, `runNative256`, `runNativeHard`, `runNativeExhaust` | 3: successful recursive production and complete root-portfolio exhaustion |

Point-addition branches and helper predicates are measured inside replay,
proposal and complete checking. They are not independent search endpoints.
The five structured families in `libraries.yml` cover each significant phase:
transcript length, independent scalar/modulus widths, row vectors, supplied
certificates and native production.
`runSize65/256/512` are private representation-count observations; they do not
advertise a public size API or discharge a performance criterion.

For scalar ladders, `q = 13 * (2^k - 1)` has `k + O(1)` bits; the point
`(1,2)` has order thirteen modulo seven. The prescribed `Nat.testBit` extracts
each bit by shifting the complete natural number. Lean's bignum shift copies
the remaining suffix, so the total copied bits are quadratic in `k`, while
the affine ring operations and witness traversal are linear. This source-level
derivation precedes the corrected runs and is adjacent to the registrations.
See [Lean's bit definition](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/Init/Data/Nat/Bitwise/Basic.lean)
and [runtime `lean_nat_big_shiftr`](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/runtime/object.cpp).
The SPEC's separate `O(L)` **modular-operation** bound is unchanged. The actual
scientific ladder doubles `k` from 262,144 through 4,194,304, exposing bignum
suffix work. It is a family claim, not a subject-bit complexity theorem.

Actual caller widths have separate coverage. Independent GP-generated primes
range from 64 through 4,096 bits, with full-width point coordinates and dense
scalars. `runSizedReplay` and `runSizedProposal` grow both widths together;
`runModulusReplay` and `runModulusProposal` hold the scalar at 47 bits while
varying modulus width. `runScalarReplay` and `runScalarProposal` vary scalar
width from 32 through 512 bits at the supplied vector's 65-bit modulus.
[The generation record](ecpp/audit/sized-primes.json) retains the command,
GP version and exact outputs. Expected points and inverse transcripts are
prepared outside timing; every measured call checks the complete result.

The modulus-width registrations use mode 2. No tight monomial covers the changing GMP arithmetic regimes and, on the
diagonal, scalar bit-copying. Proposals additionally have operand-dependent
Euclidean iterations and quotient sizes. GMP's [basecase division](https://gmplib.org/manual/Basecase-Division)
and [multiplication](https://gmplib.org/manual/Basecase-Multiplication)
have quadratic upper bounds. Classical extended Euclid also costs O(k²):
quotient widths sum to O(k), with each division/coefficient update bounded
by its quotient width times k. See Brent and Zimmermann,
[Modern Computer Arithmetic, §§1.6, 1.6.2 and 2.5](https://maths-people.anu.edu.au/~brent/pd/mca-cup-0.5.9.pdf).
At most 2k additions/inverses give the diagonal cubic bound; a fixed scalar
gives the quadratic modulus bound. The proposal profile attributes its dominant
phase to this very Euclidean recurrence; checked replay instead measures ring
operations and allocations, covered by the GMP bounds. Bit extraction and list work are
below those bounds. These declarations precede collection and assert upper
bounds, rather than fitted equalities.

The fixed-modulus caller ladder uses the stronger mode 1 in its bounded-width
regime: scalar extraction copies at most eight limbs and Euclidean/ring
operands remain at 65 bits. At most two additions/inverses per scalar bit
give linear work across 32–512 bits. This is separate from the multi-million-bit
scalar ladder's quadratic copying regime; neither claim extrapolates into
the other regime. All six callbacks belong to `scalar-modulus-widths`.

Parser/preflight ladders double row count from one through 4,096. Every row
has fixed-width fields, so bytes, digit scans, JSON decoding and integer-limit
checks each take linear work. The wide-integer accepted endpoint complements
this controlled ladder; it does not infer a general integer-bit parsing bound.

For complete chains and bounded production, a subject-bit ladder changes
scalar lengths, inverse counts, terminal-factor shape, recursive depth and
success/exhaustion branches independently. Neither a tight one-parameter
family model nor a published **compiled wall-time** bound covers that whole
operation. The SPEC's scalar/root operation ceilings omit bignum and terminal
factor costs; the profile below confirms that limitation. After considering
modes 1 and 2, these endpoints use mode 3 with operation-specific regression
budgets. CM's bounded Euclidean and root paths also vary with valuations and
residues; its two fixed inputs test ordinary and exceptional proposal work,
and complete production additionally exercises other portfolio entries.

## Verdicts

All observations use the shared `chungus2` AMD EPYC 9455 host, an automatically
leased CPU and Lean 4.35.0-rc3. Every completed sample is retained, with host
load as context. The collectors record commands, CPU, toolchain, executable
digest, source digests and artifact digests; [dependencies.json](ecpp/audit/dependencies.json)
also fingerprints the computational prerequisites and frozen fixtures.

| Parametric target | Model | Verdict | Residual log slope | Retained export |
| --- | --- | --- | ---: | --- |
| `Hex.ECPPBench.runReplay` | `k * k` | consistent with declared complexity | -0.020550 | [runReplay.json](ecpp/audit/scientific-current.artifacts/runReplay.json) |
| `Hex.ECPPBench.runProposal` | `k * k` | consistent with declared complexity | -0.036033 | [runProposal.json](ecpp/audit/scientific-scalar-final.artifacts/runProposal.json) |
| `Hex.ECPPBench.runParse` | `r` | consistent with declared complexity | -0.002348 | [runParse.json](ecpp/audit/scientific-current.artifacts/runParse.json) |
| `Hex.ECPPBench.runPreflight` | `r` | consistent with declared complexity | -0.016072 | [runPreflight.json](ecpp/audit/scientific-current.artifacts/runPreflight.json) |
| `Hex.ECPPBench.runSizedReplay` | `k³` | within declared upper bound (observed faster) | -1.227522 | [runSizedReplay.json](ecpp/audit/scientific-gmp.artifacts/runSizedReplay.json) |
| `Hex.ECPPBench.runSizedProposal` | `k³` | within declared upper bound (observed faster) | -0.785837 | [runSizedProposal.json](ecpp/audit/scientific-widths-final.artifacts/runSizedProposal.json) |
| `Hex.ECPPBench.runModulusReplay` | `k²` | within declared upper bound (observed faster) | -1.230348 | [runModulusReplay.json](ecpp/audit/scientific-widths-final.artifacts/runModulusReplay.json) |
| `Hex.ECPPBench.runModulusProposal` | `k²` | within declared upper bound (observed faster) | -0.806975 | [runModulusProposal.json](ecpp/audit/scientific-widths-final.artifacts/runModulusProposal.json) |
| `Hex.ECPPBench.runScalarReplay` | `k`, 32–512 bits | consistent with declared complexity | 0.011959 | [runScalarReplay.json](ecpp/audit/scientific-caller-final.artifacts/runScalarReplay.json) |
| `Hex.ECPPBench.runScalarProposal` | `k`, 32–512 bits | consistent with declared complexity | 0.011601 | [runScalarProposal.json](ecpp/audit/scientific-caller-final.artifacts/runScalarProposal.json) |

Each ladder has three trial-major outer trials; no advisory remains. Commands:
`hexecpp_bench run <target> --export-file <export>`, orchestrated by
`python3 scripts/bench/ecpp_audit.py --output <record>` with `--family` and
`--skip-endpoints` selecting unresolved cases. The complete command streams
are in [scientific-current.json](ecpp/audit/scientific-current.json), source
`2aca3251099eab227c9a69d74370a3673720b659`, and
[scientific-scalar-final.json](ecpp/audit/scientific-scalar-final.json), source
`524f5ebdbd20ac3e99eefd8363376e230d2233c9`. The proposal callback, bit extraction
and its fixed-modulus helpers are unchanged between these sources; later
parser/search diagnostic edits and additive registrations do not affect it.

The four modulus-width harness exports say **inconclusive** because the
harness currently implements two-sided matching. Each has a negative residual
slope, declining normalized ratios, complete trials and no advisory. The
independently qualified mode-2 declarations therefore pass with the distinct
one-sided result shown above, as required by the benchmark contract pending
lean-bench #70. [scientific-widths-final.json](ecpp/audit/scientific-widths-final.json)
records source `e893b9f15c45f5cb1366ab6bd14858ce92568a8e` and the restored
natural-number inverse. The final modulus-proposal child records HEAD
`873bdbc33`, which added derivation comments and companion compatibility only;
its recorded core and executable hashes are unchanged. Replay's earlier export uses the identical timed
callback, prime moduli and canonical transcripts; proposal preparation is
outside measurement. [evidence-reuse.json](ecpp/audit/evidence-reuse.json)
records unchanged core hashes and the documentation-only search delta.
The fixed-modulus scalar ladder's fresh record is
[scientific-caller-final.json](ecpp/audit/scientific-caller-final.json).

Budgets are twice a retained baseline median rounded upward, declared before
their validation runs in `scripts/bench/ecpp_audit.py`. This permits a modest
bounded overhead increase without confusing host-specific seconds with a
universal guarantee. The prior baselines are
[compiled.json](ecpp/compiled.json),
[native/compiled-updated.json](ecpp/native/compiled-updated.json) and the
longest-chain/exhaustion rows in [native/validation.json](ecpp/native/validation.json)
and [native/campaign-updated.json](ecpp/native/campaign-updated.json).
Previously unregistered CM/counting cases use
[bootstrap-operations.json](ecpp/audit/bootstrap-operations.json), whose exact
source and command are in [bootstrap-operations-context.json](ecpp/audit/bootstrap-operations-context.json).
These are meaningful per-operation ceilings, not harness process timeouts.

| Fixed target | Median (ms) | Budget (ms) | Verdict |
| --- | ---: | ---: | --- |
| `runCheck65` | 0.145 | 0.32 | pass |
| `runCheck256` | 5.434 | 12 | pass |
| `runCheck512` | 20.383 | 45 | pass |
| `runConvert65` | 0.856 | 1.6 | pass |
| `runConvert256` | 69.570 | 170 | pass |
| `runConvert512` | 403.313 | 1,050 | pass |
| `runNative128` | 59.475 | 125 | pass |
| `runNative256` | 692.763 | 1,450 | pass |
| `runNativeHard` | 1,574.224 | 3,300 | pass |
| `runNativeCheck` | 4.683 | 10 | pass |
| `runNativeConvert` | 58.255 | 140 | pass |
| `runParse512` | 0.751 | 1.6 | pass |
| `runCM128` | 0.114 | 0.23 | pass |
| `runCM256` | 0.098 | 0.20 | pass |
| `runCountedConvert65` | 1.001 | 2.1 | pass |
| `runNativeExhaust` | 34.860 | 75 | pass |

All five repeats agree with expected hashes. First eleven rows come from
`scientific-current.artifacts/endpoints.json`; the remaining rows come from
[operations-final.artifacts/endpoints.json](ecpp/audit/operations-final.artifacts/endpoints.json).
[operations-final.json](ecpp/audit/operations-final.json) records its exact
command and source digests. `runParse512` returns seventeen parsed rows;
other budgeted cases return content-checked acceptance or exhaustion. Native
seeds are zero for the ordinary cases, seven for `runNativeHard`
(validation-256-7), and three for `runNativeExhaust` (tuning-256-3). The fixed
numerals, transcripts and hashes are defined in `bench/HexECPP/Bench.lean`
and its frozen fixture imports; native replay input is warmed outside timing.

Phase 6's adjacent comparison uses the main-tree bootstrap implementation
`5d232c765ab1525fa5894509bad7333dc0fa2edf`, rebuilt on the same pinned toolchain.
Five trial-major pairs alternate AB/BA, with all eleven shared registrations
and identical result hashes. [regression-current.json](ecpp/audit/regression-current.json)
retains every child sample and command; [regression-current-summary.json](ecpp/audit/regression-current-summary.json)
derives the paired medians without recollection. Checker ratios are
0.987/1.001/1.006; conversion ratios are 1.196/0.883/0.824; ordinary native
production ratios are 0.982/0.976. The small converter performs an additional full public-boundary replay;
larger conversion benefits from local-step checking and one final chain replay.
Every operation remains inside its independently declared ceiling. Parser
ratio is 1.017, native check 1.018 and native conversion 0.899.

## Comparator ratios

The comparator `PARI/GP primecertisvalid` is **informational**. The retained matched-subject
verification comparison uses Lean 4.34.1 source `de25e7b` and PARI 2.17.3 on
shared-host CPU 13. Reusing it answers the SPEC's external verification
question without mixing current Hex timings with old PARI timings. The retained
protocol and source versions are in [ecpp/README.md](ecpp/README.md),
[compiled.json](ecpp/compiled.json) and
[pari-verify.json](ecpp/pari-verify.json).

| Accepted subject bits | Hex check (ms) | PARI verification (ms) | Hex / PARI |
| --- | ---: | ---: | ---: |
| 65 | 0.155376 | 0.050 | 3.11 |
| 256 | 5.544 | 2.390 | 2.32 |
| 512 | 21.084 | 9.950 | 2.12 |

PARI times batches inside one persistent GP process using `gettime`: one
hundred validations per trial for the smaller subjects, twenty for the largest,
with five trial-major trials. Process launch lies outside the reported region,
so no subprocess overhead subtraction is needed. The integer-millisecond timer
limits the smallest batch's precision. All three canonical inputs are within
the soft per-call ceiling. The ratio decreases across these fixed cases; there
is no fitted asymptotic comparator claim or gating speedup goal. Hex checks an
explicit `PrimeCert` leaf while PARI uses its own below-64-bit integer terminal
convention and a different certificate representation. These ratios describe
that contract difference too. The optional
[verification plot](figures/hex-ecpp-comparator-supplied-certificates.svg) reads
those same records (`python3 scripts/plots/hex-ecpp-comparator.py --family supplied-certificates`).

The full Pocklington/ECM route comparison is **construction capability**,
not verification latency. [native/README.md](ecpp/native/README.md),
`campaign-updated.json` and `validation.json` retain all budgets, subjects,
seeds and source versions. Across the two frozen corpora there are 27 complete
kernel-replayed native successes in 32 cases and seven 256-bit capability
gains over the full construction route. [audit/native-corpora.json](ecpp/audit/native-corpora.json)
reconciles the complete current certificates and all exhausted outcomes.
No new measurement of the unchanged construction comparator is needed.
These 128/256-bit results do not establish success for all admitted subjects.
The separately frozen 512-bit extension is measured below. Scalar/parser synthetic families have no
same-contract external ECPP endpoint; their independent cost derivations and
oracle conformance serve separate purposes from PARI certificate validation.

## Profile

The current representative profiles use source `2aca3251099eab227c9a69d74370a3673720b659`.
Run `python3 scripts/profile/ecpp.py --output <record> --profiler-root <checkout>
--scalar-bits 1048576`; the record
[profiles-current.json](ecpp/audit/profiles-current.json) retains every perf,
samply, normalization/filter and attribution command, versions and raw paths.
The profiler source is `9356baa2f5757ee40320a897bd284914d5bb9f5e`; perf samples
cycles at 999 Hz, samply imports them, and the standard filter retains only
the timed regions on the benchmark thread. All four calibration and timestamp
sensitivity checks pass. Raw captures remain at the recorded `/tmp` paths;
the normalized summaries and their digests are committed.

| Family / target / parameter | Own code (%) | GMP (%) | Allocation (%) | Lean runtime (%) | Other (%) | Summary |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| transcript / `runReplay` / 1,048,576 | 1.85 | 92.87 | 5.05 | 0.06 | 0.16 | [transcript](ecpp/audit/profiles-current-profile-transcript-length.json) |
| rows / `runParse` / 4,096 | 13.12 | 0 | 55.71 | 25.61 | 5.57 | [rows](ecpp/audit/profiles-current-profile-row-vectors.json) |
| supplied / `runConvert512` / frozen 512-bit vector | 2.63 | 43.18 | 41.44 | 7.50 | 5.25 | [supplied](ecpp/audit/profiles-current-profile-supplied-certificates.json) |
| native / `runNativeHard` / validation-256-7, seed 7 | 1.84 | 42.74 | 45.12 | 6.87 | 3.44 | [native](ecpp/audit/profiles-current-profile-native-production.json) |
| scalar/modulus / `runSizedProposal` / 512 bits | 1.74 | 40.43 | 46.81 | 8.31 | 2.70 | [widths](ecpp/audit/profiles-widths-final-profile-scalar-modulus-widths.json) |
| scalar/modulus / `runSizedReplay` / 4,096 bits | 0.34 | 93.11 | 5.80 | 0.40 | 0.34 | [replay widths](ecpp/audit/profiles-replay-widths-final-profile-scalar-modulus-replay.json) |

The width profile uses source `e893b9f15c45f5cb1366ab6bd14858ce92568a8e`:
`python3 scripts/profile/ecpp.py --only scalar-modulus-widths --output
reports/ecpp/audit/profiles-widths-final.json --profiler-root <checkout>`.
[profiles-widths-final.json](ecpp/audit/profiles-widths-final.json) retains
commands, source/binary digests and passing filter diagnostics. Extended
Euclid accounts for 90.43% inclusive samples, directly connecting the
published bound to the dominant timed proposal phase. It complements the
fixed-modulus bit-copy profile and complete converter/search profiles.

The checked replay profile independently covers the two replay upper-bound
registrations: `python3 scripts/profile/ecpp.py --only scalar-modulus-replay
--output reports/ecpp/audit/profiles-replay-widths-final.json --profiler-root
<checkout>`. [profiles-replay-widths-final.json](ecpp/audit/profiles-replay-widths-final.json)
retains source `929c1d4f1` plus the recorded working-tree profiling case
(committed in `690326b85`), executable/core digests and passing filter diagnostics.
The profiling label is the replay phase of `scalar-modulus-widths`.
GMP accounts for 93.11% of leaf samples: multiply/subtract-multiply primitives
contribute 33.23%/22.81%, with quotient/remainder and basecase multiplication
also visible. Toom-2 multiplication and divide-and-conquer division appear
too; these faster regimes remain below the cited quadratic upper bounds. Thus the cited multiply/divide bounds cover the dominant timed
arithmetic. Allocation is 5.80%; each addition allocates boundedly many
k-bit residues and arithmetic temporaries, also below the quadratic per-addition
bound. The fixed-scalar modulus wrapper executes the identical callback with
fewer additions; the diagonal registration adds at most 2k such operations.
Neither replay callback computes an inverse. Assembly stack unwinding omits
many caller frames, so this profile supplies leaf attribution rather than
inclusive caller coverage; the passing timed-region filter selects the
benchmark thread independently of stack depth. All prior profiles remain applicable
to unchanged timed operation bodies, as recorded by `evidence-reuse.json`.

Inclusive percentages overlap and must not be summed. Dense scalar replay is
100% inside `replayBits`; GMP suffix copying explains its compiled quadratic
cost, while checked addition occupies 2.15%. Parsing is 98.22% inside
`parseLocated`, including allocation and JSON/list runtime work; `parseRow`
accounts for 18.01%. Both phases belong to the registered parser target.
Supplied conversion's dominant inclusive entry is `HexArith.extGcd` (75.87%),
then `convert` (50.36%), `convertRow` (47.70%) and scalar proposal (43.08%).
The shared arithmetic dependency already benchmarks extended GCD; proposal and
conversion targets here include its workload at fixed modulus and real large
moduli respectively. Native search (79.37%) is dominated by point scalar
proposal (68.81%), already separated as a target. CM proposals and terminal
construction also have fixed targets. No dominant timed phase is left outside
the inventory. Allocation percentages explain retained integer/list traffic;
they do not constitute a correctness or asymptotic failure.

## Retained runs

Completed unsuccessful runs are retained, with their limited evidentiary roles explicit:

- `scientific.json` and `scientific-final.json`: eager native fixture startup
  polluted the spawn floor. Lazy replay fixture warmup fixes that instrumentation.
- `scientific-bignum.json`: an earlier scalar schedule did not expose the full
  bignum regime. The initial linear declaration was independently disproved by
  the prescribed bit extraction's source, not replaced by a fitted exponent.
- `scientific-scalar-final.json`: replay's process cap omitted its potentially
  long fixture preparation and one call. Its killed sample and inconclusive
  result remain retained; the enlarged operational cap and full current run
  supply the passing replay evidence. The passing proposal run is reused.
- `profiles.json`, `profiles-perf.json`, `profiles-remaining.json` and their
  summaries retain the initial sample-import/calibration attempts. Current
  perf-import profiles cover every family with passing filter diagnostics.
- `regression-current.json` collected all samples, then its initial
  postprocessor incorrectly required Boolean hash one for the parser's row
  count. Corrected paired hash checking derives the retained summary without
  rerunning successful measurements.

- `scientific-gmp.json`, `regression-gmp.json` and `profiles-gmp.json`
  retain the signed-integer inverse attachment experiment. Its compiled C
  fallback lacks a GMP GCDEXT reference, as shown in `inverse-backend.json`.
  Adjacent ratios for 65/256/512-bit conversion are 1.571/1.152/1.124 and
  native 128/256-bit production 1.296/1.355 against the common bootstrap.
  The original natural-number recurrence is restored, reusing its passing
  evidence rather than retaining this slowdown. The experimental proposal's
  `k³ log k` declaration cited the wrong backend and cannot certify the final
  operation. Fresh proposal/modulus runs use the classical Euclid bound.
  The checked replay callback and its canonical prime-field inputs do not
  change with the preparation backend, so that passing upper-bound export
  retains its specific evidentiary role.
- The two fixed-modulus scalar rows in `scientific-widths-final.json` were
  collected under quadratic upper bounds through 4,096 bits and already
  showed linear scaling. That declaration was a loose upper bound for the dominant bounded-width
  Euclidean/ring work in this range. The corrected model follows the source
  operand limits, and uses the actual 32–512-bit caller regime.
  Fresh mode-1 samples in `scientific-caller-final.json` certify it; the old
  observations are retained without relabeling.

Earlier records are observations, not retroactively passing verdicts. The
successful current ladders and declared budgets are the Phase 4 evidence.
Shared-host variation, synthetic fixed-modulus scalar scope, finite native
capability and different PARI terminal contracts are explicit practical limits.

## Concerns


## Explicit 512-bit native production

The `native-production` family now includes the independently generated 512-bit
corpus and frozen finite policy in [native512/README.md](ecpp/native512/README.md).
The eight-case holdout has four genuine ECPP successes (17–20 elliptic steps),
against exhaustion of full current construction including ECM on all eight.
Every accepted certificate has independent arithmetic/prime checks and fresh
kernel replay; the actual elaborator separately confirms construction exhaustion.
All unsuccessful native outcomes, raw outputs and adjacent NC/CN timings are
retained. These are capability gains, not a claim of complete 512-bit coverage or
a same-result construction latency comparison. Default 256-bit dispatch is unchanged.

| Fixed endpoint | Median ms | Declared budget ms | Result |
|---|---:|---:|---|
| `runNative512` | 1560.326 | 5000 | pass |
| `runNative512Convert` | 142.405 | 300 | pass |
| `runNative512Check` | 28.417 | 80 | pass |

Five repetitions on the shared host, selected CPU and source digests are retained
in [endpoints-v2.json](ecpp/native512/endpoints-v2.json). Conversion and checking
use the warmed complete holdout ordinary-0 certificate. The full-corpus driver
also records compact/expanded output rendering separately from these operations.
The representative [512-bit profile](ecpp/native512/profile-v2-profile-native-production-512.json)
has 7820 samples with 96.92% classified: GMP 56.74%, allocation 32.23%, Lean runtime
6.79%, Lean own code 1.16%, other 3.08%. Order factorization and scalar proposals
account for 35.49% and 27.31% inclusive samples respectively; inclusive shares
overlap. This attribution supports the existing arithmetic and factorization
cost model; it does not justify automatic dispatch.

[regression-v2.json](ecpp/native512/regression-v2.json) retains four adjacent AB/BA
trials over every existing 128/256-bit subject. Results, certificates, original
resource counters and random states agree exactly, with median search ratios
1.002 and 0.999. Shared-host variation is retained without discarded samples.
The computational implementation and allocations were frozen before any holdout
arm; later public reification uses raw natural literals to fit the unchanged
syntax ceiling, without changing search. Public fresh-module generation/replay
timings and the initial rejected representation are retained alongside the core
measurements and are distinct from compiled search/check/convert timings.

The companion proof track separately measures reification and fresh kernel
replay in [proof-phases-timed-v2.json](ecpp/native512/proof-phases-timed-v2.json).
Four fixed trial-major schedules give 44.150 ms median for
reification plus type inference and 45.961 ms for replay preflight
(including its own reification). The complete fresh proof module takes
17.619 s median, versus 3.820 s for matched import/numeral
baseline; those wall observations include Lake and import overhead. All samples
are retained, including the earlier uninstrumented schedule.
