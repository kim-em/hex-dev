# Real-closure Phase 4 evidence

## Compiled MetiTarski functional validation

The input is the degree-15 polynomial from section 4 of
[de Moura and Passmore, CADE 2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf),
followed by `Y³ + x³ + 1` over its least real root `x`.
`bench/HexRealClosure/Phase4.lean` runs the actual native complete-root API
and the canonical real-algebraic backend on these same inputs.
It flushes every completed stage, checks root equations and multiplicities
after isolation, and reports construction of `x³ + 1` as a separate stage.
The independently verified interval `(-1875/2048, -1875/4096)` selects the
least root. The historical runs below precede these explicit stage and
selection checks.

[Retained outputs and metadata](bench-results/real-closure-phase4-functional/)
identify the exact source, executable hash, automatically leased CPU, host,
start and end times and operational timeout. Every completed or interrupted
arm is retained. These runs validate the workload; they are not a fixed
trial-major scientific comparison.

The native arm completed in 5.52 seconds on the shared host. Its first
isolation returned three roots and took 4.98 seconds; the second returned
one root and took 0.150 seconds. Both equation and multiplicity checks passed.
The canonical backend arm reached the 1800-second operational cap. Its stdout
was buffered and empty when the process was terminated, so the last completed
stage cannot be established from that output.
This timeout is a censored observation, not a completed timing sample or a
quantified speedup. No rerun of that tagged executable has been collected.
Its second-isolation window excluded construction of `x³ + 1`; that setup was untimed in the
historical run.

### Flushed and build-bound functional runs

The retained `flushed-native-d84e506` run checks the least-root interval and
reports coefficient construction separately. It completed in 5.47 seconds;
first isolation took 4.94 seconds, construction 0.00372 seconds and second
isolation 0.149 seconds. Its source is preserved by
`issue-10378-phase4-flushed-source`.

The `build-bound-native-91bcb67` and `build-bound-canonical-91bcb67` runs
also retain a successful build log and its hash. Both use the executable
SHA-256 `d5b10c63a1edaa05a05459415cea7b225834788276b9493d0a01f721795c9bad`
from source `91bcb67124367f70d24c607371eb017b80237560`, preserved by
`issue-10378-phase4-build-bound-source`. The native run completed in
7.08 seconds: first isolation 6.51 seconds, construction 0.00399 seconds,
second isolation 0.160 seconds. All root-selection, equation and multiplicity
checks passed.

The `snapshot-native-7b63305` run executes a retained copy of the hashed
binary, records Lean 4.35.0-rc3 and Lake 5.0.0-src, and completed all checks
in 5.47 seconds. Its source is preserved by
`issue-10378-phase4-snapshot-source`. The copied executable remains at
`/home/kim/.codex/tasks/hex-10378/phase4-snapshot-native/hexrealclosure_phase4`;
the committed archive retains its hash, build log, metadata and output.
The flushed, build-bound and snapshot native runs execute the same binary
`d5b10c63…`; their 5.47, 7.08 and 5.47-second observations record shared-host
variation on byte-identical code, rather than a source-change effect.

The canonical run completed first isolation in 40.26 seconds, returned
three roots and passed the least-root interval check. It then reached the
1800-second cap before the coefficient-construction stage completed;
metadata records signal 9 and exit code −9. This localizes the unfinished
work to construction of the second polynomial, rather than its isolation.
The canonical construction uses generic real-algebraic multiplication and
exactification: products of the degree-15 operands can form degree-225 product
eliminants before exact factorization. The native construction instead reduces
inside `ℚ(α)`. Consequently the retained canonical arm supplies no second
isolation measurement. The 91bcb67 build logs show Lake's target was up
to date at a clean source commit. The 7b63305 snapshot log records compilation
of the Phase4 driver and executable against cached dependencies. Neither
build recompiles the dependency graph from an empty cache.
These are retained functional observations from a shared host, including
changed apparatus and censored execution. They are not a scientific timing
comparison or a quantified speedup.

The unprofiled native run of the profiled binary spends about 90% of its
5.52-second process time in first isolation over `ℚ` (4.98 seconds). The
build-bound native run spends about 92% there. The preliminary whole-process
profile therefore mostly describes this base-field path. It provides little evidence
about the algebraic tower stage. The separately filtered first- and
second-stage attribution is retained in the
[MetiTarski root-operation profiles](bench-results/real-closure-metitarski-kernels/).

## Preliminary native profile

[Retained profile metadata and reports](bench-results/real-closure-phase4-native-profile/)
cover one compiled native MetiTarski run, at 99 Hz `cycles:u` with
8192-byte DWARF call stacks. The exact compiled source is
`b2cea573a742a279dc07e8626f64b570c19d0c2e`; the binary SHA-256 is
`3edbc3503a26592c2dc36410d5a30e81d571306aa4a835d997c90154578a62af`.
The source is preserved by the upstream tag
`issue-10378-phase4-profile-source`. The measured repository at
`2a20b4e3c0d6725a3bec38e88aa92ea625390a59`
adds only evidence files to that source; its driver and Lake configuration
match the compiled source. The current driver includes later stage checks. Both stages
and the equation/multiplicity checks completed.

The profile retained 539 samples and reported zero lost samples. The largest
exclusive symbols were GMP half-gcd (`__gmpn_hgcd2`, 14.68%), `div2`
(9.90%), `malloc` (8.82%), and GMP gcd (`__gmpn_gcd_11_x86_64`, 5.81%).
The retained leaf categorization assigns 53.72% to GMP arithmetic (including
`div2`) and 30.50% to allocation; 8.63% lies below the report's displayed
threshold. These exclusive samples show substantial exact rational arithmetic and
allocation cost. Stack unwinding did not recover reliable inclusive Hex
callers. This whole-process profile includes untimed checks and uses 99 Hz;
it does not satisfy the filtered 1 kHz LeanBench/Samply profile contract in
`SPEC/profiling.md`. They do not separate the two isolation stages or supply exact
operation counts. Sampling percentages describe this one shared-host run.

The 4,833,596-byte raw profile is retained at the local path and SHA-256
recorded in metadata (`2ecc4899ef1b3b7c7f2d0cf98c23a19d739a3be2d673d64d4aa9e1ff751da14d`).
The historical gather profile with missing exact source provenance is not
used for this attribution.

## Exact workload provenance

The retained independent checks use python-flint 0.9.0 to establish that
the MetiTarski degree-15 polynomial is irreducible and squarefree. An exact
rational Sturm sequence finds three real roots and verifies the least-root
interval, with no root below it. Reproduce these checks with
`python3 scripts/oracle/real_closure_phase4_inputs.py --paper PAPER.pdf`
in an environment with the pinned versions. The checker verifies the supplied PDF hash; the formulas
were manually transcribed and checked against section 4, PDF page 14.
`input-checks.json` records this checker's hash and is the current input
verification; `workload-checks.json` retains the earlier, narrower check.
Retain a new compiled functional run with
`python3 scripts/bench/real_closure_phase4.py native NEW_OUTPUT_DIRECTORY`
(or `canonical`); the runner requires a clean checkout, retains a successful
`lake build hexrealclosure_phase4` log, refuses to overwrite evidence and
copies the built executable into that directory, hashes and executes that
snapshot, and records Lean and Lake versions, CPU model, OS, kernel, source
commit, binary hash and termination signal. The output directory must be
outside the checkout; copy the metadata, logs and output into the report
archive afterwards. Lake validates its cached input hashes, including artifacts
restored from other worktrees; the retained build is not a fresh compilation.
Z3 4.15.4 checks the printed first `tower8` polynomial under `0 < ε < 1`.
The paper prints a constant term `4 − 2ε² + 4`, giving

`P(x) = (x² − εx − 2)² + 4 − 2ε²`.

It has no real root for `0 < ε < 1`; the exact Z3 check is unsatisfiable.
The paper PDF SHA-256 and formula are in the retained checks. The original
CADE 2013 scripts have not been recovered from the pinned Z3 source trees.
No corrected polynomial or replacement workload is assumed here.

## Short product-chain normalization comparison

The [retained matched clean/eager comparison](bench-results/real-closure-normalization-d73e2f/README.md)
checks four Rat-extension sizes, all 64 arithmetic prefixes and 48 timed arms
from a preregistered fixed schedule. Both storage policies use one prepared
root and the same native packing. The non-monic head disables production monic
reduction, so clean follows that unreduced production regime. Eager was faster in every paired trial for
this short family. The archive retains actual stored/query coefficient growth,
source and executable bindings, exact independent checks and all command outputs.

This family has one extension and 2n linear-seed products, eager denominators
at most 4, and direct Sturm queries; degree 2 takes the linear endpoint fast
path. These observations do not determine a normalization policy or satisfy
whole-tower normalization, scaling, operation-counter or time-budget coverage.

## Nested clean/eager measurements

The [nested matched comparison](bench-results/real-closure-nested-measurement-ca2e22/README.md)
retains all 96 adjacent AB/BA arms from six fixed trial-major trials, at depths
one and two and product counts 2, 4, 8 and 16. Every arm computes
`(1 + alpha_d)^m / (alpha_d - 3)` in the actual validated tower with heads
`(2X^2 - alpha_(d-1))(X - 3)`. All sixteen endpoints pass native checked
reading and root/query replay, and eight paired FLINT exact-value checks.

Each arm reduces or retains representations at every level and builds its
own lower-level evidence. The depth-two ratios and evidence sizes therefore
include those lower-level effects as well as top-level storage.
These nonmonic heads disable production monic reduction. Clean packing keeps
nonzero representatives unreduced; eager reduces against the full working
cubic, including its extraneous root 3. This comparison does not measure
production reduction under monic clean heads or a minimal quadratic policy.
Both arms exercise the nonconstant inversion gcd split; these data do not
isolate storage policy, a smaller defining polynomial after splitting and an
irreducibility fast path from one another.
The timer includes product/division, recursive arithmetic and packing's
selected-root queries, plus encoding and hashing the result. Context setup,
final query evidence, checked reading and replay occur outside timing.

At depth one with two products the paired direction is mixed. Eager is lower
in all six pairs of every other parameter combination. At depth two, the
paired eager/clean median falls from 0.134639 for two products to 0.039732 for
sixteen. The largest endpoint retains 765/221 stored bytes and
6,211,399/17,869 final-query bytes for clean/eager. Final evidence is produced
outside timing; these sizes do not measure its construction or replay cost.
The linked archive retains all medians, ranges, coefficient degrees and bits,
source/binary identities, raw points and host activity. These are finite
family observations and do not determine a global normalization policy.

The separate [generated-C diagnostics](bench-results/real-closure-nested-diagnostics-c7d917/README.md)
retain callback counts, polynomial gcd/xgcdLeft entries and Lean/GMP integer
gcd entries. For depth two and four products, both policies enter polynomial
gcd and xgcdLeft 23 times each, while clean/eager enter integer gcd
248,512/82,295 times. Callback categories also nest: division invokes
multiplication and inversion, and inversion invokes gcd/xgcd sites; do not
sum these categories. Lean and GMP count different layers of the same calls;
they must not be added. Counts exclude setup and final evidence production,
and omit the fast polynomial `*With` entries. The traced depth-three clean
preparation hit its 600-second cap before entering the counted workload.
That retained interruption supplies no clean depth-three expression timing
or matched depth-three comparison.

## MetiTarski second-stage scaling

The [degree-ladder protocol and results](bench-results/real-closure-metitarski-scaling/README.md)
measure complete roots of `Y^n + alpha^3 + 1` for n = 3, 5, 7, 9 in the
fixed selected degree-15 predecessor field. Degree three is the exact paper
second input; the higher degrees are a derived family. Setup and an untimed
warm-up precede the measured action. The timer includes complete root
production, its count check, runtime input-prefix extraction/normalization
and the harness consumer; functional equations, serialization and replay
are outside timing.

All 24 points from six fixed trial-major rounds completed and are retained.
Median milliseconds are 213.826, 469.475, 731.902 and 1299.439; corresponding
`time/n^3` values are 7.919, 3.756, 2.134 and 1.782 ms. Descriptor bytes grow from
21,688 to 204,318. The harness verdict is `inconclusive`, with log-log slope -1.404948 for
`time/n^3` against n and no dropped leading points. A finite degree range and substantial fixed
cost do not establish asymptotic complexity. Observed time grows more slowly
than n³ over this finite degree ladder; the operation runs faster than declared. Its registration does not identify that
hypothesis as an independently derived model or a cited bound. This capture
does not satisfy the Phase 4 exit criterion; its declaration, family and
calibration need investigation under the
[benchmarking policy](../SPEC/benchmarking.md#anti-patterns).
The cause has not been classified as an implementation bug, declaration error
family mismatch or schedule miscalibration. Each requires the policy's corresponding response.
Any declaration correction needs an independent counterexample and cost-model
derivation before collecting new measurements, retention of the old declaration
and every sample, and fresh validation. Choosing exponents from observed slopes
is verdict-fitting; relabelling a hypothesis as a cited bound is also a
declaration change.
It cannot turn this earlier inconclusive capture into a pass.

The signal-floor multiplier is 1 rather than the ordinary 10. 22 of 24 measured batches
fall below the ordinary floor. Child-side inner timing avoids
charging spawn time to the operation, but the multiplier-1 exception requires
rungs fixed by the library SPEC. That condition is unmet: the SPEC does not
fix this derived 3/5/7/9 ladder. A permitted unchanged rerun would repeat this
unqualified registration and would not resolve that policy gap. The next
protocol must establish eligibility independently of the observed timings,
or use the ordinary floor and an appropriately raised schedule, with fresh
validation. Wide ranges and recorded changing host activity also limit
inference; every observation is retained.

The [complete retained capture](bench-results/real-closure-metitarski-scaling-14b03f/README.md)
binds the measured source, all raw timings, seven frozen source snapshots,
functional and measured-input packets, and independent FLINT checks of the
selected predecessor, coefficients, unique odd-radical root, interval,
Thom word and reported multiplicity. The exact negative radical and
closed-form derivative signs establish multiplicity one. Scientific timing is separate from CI's native
fixture/replay and independent oracle checks.

## Measurement coverage and remaining work

These deliveries supply specific evidence; the library's Phase 4 readiness
still requires the complete specified coverage and final audit.

| Required evidence | Retained coverage | Remaining scope |
| --- | --- | --- |
| Exact archived tower workloads | MetiTarski degree-15 input and cubic second stage transcribed from the paper and independently checked | Script-level `basic.py`/`nlsat.py` provenance and original Rioboo/Strzeboński inputs; authoritative `tower8` correction/archive, its isolation, zero/sign-test counts and the required counters |
| Fixed trial-major scaling | Six trials at four odd degrees in one fixed MetiTarski coefficient field | Investigate the inconclusive verdict, declaration/family and unmet floor-exception condition; a qualified protocol/model needs fresh validation; remaining required input/depth families |
| Matched clean/eager storage | 48 single-level arms and 96 depth-one/two product/division arms | Repeated nested zero-test costs; distinguish storage policy, smaller defining heads after splitting and an irreducibility fast path; other required families and monic-clean production reduction |
| Coefficient and evidence growth | Stored degrees, bytes and coefficient bits; selected/query graph bytes in those families | Remaining families/stages and certificate operand sizes |
| Operation/query counters | Nested callback and selected polynomial/integer gcd diagnostics | Scalar inversions, gcd/xgcd, splits/transports, bound attempts, bisection nodes, BKR queries/matrix work and coefficient-sign and zero-test calls across the required families |
| Outer isolation scaling | Functional isolation/policy checks | Counter evidence consistent with the stated linear bounds; full fallback, joint comparison and transport costs |
| Root/generator reuse | [Reuse report](real-closure-root-reuse.md): two-trial reuse/order diagnostics from recorded modified worktrees | General required tower families and final correspondence to accepted APIs; these observations do not measure certificate DAG sharing |
| Certificate sharing and depth | Functional DAG reading/checking | Bytes/nodes/edges versus unshared occurrence costs, arithmetic/operand sizes, cycle/forward-reference rejection before expansion, `Sℓ ≤ Sℓ,local + bℓ*max Sℓ₋₁` and the analogous replay-time recurrence |
| Separated compiled stage costs | Functional reading/replay and whole-command observations | Yun, query production, BKR solving, coefficient signs, isolation, serialization and kernel replay; whole-command success is not a separated timing distribution |
| Trivial-path delegation | Native/canonical agreement, `TrivialTests` and independent FLINT conformance; retained canonical MetiTarski arm is censored | Required matched comparison against the existing real-algebraic backend |
| Midpoint/dyadic versus infinitesimal samples | Functional sample APIs and conformance | Required matched measurement evidence for those alternatives for #10301 |
| Profiling diagnostics | [Filtered first/second-stage profiles](bench-results/real-closure-metitarski-kernels/README.md) explain observed sorting/sign costs | No per-family profiling quota; profile unexpected verdicts, surprising constant factors or unexplained dominant costs outside registered targets |

The accepted filtered profiles supply inclusive Hex attribution with clean
committed postprocessing and recorded stack truncation. The preliminary
whole-process profile and historical gather profiles with missing source
provenance do not supply that filtered contract. Ordinary-kernel correctness,
compiled functional checks and scientific timing have distinct boundaries;
none substitutes for the missing tower8 correction or unfinished coverage.
Profiling diagnoses observed costs; it is not a separate phase deliverable.
