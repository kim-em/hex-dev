# Tower factorization comparison protocol

The hypothesis is that exact rational Euclidean squarefreeness tests inflate
Trager's cost through intermediate coefficient growth. A successful modular
squarefreeness certificate can replace those tests; an unsuccessful trial must
retain the exact fallback. Reconstruction, multiplicities, canonical ordering,
and recursive irreducibility checks remain required.

This experiment uses the existing fixed registrations in
`bench/HexNumberFieldTower/Bench.lean`. It makes no parametric complexity claim
and fits no exponent to timings. The canonical factorization and certificate
replay retain their registered mode-3 budgets of 2 seconds. The six fixed
Selmer comparator rungs (degrees 2, 3, 4, 6, 8, 12) measure constants only.
The headline report explains why the composite algorithm has no independently
derived tight wall-time model; this experiment does not change that assessment.

Before/after measurements use lean-bench on `chungus2`, CPU 13 (selected by
`scripts/bench/idle_core.py` before measurement), with five repeats,
`--min-total-seconds 0.2`, and the registered warmup. Save the baseline binary
before changing executable sources. Run the baseline and candidate on the same
CPU, without overlapping builds or timing runs; record CPU/sibling idle samples
and preserve the complete harness export and source commits. Compare all six
fixed rungs and both canonical degree-24 operations, including result hashes.
The existing PARI comparator remains informational; record fresh PARI pairs and
the protocol-overhead control if the provider is available. Do not compare new
Hex times directly with historical PARI measurements.

Inspect the rational squarefreeness calls and intermediate coefficient heights
to attribute any reduction. An unchanged unsuccessful modular trial must still
reject repeated factors and handle primes dividing the leading coefficient or
discriminant. Verify those branches, rational denominators, the public
factorization/checker regressions, and the Mathlib correspondence proofs.

These local measurements establish before/after constants, not a replacement
release-quality shared-host verdict or a change to Phase-4 coverage.

An attempt whose postflight sample finds the measured CPU or its sibling at
least 5% busy is retained as a contaminated diagnostic. Allow at most two
retries with the same settings; rerun both binaries and PARI in each retry.
The first retry uses CPU 13 with sibling 61. The final retry uses CPU 1 with
sibling 49, selected idle before this amendment because CPU 61 has acquired
an independent profiling workload. Both binaries move together; this changes
the placement, not the inputs, repeat count, budgets, or acceptance threshold.

Preregistration provenance: `b8602c76a` fixes the model and measurement schedule.
The environmental policy was amended after rejected measurements:
`20ff1f2f9` specifies the retry allowance and 5% postflight threshold after the
first attempt; `0faa834dc` specifies CPU 1 for the final retry after the second
attempt. These amendments do not retrospectively qualify any timing result.

## Follow-up comparisons

A new local comparison series uses the same fixed inputs, five repeats,
0.2-second batch floor, warmup, and unchanged mode-3 budgets. The original
baseline binary has SHA-256
`9cda578dbc8724ea9c10462c1c6e2ccbaf6d48e6a85ef291a2f1bf7e4c5df810`;
the merged modular-check binary has SHA-256
`ff0dc3dfce3582d45dc7fa7e8bb5cb5b92fa1cca37dc3282c929d0c568b8f0df`.
This series also measures independent norm-construction and recovery variants
against the merged implementation, then their combination if both improve.
The norm hypothesis is that a descending Horner fold avoids materializing
all ascending powers and multiplying them by each lifted coefficient.
The recovery hypothesis is that exact divisibility or a single irreducible
norm factor permits avoiding unnecessary gcd or shift work. These are fixed
input constant comparisons; no exponent is inferred from timings.

Each comparison selects an idle physical core with `idle_core.py` before
starting either arm, records its logical CPU and SMT sibling, and uses that
same placement for both binaries and fresh PARI calls. No build or profiler
from this session overlaps a measurement. Record two-second preflight and
postflight samples for each arm and sample sibling utilization during each
arm. Reject an arm if its pre/post CPU or sibling utilization is at least 5%,
or mean sibling utilization during execution is at least 5%. Preserve every
attempt, including rejected results. Retry the whole pair, never one arm,
at most twelve times; choose a new idle core before each retry. Host telemetry
alone determines rejection, never a timing value. These comparisons remain
local shared-host evidence, not release-quality performance verdicts.

Retain an optimization only when all result hashes match, correctness proofs
and conformance pass, the canonical factor/check medians improve in two
accepted paired comparisons (alternating arm order), and no fixed rung has a
repeat-range-disjoint regression. Retain an inconclusive variant as measured
investigation evidence rather than wiring it into the factoring path.

The combined variant is compared both to the merged modular-check executable
and to the original executable, with the same two accepted opposite-order
pairs and the same admission rules. The latter comparison measures the total
improvement directly rather than multiplying speedups from separate runs.

### Quiet-preflight replication

If a shared-host burst prevents selecting any idle core, that is an
unavailable environment, not a negative verdict on an implementation.
A further replication uses the same binaries, fixed cases, repeats, warmup,
2-second budgets, opposite pair orders, and 5% admission thresholds. It
selects physical cores whose lowest logical CPU is at least 24 on `chungus2`,
to avoid competing with other automatic selectors that prefer low indices.
Before the first arm of a pair it waits up to 15 minutes for a two-second
quiet CPU/sibling sample, recording every preflight window. A busy second-arm
preflight still rejects the whole pair. At most twelve timed pair attempts
are allowed per comparison; a preflight timeout produces an explicit partial
artifact. This environment amendment applies only to the new replication;
none of the interrupted earlier variant measurements is admitted afterward.

### Monic normalization variant

A further fixed-input hypothesis is that returning an already-monic polynomial
unchanged avoids a tower inversion of one and a coefficientwise scale by one.
Compare this shortcut against the combined Horner/recovery executable
`8d54c7158`, using the eight Hex registrations, five repeats, the same warmup
and batch floor, and two accepted opposite-order pairs. The unchanged PARI
registrations are omitted from this isolated comparison to shorten each
exposure window. Retention uses the same hash, canonical-median, and
repeat-range criteria. The final comparison against the original executable
includes fresh PARI and overhead measurements. The monic shortcut must retain
the existing zero and nonmonic behavior and all certificate guarantees.

The reusable runner is [tower_factor_compare.py](../scripts/bench/tower_factor_compare.py).
Supply the registered interpreter with `--pari-python` (or the explicit
`HEX_PARI_BENCH_PYTHON` environment variable). It records Python, cypari2,
and PARI versions and fails before timing if the provider is unavailable.
It validates every named case, all five raw repeats, hashes, warmup, budgets,
and derived timing summaries, then writes a series decision. Decision
validation also requires accepted host pairs, the same source and executable
for each arm across pairs, and opposite arm orders. Incomplete
series retain their accepted pairs and have no retention verdict. Full
preflight snapshots are retained to make unavailable-core decisions auditable;
the high-index placement is a heuristic, not a reservation against other work.
This runner is scoped to this issue's host and fixed protocol. It fails closed
on an invalid export or preflight timeout and refuses to overwrite a series;
its partial artifacts remain available without an automatic resumed verdict.

### Integration comparison

The integrated Horner/recovery implementation at `2ae8157bc` includes the
upstream `natDegree` API rewrite. Although that accessor is an inline
abbreviation for the former expression, the rebuilt executable differs, so
compare it directly against the original `b8602c76a` executable in a new
`rebased` series. Use all fifteen fixed registrations, including fresh PARI
and overhead calls, with the same five repeats, batch floor, budgets,
quiet-core policy, twelve-attempt limit, opposite pair orders, and retention
criteria. The candidate SHA-256 is
`c3e2de0cb83c2ab3e7fb68997c06778ed8a2369f63c4f21878ec88d7ce3c10a6`.
The tag `bench/issue-10074-measured` preserves all pre-rebase source commits
and preregistrations referenced by the earlier artifacts.

## Singleton recovery and quadratic norm experiments

The [fresh profiles](hex-number-field-tower-performance.md#factorization-after-norm-and-recovery-improvements)
identify two independent targets: recovery including shifts (about 26% of
factorization), and shifted norm construction plus resultants (about 52%).
These shares motivate experiments; they are not predicted speedups. The
execution order is **prototype, differential checks, timing decision, then
correspondence proofs**. No prototype is eligible to merge before its proofs
and final verification pass.

### Baseline and independent prototypes

Use the computational source at `af7b4d49f661a23debf82960bfff3c78435ff135`
as the common baseline for both prototypes. Its saved benchmark executable is
`/tmp/tower-factor-profile-af7b4d49f/hexnumberfieldtower_bench`, SHA-256
`038b21ce95e7a3c2571d869347206ca3ab4e049633ca700490af9937d7c20b2f`.
Record candidate source commits and saved binary hashes before measuring.
Keep each prototype isolated from the other and from unrelated upstream
runtime changes. Any necessary baseline change requires a new recorded
baseline before candidate measurements.

1. **Singleton recovery.** In `Factor.factorSquarefree?`, after the accepted
   norm has been recursively factored, use the singleton case to return the
   canonical monic input component instead of calling `Factor.recover`.
   Retain squarefreeness, recursive norm factorization, reconstruction,
   positive-degree, and public certificate checks. Do not put an unconditional
   singleton shortcut in `recover`: an arbitrary one-element lower-factor
   array does not establish that it factors the accepted norm. Empty and
   multiple-factor cases keep the existing recovery behavior.
2. **Quadratic norm.** Dispatch in `Norm.oneLevel` when the top defining
   polynomial has degree two; retain the current resultant path for other
   degrees. For `m(Y) = Y² + bY + a`, maintain `A(X) + Y B(X)` during Horner
   evaluation modulo `m`. Multiplication by `X - cY` sends `(A, B)` to
   `(XA + caB, XB - cA + cbB)`; add the two blocks of the next input
   coefficient afterward. Return `A² - bAB + aB²`. For `Y² - 2` this is
   `A² - 2B²`. This supports quadratic coefficients over a lower tower,
   rather than recognizing the particular Selmer fixture. Preserve canonical
   output encoding, shifts, zero/constants, and rational denominators.

Build prototypes through `lake build` on the Mathlib-free computational and
benchmark targets. During this stage the companion proofs may need updates;
do not replace them with axioms or sorries or count stale proof artifacts as
validation. First inspect the existing norm and recovery theorem statements
for a plausible proof route, but defer constructing those proofs until the
performance decision. A mathematical counterexample ends the candidate even
if benchmark outputs happen to agree.

### Correctness checks before timing

Compare against the reference implementation, not only against a checksum of
factor degrees. Require equality of the full canonical factorization output
and checker results, byte-identical conformance fixtures, and all 49 registered
benchmark checks with the explicit PARI provider. Check corrupted certificates
still fail. Exercise irreducible and reducible inputs, repeated factors,
nonmonic inputs, denominators, zero/constants, and a height-two tower.

For the quadratic norm, additionally compare the entire norm coefficient
array against the existing resultant on a deterministic grid of small inputs
with both generator-coordinate blocks populated, shifts `0, 1, -1, 2, -2`,
quadratic relations with nonzero linear term, and coefficients over a lower
quadratic field. Include nonquadratic fallback cases. Confirm the intended
fast branches actually execute in the public factor and replay benchmarks.

### Timing gate before proof development

Use the eight existing Hex fixed cases: degrees `2, 3, 4, 6, 8, 12`, canonical
degree-24 factorization, and canonical degree-24 replay. Reuse the five repeats,
0.2-second batch floor, registered warmup, unchanged canonical 2-second
budgets, quiet high-core placement, pre/postflight and sibling-utilization
thresholds, opposite pair orders, and twelve-attempt limit above. No local
build or profiler overlaps timing. Preserve every attempted export and its
telemetry; an incomplete series has no performance verdict. Fit no exponent.

Compare each isolated prototype against the common baseline. Advance to proof
development only if both canonical medians improve in both accepted pairs,
all hashes match, and no smaller rung has a repeat-range-disjoint regression.
For these new experiments, additionally require each canonical operation's
candidate maximum to be below the baseline minimum in at least one accepted
pair. This stricter effect-separation gate is fixed before measurement; it
does not revise earlier experiments or constitute a significance test. Extend
the artifact validator to enforce it before running these series.

If both isolated variants qualify, measure the combination against the common
baseline and against each isolated variant. Apply the same timing gate to
all three comparisons so that both changes must contribute when combined.
If an isolated or marginal effect is inconclusive, retain its investigation
artifacts and defer its proof work; do not relax the gate after seeing results.
Use Hex-only comparisons for the isolated and marginal experiments. The final
candidate-versus-baseline comparison includes all fifteen registrations,
including fresh PARI and its overhead control with the explicitly recorded
provider. Measure combined effects directly, not by multiplying speedups.

### Proof and integration stage

For each retained implementation, prove the singleton norm's implication for
component irreducibility and the correspondence of the returned canonical
factor, or prove the quadratic Horner invariant and exact norm identity,
respectively. Preserve the existing public soundness/completeness statements.
Build the tower Mathlib companion and rerun conformance, oracle, and benchmark
checks. If a proof obligation forces a runtime change, remeasure the changed
candidate before treating the earlier performance decision as final.

Record measured results and source provenance before opening the implementation
PR. Obtain the requested independent second opinion while CI runs, resolve
integration conflicts, and require green CI before merging. After any rebase
that changes the measured executable, validate performance on the integrated
binary again. The accepted prototype is a reason to invest in proofs, not a
substitute for them.

### Sustained-quiet marginal replication

The `combined-quadratic` series exhausted twelve attempts with only one
host-admitted pair (attempt 10), so it has no performance verdict. Preserve
the entire series. A fresh replication of this marginal comparison uses the
same saved quadratic and combined binaries (`af91cca87`, SHA-256
`28701e063ccb1667223fdd56eb899c84afc3571e3efd05a372a1f7822ce4c4d9`, and
`4209945bc`, SHA-256
`f6feab899807eb26da3310dd64497a203669505d0fa2c0d4eda3100f56576cf3`).

Before selecting a core for each attempted pair, require fifteen consecutive
two-second windows in which both the core and its SMT sibling are each below
5% busy. An absent CPU makes its core unavailable. Keep the fifteen-minute
preflight deadline and twelve-attempt limit per series. Between-arm preflight,
postflight, during-run sibling admission, same-core pairing, opposite orders,
all eight Hex cases, repeat counts, warmup, budgets, hashes, and the stronger
performance gate are unchanged. The runner's `--quiet-windows 15` selects this
stricter preflight; its default preserves the earlier protocols.

This is an environmental replication of an incomplete series, not an
extension of its attempt limit or a reclassification of any rejected arm.
Select the first two host-admitted opposite-order pairs without inspecting
their timings, and retain every attempt. Do not develop the combined
correspondence proofs until the complete marginal comparison passes.
