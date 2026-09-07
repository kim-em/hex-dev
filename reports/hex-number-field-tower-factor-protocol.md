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
