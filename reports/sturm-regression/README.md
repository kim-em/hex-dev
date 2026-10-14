# Sturm computational regression comparison

The Phase-6 question is whether the native computational paths carrying timing
claims regress against the most recent committed benchmark baseline. This is
separate from the owning issue's completed Phase-4 complexity and comparator
attestation. The [retained first comparison](../bench-results/sturm-phase6-comparison/README.md)
stopped at the largest `runRationalHigh` parameter on both source arms. Its
all collected data and the failure are preserved; it supplies no Phase-6 pass.
Only 12 of 58 families were attempted in block zero; 46 families and blocks
one through three never started.

## Scope and baseline

The proposed baseline executable is the retained native build of
`75fbfa04550ae0f76df074176f44bf0f2533334a`, identified by the source manifest in
`reports/bench-results/sturm-sign-comparisons/capture/after-source.json.gz`.
Decompress that JSON manifest before supplying it to the collector.
Its SHA-256 is
`55640ad98ad3cf2323b93922272b28fec5d0c093115cfd29df8e11590d6ddc57`.
The measurement accompanying that commit covered coefficient signing. Using
that committed source's executable for the other registered operations would
be a new computational baseline comparison; it would not turn the historical
sign capture into historical measurements of those operations. Before collecting,
freeze the clean candidate source and executable and record their exact bindings
in the campaign's decision file.

A source comparison against that baseline finds a computational change in
`HexPoly/Instances.lean`: polynomial powering now returns the input directly
at exponent one, also simplifying exponent two. The sign implementation has
also moved namespace. The comparison must not assume that the entire native
computational graph is byte-identical merely because the Sturm definitions
changed only in docstrings. Unrelated Mathlib/Tau Ceti pin changes are outside
this executable's computational import boundary.

The current executable registers 59 parametric families and 34 fixed controls.
The comparison selects the 58 parametric families with timing claims. The
auxiliary `Hex.SturmBench.runSigns` traversal has no timing target under the
existing [owner disposition](../hex-sturm-performance.md#verdicts); its retained
failed characterizations remain unchanged. The preflight smoke check includes that auxiliary family at the runner's
small inputs. Only the eight native fixed controls have declared expected
hashes; all timed rungs must additionally agree between the two source arms.
Hash agreement establishes agreement with the baseline, not independent
mathematical correctness of every timed input.
The 26 external fixed registrations remain the owner's informational FLINT/Z3
comparisons and are outside the timing comparison. The collector records the
actual selected and excluded names, refuses missing native controls, and refuses
cross-source registration differences.

## Collection and interpretation

`scripts/bench/sturm_regression.py` runs four trial-major blocks. Within each
block it collects adjacent complete parent ladders for the two source arms,
alternating AB and BA between blocks. Adjacency is per complete ladder, rather
than per input rung. The declared schedules, tuning, warmup, signal floors and
verdict eligibility stay with the pinned LeanBench parent runner; only its
outer-trial count becomes one per parent invocation. A shared-host CPU lease
selects one CPU without waiting for an idle core. Every completed run, failure,
command, export and host-load observation is retained.

`bench/HexSturm/CompareExports.lean` combines four complete exports per arm and
uses the pinned LeanBench trial summaries and median comparison with an explicit
10% threshold. It returns 0 for a complete passing comparison, 1 for a regression,
2 for insufficient eligible evidence, and 3 for malformed or mismatched inputs.
The collector succeeds only if every selected family returns 0. No paired-ratio
or noise exemption replaces that rule. The single-trial complexity verdicts in
raw parent exports are not new complexity evidence; the combined guard emits
only the baseline comparison report.

The collector checks the frozen executable/source bindings, benchmark
registration bodies, harness sources, native runner/CLI dependency pins and toolchain before taking
the CPU lease.
It verifies the eight fixed expected hashes and performs the parent
parametric smoke checks before timing, then stops on a failed parent or
an adjacent cross-arm input/configuration/hash mismatch, and checks frozen
integrity again at completion. The retained context identifies both source
arms; the parent export's launch-directory git metadata alone does not identify
the older executable.

## Frozen decisions, preflight and reruns

`--decision FILE` is required. The JSON object contains nonempty `question`,
`interruption`, `regression` and `inconclusive_rerun` policy strings,
`interruption_consumes_decision: true`, plus
`baseline_source_sha256`, `candidate_source_sha256`, `guard_sha256`,
`script_sha256` and a `tool_sources` map. It also requires `guard_build` with a nonempty `command` argument list,
`result: "success"` and the candidate `source_head`. This records the build
attestation; it does not mechanically prove source-to-binary correspondence.
The map binds these four paths:

- `scripts/bench/sturm_regression.py`
- `scripts/bench/cpu_lease.py`
- `scripts/bench/sweep_freshness.py`
- `bench/HexSturm/CompareExports.lean`

Freeze and build the guard with the pinned runner in the clean candidate
checkout before recording its binary hash and these source hashes. Record the
build command/result with the decision; a binary digest alone does not prove
compilation provenance. The collector checks every binding, including the actually imported helper
files, the candidate Git
head and clean status, and retains the exact decision bytes with each attempt.

Run `--preflight` with the other required arguments first. It checks source,
registration and executable bindings, runs `list` and the correctness/smoke
controls, then exits without taking a CPU lease or collecting timing samples.
Its context is labelled `preflight`; it has no computational comparison pass.
Retain that output with the decision before collecting. The baseline manifest fields and benchmark registration bodies are checked
again on each invocation. Comment normalization preserves ordinary code
indentation, but is a textual check rather than a complete Lean equivalence
checker. Matching rung hashes and configurations remain separate controls.
A real candidate and both frozen binaries need their own successful preflight.

The pinned guard's code 1 remains a regression finding, code 2 is insufficient
eligible evidence, and code 3 is invalid input. Across many input rungs, shared
host variation can produce flagged comparisons; a flag is a mechanical median
comparison rather than proof that a source change caused the slowdown. Retain
and investigate it with the raw block exports and host context. The collector
also retains per-block candidate/baseline ratios as descriptive context. No pairing,
noise exemption or threshold adjustment replaces the pinned result. Mixed invalid inputs and regression findings retain both
the failed overall outcome and an explicit `regression_findings` list.

`--rerun-of DIR` permits one unchanged rerun only of a completed inconclusive
comparison. The earlier run must have no integrity failure or prior rerun, and
its source, script, guard and decision bindings must match. A marker keyed by the baseline, candidate and guard executable hashes reserves
the first attempt. It lives in `$XDG_STATE_HOME/hex/sturm-comparisons` (default
`~/.local/state/hex/sturm-comparisons`), outside individual checkouts. Copying or
reformatting the decision, rewording its question or using another checkout does
not reset the same executable comparison's attempt count. Decision bytes remain
bound for an eligible unchanged rerun. Retain this journal with the campaign;
removing it is not a supported way to start another attempt.
An exclusive marker in the original output directory reserves the unchanged
rerun; a third attempt,
rerun of a rerun or changed binding is refused. CPU lease and affinity setup finish before reservation, so their failure
does not consume an attempt. Preflight does not reserve an attempt. An
interruption after reservation consumes the decision. SIGINT, SIGTERM and
SIGHUP use the interruption path, preserving signals already ignored by
`nohup`. Uncatchable termination or a repeated signal during finalization can
leave a partial
context and reservation without a final context hash; that still consumes the
attempt and cannot be treated as a completed inconclusive run. Interrupted and failed runs retain their context and completed data;
the tool does not resume them or reinterpret regressions as inconclusive.
Source changes need their own named question and fresh bindings. No campaign
may start from a mutable or uncommitted source snapshot.

## Tool checks

The existing CI build step builds the comparison executable, runs its synthetic
export controls, and tests registration selection without collecting performance
samples. The controls cover positive comparisons, regressions, improvements,
insufficient signal, incomplete inputs, function/configuration/hash mismatches,
failed measurements and distinct malformed-input refusals. Scope tests reject
missing native fixed controls, duplicate or unhashed registrations and a changed
auxiliary-family disposition. Synthetic executable controls additionally test
the complete collector: AB/BA order, guard argument order, preflight without
measurement, mismatched hashes, retained timeout status, mid-run binary mutation,
early binding failures and the single unchanged-rerun reservation. These tool tests are not computational performance
evidence.

The export guard requires exactly four complete parent exports per source,
independently of a benchmark registration's default trial count. Three-export
and two-export input are refused. Every declared parameter needs all four
eligible trials; the guard uses the pinned median comparator and 10-percent
rule. Its compiled controls validate these refusals. Reusing this guard for
OrderedFn requires four balanced blocks and the applicable source/configuration
bindings; it does not make the retained three-block capture acceptance evidence.
