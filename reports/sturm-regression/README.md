# Sturm computational regression comparison

The Phase-6 question is whether the native computational paths carrying timing
claims regress against the most recent committed benchmark baseline. This is
separate from the owning issue's completed Phase-4 complexity and comparator
attestation. No measurements or performance pass are recorded here yet.

## Scope and baseline

The proposed baseline executable is the retained native build of
`75fbfa04550ae0f76df074176f44bf0f2533334a`, identified by the source manifest in
`reports/bench-results/sturm-sign-comparisons/capture/after-source.json.gz`.
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
failed characterizations remain unchanged. Correctness verification still
includes that auxiliary family and all eight native fixed expected-hash controls.
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
It verifies native expected results before timing, stops on a failed parent or
an adjacent cross-arm input/configuration/hash mismatch, and checks frozen
integrity again at completion. The retained context identifies both source
arms; the parent export's launch-directory git metadata alone does not identify
the older executable.

Before collection, the decision file must specify interruption handling and the
single allowed unchanged rerun. A failure or inconclusive result cannot be
silently replaced by later successful samples. Source changes need their own
named question and bindings. No campaign may start from a mutable or uncommitted
source snapshot.

## Tool checks

The existing CI build step builds the comparison executable, runs its synthetic
export controls, and tests registration selection without collecting performance
samples. The controls cover positive comparisons, regressions, improvements,
insufficient signal, incomplete inputs, function/configuration/hash mismatches,
failed measurements and distinct malformed-input refusals. Scope tests reject
missing native fixed controls, duplicate or unhashed registrations and a changed
auxiliary-family disposition. These tool tests are not computational performance
evidence.

The export guard requires exactly four complete parent exports per source,
independently of a benchmark registration's default trial count. Three-export
and two-export input are refused. Every declared parameter needs all four
eligible trials; the guard uses the pinned median comparator and 10-percent
rule. Its compiled controls validate these refusals. Reusing this guard for
OrderedFn requires four balanced blocks and the applicable source/configuration
bindings; it does not make the retained three-block capture acceptance evidence.
