# Repeated-factor compiled stage costs

This fixed-problem protocol measures the existing Mathlib-free registrations
`Hex.RealClosure.Bench.runYun`, `runAssembly`, `runRoots`, and `runNativeRoots`.
Each uses the same rational polynomial
`-3 X² (X² - 2)³ (X - 3)⁵`, with distinct ordered real roots
`[-√2, 0, √2, 3]` and multiplicities `[3, 2, 3, 5]`.
Construction of the runtime inputs precedes timing.

Six fixed trial-major rounds invoke the four registrations in that order.
Each invocation uses the existing lean-bench fixed runner with `--repeats 1`
and `--min-total-seconds 0.2`; its child auto-tunes inner repeats. All 24
completed measurement exports, stdout/stderr, exit statuses and host activity
are retained. No observed sample is discarded, and this protocol authorizes
no rerun. Acquire one automatically selected CPU using `cpu_lease` and pin the
orchestrator and inherited children there, without checking core quietness.

These are inclusive stage boundaries: Yun includes zero extraction and the
raw recurrence; assembly includes those stages and every factor's isolation;
complete roots also include global comparisons/sorting; native roots also
materialize each selected child and its checked descriptor/prepared domain.
Each checks its actual result and returns the registered expected hash 1.
Do not subtract their observations to infer exclusive stage costs. They are
fixed-input absolute observations, with no complexity or scaling verdict.
BKR solving, coefficient-sign calls, query construction, serialization and
ordinary kernel replay still require separate evidence.

Before collecting, bind the protocol/source commit, Lean/lean-bench pins,
compiled executable hash, build log and registration source. Retain all raw
exports and report medians and full ranges from per-call values
`total_nanos / inner_repeats`, along with the inner-repeat counts.
