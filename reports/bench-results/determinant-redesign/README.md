# Fixed-witness determinant experiments

- `arithmetic`: initial implicit-exponent generator; one completed replay
  sample followed by a 60-second timeout.
- `arithmetic-direct`: explicit conjunction traversal; same statement
  inference problem and timeout. The completed replay sample is retained.
- `arithmetic-threshold`: bounded heartbeat diagnostic identifies pending
  metavariable/typeclass synthesis as the failure before tactic execution.
- `arithmetic-typed`: explicit `Nat` exponent types; all eight arithmetic
  samples complete. The support source here is integer-specific.
- `full`: all eight complete-proof samples, including every candidate lemma.
  Its support is generalized to arbitrary commutative rings.
- `setup`: development failures, smaller diagnostics and successful axiom /
  proof-node audit. These logs are not performance samples.

Each batch retains source snapshots, fixture, raw observations, result data,
host context and a terminal status with elapsed time. Failed attempts are not
discarded or counted as successes. No larger mathematical input was run.

Proof-work clocks and external build clocks are separate. A final kernel
check below the 1 ms profiler threshold contributes an interval `[0,1)`;
it is not declared free. Full-proof samples sum all four candidate lemmas'
tactic and kernel costs, including the first check of each.

The report is [here](../../determinant-redesign-results.md); reproducible
working generators are under `experiments/Determinant/`. Exact measured
generator/support versions remain in these directories as `*.txt` snapshots.
