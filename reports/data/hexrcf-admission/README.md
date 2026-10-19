# Admission traversal evidence

See [the report](../../hexrcf-admission.md) for scope and limitations. Run
`python3 reports/data/hexrcf-admission/verify.py --check-head` from the repository
root to check the source-bound record against the current tree. Without
`--check-head`, verification checks the immutable implementation commit.

`context.json` binds the implementation, its parent record, source files and
frozen artifacts. The older records retain their original source pins. The
source change is exactly the tactic implementation, its new admission test
module and the registration of that test in the existing default library.

The original-source profiles are separate diagnostic runs. The only paired
cost comparison is the fixed guard-only AB/BA experiment, with all four arms
retained. It is not a whole-tactic speedup or a scaling study. Profiler category
times are exclusive. The copied Lean profiler implementation documents that
interpretation.

The full-source prototype inputs, timing-only checker, original checker,
failed-input snapshots and final source patch identify the successive variants.
Logs retain the unknown-constant and parser failures, cache-fetch failure,
explicitly terminated setup attempt, initial negative-test warning and static
negative-probe classification failure. A terminated service is not a passing
sample even if systemd reports successful termination. The final negative-test
module restores the complete saved state, including its deliberately forbidden
local fixture and warning, and exports no admitted theorem.

The systemd wrapper applies an aggregate 32 GiB limit with no swap and two Lean
threads. Builds run serially. This record does not complete #10358 or replace
the required fresh review, exact-head CI and merge.
