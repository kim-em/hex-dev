# Matched timing-resolution protocol

The primary SignDet comparison requires a complete native comparison across all
25 parameterized and six fixed timing workloads. Its retained original attempt
stopped after the first source pair: both arms completed every parameter with
matching answers, but every candidate measurement was below its signal floor.
The attempt and its consumed reservation remain retained. It cannot be resumed
or treated as a completed inconclusive comparison.

The [bound proposal](resolution-proposal.json) permits one explicit change:
increase `target_inner_nanos` to four billion for every parameterized workload,
in both unchanged binaries. Fixed workloads keep their original repeats and
configuration. The target controls timed work per sample, not the acceptance
threshold. The existing native checker, parameter schedules, signal-floor
multipliers, warmup, four trial-major adjacent AB/BA/AB/BA blocks and per-call
deadlines remain unchanged.

The failed candidate's floor was about 1.137 seconds, while its actual timed
batches took about 0.552–0.959 seconds with a one-second target. Four times the
target provides additional timed work without changing that floor rule. It is
not a guarantee of adequate resolution on a later shared-host observation.
Below-floor annotations remain in the exports; the existing native checker
still requires every declared parameter and all four eligible source trials.
No smoke result, shortened ladder or partial comparison can pass this gate.

## Admission and consumed attempts

`scripts/bench/sturm_regression.py --profile sign-det --resolution-from ORIGINAL`
requires a decision with the matching `resolution_protocol`. Before any CPU lease
or measurement reservation it authenticates:

- The original context, bound decision and account-global reservation, on the
  same host, with no integrity failure or earlier adaptation/rerun.
- The same frozen native binaries, producer inputs, source manifests and guard
  build; the complete original timing selection.
- The original complete source pair, commands, successful parameter hashes,
  one-second configuration and candidate exit 2. The recorded below-floor
  failure must match the actual retained export, whose timings are below its
  declared floor.
- The exact context and export hashes in the proposal. The new target is fixed
  at four seconds; adding fields or choosing another target is refused.

The collector uses one stable `-resolution` reservation beside the original
reservation, keyed by the same native comparison identity. Moving the output,
changing the decision text or changing the collector cannot create another slot.
Preflight does not lease a CPU or consume an attempt. Once collection reserves
that slot, interruption, failed commands and insufficient resolution remain
consumed results. The existing single unchanged-rerun rule applies only to a
completed inconclusive comparison with identical bindings. There is no further
target adaptation or automatic retry.

## Tooling and evidence

The original candidate and build manifests remain immutable. An execution
checkout must descend from that candidate and preserve every recorded producer
input. Only the collector, its controls, the named protocol summaries and new
non-Lean evidence under this report directory may differ. Tool sources and the
execution commit are bound separately from the native build provenance.

The parent must export the four-second target for every parameterized arm;
ignoring the override fails collection. Fixed commands receive no override.
All raw exports, stdout/stderr, host context, failures and native guard reports
must be retained. Host activity is recorded, with no quiet-core precondition or
sample rejection.

The admission controls exercise the actual archived failure without running a
benchmark. Separate synthetic-executable controls check command construction,
complete scope and slot consumption; their stub verdict is not performance
evidence. The native guard and its retained controls remain unchanged.

This protocol and its controls do not establish a performance pass. Acceptance
requires the complete collected exports and the unchanged native checker verdict.
No phase counter or publication eligibility changes follow from this proposal.
