# Matched timing-resolution protocol

The primary SignDet comparison requires all 25 parameterized and six fixed timing
workloads. Its retained original attempt stopped after the first complete source
pair. Per-call times differed by less than 0.6%, and the answers matched. The
baseline spawn floor was 57.392388 ms; its tenfold threshold excluded the 16384
row. The candidate spawn floor was 113.739337 ms; its tenfold threshold excluded
all seven rows, whose timed batches took about 0.552–0.959 seconds. The collector
then treated the candidate's below-floor exit 2 as fatal. These observations do
not establish a causal host-activity explanation or an arithmetic regression.
The failed attempt and its consumed reservation remain retained; it cannot be
resumed or treated as a completed inconclusive comparison.

The [bound proposal](resolution-proposal.json) permits one matched target increase
to 2.25 seconds for exactly four floor-filtered workloads: `Height.runReduce`,
`Height.runCheck`, `runSmallReduced` and `runSmallFull`. Both unchanged binaries
receive the same override. The other 21 parameterized registrations retain their
100 ms targets and disabled floor filters (`signalFloorMultiplier = 1`). Fixed
workloads retain their repeats and configuration. The existing native checker,
parameter schedules, signal-floor multipliers, warmup, four trial-major adjacent
AB/BA/AB/BA blocks and per-call deadlines remain unchanged.

## Runner limit and resolution margin

The pinned runner limits the effective target to one quarter of the deadline
remaining after its measured spawn floor. It exports that effective target as
part of the configuration; different clamped configurations cannot pass the
native comparison. The Height pair has ten-second caps and the Small pair has
sixty-second caps. The pinned default kill grace is 100 ms.

Admission reads those frozen registrations and runner defaults. With a declared
one-second planning spawn floor, the Height target budget is
`(10s + 0.1s − 1s) / 4 = 2.275s`, and the Small budget is 14.775s. The proposed
2.25-second target fits both. A four-second target would be clamped for Height
and is refused before a lease or reservation. This calculation takes no host
measurements. The planning floor is an operational envelope, **not** a host
admission threshold, a quiet-core rule or permission to discard samples.

The pinned autotuner aims for batches of roughly `0.55T` to `1.1T`. At `T = 2.25s`
that is about 1.2375–2.475 seconds: only about 8.8% lower-end margin above the
candidate's observed 1.13739337-second signal threshold. This is not a guarantee
of adequate resolution. Larger later floors and short batches remain in the
exports and may yield inconclusive results. A runner clamp or differing exported
target is a retained failure. There is no floor preflight, sample rejection,
quiet-host wait, lower threshold, deadline increase or further target adaptation.

## Admission and consumed attempts

`scripts/bench/sturm_regression.py --profile sign-det --resolution-from ORIGINAL`
requires a decision with the matching `resolution_protocol`. Before any CPU lease
or measurement reservation it authenticates:

- The original context, bound decision and account-global reservation on the same
  host, with no integrity failure or earlier adaptation/rerun.
- The same frozen binaries, producer inputs, source manifests, guard build and
  complete original timing selection.
- The original complete source pair, commands, successful parameter hashes,
  one-second configuration and candidate exit 2. The recorded failure must match
  the retained export, whose timings are below its declared floor.
- The exact context and export hashes, four-workload override scope, fixed target,
  planning floor and cap/grace budget. Other targets or extra fields are refused.

The reviewed collector uses one stable `-resolution` reservation beside the
original, keyed by the same native comparison identity. Changing output paths
or decision wording does not create another slot. The frozen collector and tool
sources remain part of admission; this is not a claim about arbitrary replacement
tooling. Preflight does not lease a CPU or consume an attempt. Once collection
reserves the slot, interruption, failed commands and insufficient resolution
remain consumed results. The existing single unchanged-rerun rule applies only
to a completed inconclusive comparison with identical bindings. It does not apply
to the original failed attempt. There is no automatic repeat.

## Tooling and evidence

The original candidate and build manifests remain immutable. An execution checkout
must descend from that candidate and preserve every recorded producer input. Only
the collector, its controls, the named protocol summaries and new non-Lean evidence
under this report directory may differ. Tool sources and the execution commit are
bound separately from the native build provenance.

Each selected parent must export the bound target; ignoring or clamping it fails
collection. Other parameterized and fixed commands receive no target override.
All exports, stdout/stderr, host context, failures and native guard reports must
be retained. The checker still requires every declared parameter and all four
eligible source trials. No partial comparison can pass.

Admission controls exercise the actual archived failure without benchmarks, and
pure controls cover the pinned runner's clamp arithmetic. Synthetic-executable
controls model the clamp with varying spawn floors, check override scope, preflight,
rerun eligibility and slot consumption. Their stub verdict is not performance
evidence. The native guard and its retained controls remain unchanged.

This protocol does not establish a performance pass. Acceptance requires the full
collected exports and unchanged native checker verdict. No phase counter or
publication eligibility changes follow from the proposal.
