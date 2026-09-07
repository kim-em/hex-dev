# Public divisor enumeration: corrected ownership protocol

This is a new, finite measurement campaign for #9619, on current main plus
this committed protocol and telemetry correction. The original campaign's two
rejected attempts remain rejected. The original inconclusive experiment and
noisy diagnostic pass remain in [the original protocol](hex-int-factor-divisor-protocol.md).
No benchmark implementation, scientific tolerance or public contract changes.
This campaign is exhausted. The later
[0.5% protocol](hex-int-factor-divisor-protocol-3.md) is separately
preregistered and does not reclassify any result described here.

## Operation and model

The exact input family, structural derivation, timed boundaries, independent
complete-output audit and LeanBench registration are those in the original
protocol: prechecked products of the first 6, 8, 10, 12, 14 and 15 table primes,
with divisor counts 64, 256, 1024, 4096, 16384 and 32768. The public operation
includes generation, `List.mergeSort` and array materialization. The consuming
checksum is timed; factor search, certificate construction and full validation
are outside timing. Balanced splitting and equal-half merging independently
justify the two-sided Θ(τ log₂ τ) model for this family. Linear generation,
array conversion and hashing do not change it. All values fit below `2^63`.

Mode 1 is the only registered evidence mode. Retain seven independent child
trials at each rung, warm mode, `targetInnerNanos=1000000000`,
`maxSecondsPerCall=10`, `signalFloorMultiplier=1`, slope tolerance 0.15 and
verdict warmup fraction 0.2. The harness's unchanged automatic warmup and
batching apply. The verdict range is τ=256..32768; retain τ=64 as diagnostic.
All 42 trial hashes must agree with the independently validated complete
arrays, and the exact verdict must be `consistent_with_declared_complexity`.
Neither a poor verdict nor trial spread licenses exclusion or replacement.

## Host controls and telemetry correction

Use `chungus2`, logical CPU **62**, SMT sibling **14**. The committed
[untimed 30-second core survey](bench-results/intfactor-divisors-core-survey.json)
selected this physical core by the smallest combined busy time. This survey
contains no operation timings and is not acceptance evidence. Host load varies;
a survey alone cannot establish a clean timing window.

Build first, then wait for a quiet physical-core window. The collector observes
at most 150 consecutive two-second `/proc/stat` windows. Both logical CPUs
must have busy time at most 0.002 of the window. All observations, including
failures, are retained. No benchmark runs during this preflight, and the
collector's affinity excludes the physical core. If no window qualifies, stop
the campaign with the explicit host dependency; do not spend a timing retry.
A qualifying window permits collection but does not waive the timed-region
contamination test. Do not run another local build or profile during collection,
and do not alter other sessions' affinities or workloads.

The telemetry monitor uses a dedicated process group and its children inherit
that group at fork. Each task's state, CPU and process group come from the same
`/proc/<tgid>/task/<tid>/stat` read. This removes the old race between an earlier
process ancestry snapshot and a later task scan. A newly born benchmark child
is already owned when first observed; an unrelated task with the same name is
still foreign. The runner must not daemonize or change groups (LeanBench does
neither). The monitor runs off the physical core. Collector timeout cleanup
still kills the entire monitor/benchmark group. Ownership does not exempt
sibling busy ticks from the interference test.

Retain the original 250 ms sampling interval, timed-region sidecars and
0.002 aggregate interference ceiling: estimated foreign runnable activity on
the measurement CPU plus SMT sibling busy time, weighted by timed-region
overlap. Missing/malformed timed-region evidence rejects the run. Record all
raw observations, commands, stdout/stderr, host/core state, source and direct
benchmark-binary hashes, including failures. This remains a sampling estimate;
it neither guarantees isolation nor controls frequency or allocation variation.

## Attempt limit and integration

Take one complete acceptance attempt. Only independently flagged contamination
permits **one** replacement of the entire attempt, with the same preflight and
protocol: at most two timing attempts total. Retain both attempts, and every
admissible run must pass. An admissible inconclusive verdict, validation error,
subprocess failure or timeout ends the campaign without a replacement. A
preflight exhaustion also ends it. No tolerance changes or alternate evidence
labels are authorized. Commit this protocol, collector and tests before
collection, and commit retained first-attempt artifacts before a replacement.

From the clean preregistration commit:

```sh
python3 scripts/bench/intfactor_phase4.py --divisors --cpu 62 \
  --output reports/bench-results/intfactor-divisors-campaign-2-attempt-1.json
```

Use the suffix `attempt-2.json` only for the allowed contamination replacement.
Never overwrite old evidence. Render accepted reports with `--report ARTIFACT`.
The existing inclusive profile remains applicable if its measured Lean sources
and toolchain are unchanged; explicitly verify their hashes during integration.
If timing passes, recheck the core/bridge API-to-owner mapping and Phase-5–7
freshness, clear only resolved Concerns, run the affected validations and full
CI, and record the honestly earned pair status. Publication remains outside
this work. If no admissible timing passes, preserve the precise blocker and
leave both counters at 3.
