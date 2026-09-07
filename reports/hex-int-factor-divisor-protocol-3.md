# Public divisor enumeration: 0.5% interference protocol

This document preregisters the third finite measurement campaign for #9619.
The first two protocols are exhausted, and every earlier inconclusive,
diagnostic, contaminated and preflight-only artifact remains unchanged. This
campaign changes only the independently observed host-interference ceiling and
the controls needed to measure it. It does not change the benchmark, public
complexity contract, input family, model, trial count, warmup, batching or
scientific verdict tolerance.

## Operation and claim

Measure public `Hex.Nat.divisors` on preconstructed checked factorizations for
the squarefree products of the first 6, 8, 10, 12, 14 and 15 table primes.
Their exact divisor counts are `τ = 64, 256, 1024, 4096, 16384, 32768`.
Subjects and all divisors remain below `2^63`. Factor search and construction
of checked inputs occur before timing. The timed call includes divisor-product
generation, `List.mergeSort`, array materialization and the result-consuming
complete-array checksum. `divisor-audit` exports the full arrays outside the
timed region; the collector independently reconstructs, sorts and compares
every result and checks every timed hash.

The registered family-specific model remains two-sided `τ * log₂ τ` (mode 1).
For `τ = 2^k`, the compiled `List.mergeSortTR₂` performs balanced splitting for
exactly `k` levels, visiting `τ/2` cells per level. Equal-half merges require
linear traversal per level, independently of the generated order. Generation,
array conversion and hashing are linear and do not change the bound. The
operation-count fixture and existing inclusive profile retain the detailed
derivation and attribution. No weaker evidence mode is registered.

Use the unchanged LeanBench registration: seven independent child trials per
rung, warm cache mode, `targetInnerNanos = 1000000000`,
`maxSecondsPerCall = 10`, `signalFloorMultiplier = 1`, slope tolerance `0.15`
and verdict warmup fraction `0.2`. The verdict range is τ=256..32768; retain
all τ=64 points as diagnostic. Acceptance requires all 42 scheduled points,
all checksums matching the independently validated arrays, and exact verdict
`consistent_with_declared_complexity`. Timing spread and an inconvenient
scientific verdict are never contamination criteria and never license removal.

## Host and contamination controls

Use designated shared host `chungus2`, logical CPU **81**, with SMT sibling
**33**. The retained untimed 30-second survey chose pair 33/81 because its
maximum sibling busy fraction was tied for lowest among the 47 eligible
physical cores at about 0.333%; CPU 81 itself had 0.06 seconds busy versus
0.10 seconds on CPU 33. These observations select placement only and contain
no operation timings.

The campaign ceiling is **0.005 (0.5%)**. This is small relative to the
registered 15% slope tolerance while permitting the best independently
observed core pair. It remains a rejection gate, not a correction applied to
timings. At the host's 100 Hz scheduler accounting rate, a 30-second preflight
has about 0.033% resolution per tick and permits at most 15 busy ticks per
sibling, subject to the exact measured wall duration. The collector records
the tick rate and raw busy seconds rather than rounding the decision.

After building and validating the complete output, observe up to ten
consecutive 30-second preflight windows, for a finite maximum of five minutes.
The collector runs off the selected physical core. Both CPU 33 and CPU 81 must
have busy time no greater than 0.005 of the exact window. Retain every window.
If none qualifies, end the campaign before timing. A qualifying window merely
allows timing to start; it cannot waive the timed-region gate.

During timing, pin every measured descendant to CPU 81 and keep the telemetry
monitor off CPUs 33 and 81. Sample task state every 250 ms and retain timed-loop
sidecars. Reject missing or malformed regions. The aggregate score remains the
sum of timed-overlap-weighted sibling busy time and the whole overlapping
sample interval for any observed foreign runnable task on CPU 81, divided by
timed-region wall time. Reject scores above 0.005. Because one foreign sighting
will normally exceed that total budget, this is effectively a zero-sighting
rule plus a small sibling-tick allowance; the artifact is not represented as a
0.5%-resolution estimate. Process-group ownership, descendant cleanup, raw
task lists and source/executable provenance follow the committed corrected
collector. Frequency and allocator variation remain possible even for an
admissible run.

Do not run a concurrent local build, profile or other workload during
collection, and do not alter other sessions' affinity or workloads. A passing
run must still meet all scientific and provenance checks.

## Finite attempt rule

Take one complete acceptance attempt. Only an independently flagged telemetry
contamination verdict permits one replacement of the entire attempt, for at
most two timed attempts. Commit and retain the first attempt before taking an
authorized replacement. Every admissible timed attempt must pass. An
admissible inconclusive verdict, validation error, subprocess failure or
timeout ends the campaign without replacement. Preflight exhaustion also ends
the campaign without a timed attempt. Never overwrite an artifact or rerun
until green.

From the clean commit containing this protocol and collector configuration:

```sh
python3 scripts/bench/intfactor_phase4.py --divisors --cpu 81 \
  --output reports/bench-results/intfactor-divisors-campaign-3-attempt-1.json
```

Only the authorized contamination replacement may use `attempt-2.json`.
Render reports only from accepted records. If an admissible timing passes,
verify that the existing inclusive profile's executable and measured-source
hashes still match; otherwise collect a fresh profile under the existing
attribution protocol. Then explicitly audit the core and bridge divisor API
mapping, Phase-5–7 freshness, report Concerns, machine-readable metadata,
phase/DAG checks and full CI before recertifying either library. Publication
and release-manifest changes remain outside this campaign. If no admissible
run passes, retain the exact blocker and leave both counters at 3.

## Campaign result

The preregistration commit is
`0fac6714191c290fd60c5fdb910f11d7fab1875a`. The sole
[attempt](bench-results/intfactor-divisors-campaign-3-attempt-1.json) was run
from that clean commit and is explicitly rejected. The build and complete
divisor audit passed, but none of the ten preflight windows met the 0.5% gate
on both siblings, so no timing subprocess or telemetry sidecar was created.
The retained busy fractions for CPUs 33/81 were, respectively:

| window | CPU 33 | CPU 81 |
| ---: | ---: | ---: |
| 1 | 1.000% | 1.833% |
| 2 | 2.267% | 2.600% |
| 3 | 2.033% | 2.867% |
| 4 | 4.433% | 4.700% |
| 5 | 12.466% | 10.400% |
| 6 | 1.700% | 1.300% |
| 7 | 0.500% | 1.033% |
| 8 | 2.067% | 2.167% |
| 9 | 0.733% | 0.300% |
| 10 | 1.033% | 1.867% |

The record has SHA-256
`217fd2c2c39925b24f83cddf8c8e9df6fd3d623e512bbf1fc291d21149e65893`
and retains exact monotonic intervals, tick-derived busy seconds, host state,
commands, stdout/stderr, source hashes, executable hash and the full audit.
Preflight exhaustion is not timed contamination and does not authorize the
replacement attempt. This campaign is exhausted with Phase 4 incomplete.
