# Public divisor enumeration: shared-host protocol

This document preregisters the next measurement for #9619 under Hex's
shared-host policy. The earlier experiment and all three exhausted campaigns
remain retained with their original verdicts. This protocol changes only host
admission: ordinary machine activity is recorded as context and cannot reject
or remove a completed sample.

## Operation and model

Measure public `Hex.Nat.divisors` on preconstructed checked factorizations for
the squarefree products of the first 6, 8, 10, 12, 14 and 15 table primes. The
exact divisor counts are `τ = 64, 256, 1024, 4096, 16384, 32768`; subjects and
divisors remain below `2^63`. Factor search and checked-input construction occur
before timing. The timed call includes divisor-product generation,
`List.mergeSort`, array materialization and a result-consuming checksum. The
outside-timing `divisor-audit` exports every complete array, which the collector
independently reconstructs, sorts and compares before accepting the run.

The two-sided mode-1 model remains `τ * log₂ τ`. For `τ = 2^k`, compiled
`List.mergeSortTR₂` has exactly `k` balanced levels and linear total merge work
at each level. Generation, array conversion and hashing are linear. The
committed operation census and existing inclusive profile give the detailed
algorithmic derivation and attribution; no observed timing was used to choose
the model.

Use the unchanged LeanBench registration: seven trial-major outer trials at
each rung, warm cache mode, `targetInnerNanos = 1000000000`,
`maxSecondsPerCall = 10`, `signalFloorMultiplier = 1`, slope tolerance `0.15`,
verdict warmup fraction `0.2`, `paramFloor = 64`, `paramCeiling = 32768`, and
`narrowRangeNoiseFloor = 1.5`. The verdict range is `τ=256..32768`; retain all
`τ=64` trials as diagnostic. Acceptance requires all 42 scheduled points, an
exact `consistent_with_declared_complexity` verdict, complete-array validation,
matching result hashes, clean source provenance and unchanged measured sources.

## Shared-host collection

Run on the available shared host. `--cpu auto` selects and pins one logical CPU
to avoid deliberate overlap with another Hex measurement; an explicitly named
CPU is also allowed. Neither choice asserts isolation. The collector records
the host, CPU, affinity, SMT topology, process/load snapshots and timed telemetry.
No activity percentage, sibling busy time, frequency observation or process
sighting is an admission threshold. There is no quiet-core preflight and no
contamination retry. The telemetry sidecar is descriptive even if its legacy
summary field labels the run contaminated.

Take one complete run. If its scientific verdict is inconclusive, one unchanged
rerun is allowed at
`reports/bench-results/intfactor-divisors-shared-attempt-2.json`; retain both
attempts. Validation errors, subprocess failures and timeouts remain rejected
and retained because they do not produce complete scientific evidence. A bad
verdict is never discarded or relabelled.

From the clean commit containing this protocol and collector:

```sh
python3 scripts/bench/intfactor_phase4.py --divisors --cpu auto \
  --output reports/bench-results/intfactor-divisors-shared-attempt-1.json
```

The representative inclusive profile may be reused because the public divisor
implementation, timed body, model family and input remain unchanged. Collector,
protocol and benchmark-executable bookkeeping changes do not require a new
profile. A successful run then requires report and owner-mapping reconciliation,
the Phase-5–7 freshness audit, the requested builds and checks, and honest
registry status for both libraries. Publication remains outside #9619.

## Result

The preregistration commit is
`3d5e24b620a758c44a379b430fb45aa10488ba5b`. The sole shared-host
[attempt](bench-results/intfactor-divisors-shared-attempt-1.json) is accepted.
It ran on `chungus2`, automatically selected CPU 1 with SMT sibling 49, and
retained all 42 trial-major measurements. LeanBench returned exact verdict
`consistent_with_declared_complexity`, residual slope `-0.014231`, and
normalized constants `10.990153..12.008666` on the verdict range. Per-rung
trial spreads were 1.28% to 4.84%.

The collector independently validated every complete divisor array and every
timed checksum. Timed telemetry observed 0.287004 seconds of SMT-sibling
activity over 30.514898 timed seconds (0.9405%), no foreign runnable samples,
and complete sidecars for all 42 trials. That activity is retained as context
and does not alter the raw measurements or verdict. SMT contention can only
inflate wall time, so it limits interpretation of the normalized-constant band;
over the 128-fold verdict range it does not explain the observed flat residual
slope. The accepted record has
SHA-256 `eca5c70876bce7e5fe1ad9417c3383eef643d6560515a1291e0cba6b698963af`;
its raw LeanBench export and telemetry sidecar have SHA-256
`052e9f9835731af41bd95e928d70ff487e176691d7a37227e81a2b6ca3cbd31f` and
`7eb077947190a4e5e9ab016366ad6fd5219d1026a075d4ea898f2077a79539d3`.
