# Automatic bounded primality construction

With `import HexIntFactor`, plain `primality?` constructs and recursively checks
secp256k1, P-384 and Curve448. Add `HexPrimalityMathlib` for `Nat.Prime`.
The tested caller option is a local `maxHeartbeats 4000000`; no recursion-depth
or exponent-threshold option is needed for these three fields. Four million
is a tested allowance, not a measured minimum. The default heartbeat limit
fails. Power expressions for P-384 and Curve448 can emit Lean 4.34.0's
exponent-threshold warning and still normalize successfully.

```lean
import HexIntFactor

set_option maxHeartbeats 4000000 in
example : Hex.Nat.Prime (2 ^ 256 - 2 ^ 32 - 977) := by
  primality?
```

The core route runs first. Only exhaustion with an allowance left permits one
complete ECM retry. Attempts spent on failed subsets, repeated factoring,
recursive children and witnesses all count against the original 1024 attempts.
The retry starts from the first failure's advanced random state. P-521 and
Curve25519 return the first route's certificate, attempts, random state and
events without invoking ECM. Explicit `factor :=` and `using` forms bypass
selection. Ordinary primality and integer factorization keep their policies.

## Complete paths and remaining limits

| Input | Core attempts | Retry allowance | Retry attempts | Combined result |
|---|---:|---:|---:|---|
| secp256k1 | 272 | 752 | 145 | certificate, 417 attempts |
| P-384 | 14 | 1010 | 290 | certificate, 304 attempts |
| Curve448 | 67 | 957 | 259 | certificate, 326 attempts |
| P-521 | 170 | — | — | unchanged certificate, 170 attempts |
| Curve25519 | 29 | — | — | unchanged certificate, 29 attempts |
| 507-bit fixture | 14 | 1010 | 142 | exhausted, 156 attempts |

For secp256k1, the first unresolved core obligation is the child
`205115282021455665897114700593932402728804164701536103180137503955397371`.
P-384, Curve448 and the 507-bit fixture first fail at their roots: the returned
known factor product cannot meet a construction size criterion. All recursive
obligations are resolved in each of the three successful retries. The 507-bit
input remains unsupported under the specified profile:

```
325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771
```

The [complete path record](bench-results/hex-primality-fallback-prototype-issue-10373.json)
contains all factor callback results, allocations, attempts, random-state
transitions, returned events and complete certificates. Its subject identification
uses the ordered callbacks and their insufficient known products; the production
constructor additionally reports the unresolved subject directly. The default
profile returns empty event lists; retry tests separately exercise nonempty event
concatenation. Diagnostic trace I/O is excluded from the paired timing records.

The three automatic paths have these generator transitions:

| Input | Initial state | State entering ECM | Final state |
|---|---:|---:|---:|
| secp256k1 | 18446744069414583343 | 3997430096334688559 | 1941426468410348159 |
| P-384 | 4294967295 | 15362738636118008311 | 16876097068256507619 |
| Curve448 | 18446744073709551615 | 5625365687987180107 | 485356618176329107 |

The same path record covers 0, 1, 2, 7, 97, 1009, 15 and 561. Table successes
and composite verdicts consume zero attempts and never retry. The 521-bit input
limit, depth 32, factor/subset limits, ECM bounds 32768/524288, and consecutive
64-curve schedule remain fixed. The 522-bit rejection remains covered by the
core conformance suite. These are bounded methods, not completeness claims.

## Retained comparisons

The comparisons use four fixed trial-major blocks, adjacent AB/BA arms, on
`chungus2` with Lean 4.34.0. Each measurement phase selects and pins one logical
CPU: native search uses CPU 5, fresh elaboration CPU 1, and rendering/replay
CPU 2. Host loads are recorded; every completed sample is retained. Native and
elaboration phases can overlap on different CPUs. No sample is rejected for
host activity, and no quiet-core waiting or unchanged rerun is used.

There are 88 native observations, 88 fresh-module observations, and 60 successful
render/replay observations. Explicit ECM versus automatic retry covers the three
new fields. Core-only construction versus automatic retry covers those fields,
P-521, Curve25519, the 507-bit fixture, 7 and 15. A failed construction has no
rendering or replay observation. Each successful paired certificate agrees;
first-route successes also preserve their attempt totals.

The complete records include sources, source and executable hashes, commands,
outputs, outcomes, CPU placement and load observations:

- [Native search](bench-results/hex-primality-fallback-native-issue-10373.json).
- [Fresh-module elaboration](bench-results/hex-primality-fallback-elaboration-issue-10373.json).
- [Certificate rendering and kernel replay](bench-results/hex-primality-fallback-replay-issue-10373.json).
- [Option probes and interrupted pilot](bench-results/hex-primality-fallback-experiment-issue-10373.json).

The native and elaboration comparisons use the complete-retry prototype, before
production dispatch changes. They isolate selection policy using the same
constructor and provider in both arms. Fresh modules use the same explicit
`maxHeartbeats 4000000` and native producer compilation in both arms. The
prototype elaboration includes normalization, search, rendering, literal
elaboration and goal assignment; its complete Lake duration includes imports
and ordinary proof checking. It does not measure the final registration lookup
or the `Try this:` UI. The retained records also contain observational in-process
tactic durations; fresh-module comparisons above use the external Lake timer.
The checked-in construction and option probes retain heartbeat observations
and use only the external harness for timing. Exact production suggestions and a separate production
resource probe validate the final plain tactic.

Commit fields identify the baseline; embedded source snapshots identify the
measured uncommitted prototypes. The initial pilot retains twelve option probes,
two native samples, two fresh-module samples, and a failed replay-harness build.
The failure was an unqualified `logInfo` in the observation code; the corrected
four-block replay record retains all sixty successful checks. No primality
result or completed timing sample from the pilot is overwritten.

### Native construction

Native timers include the constructor's compiled self-check and exclude process
startup, parsing, trace output and certificate formatting. The table gives
medians of four samples from the explicit/automatic comparison:

| Input | Explicit ECM | Automatic retry | Explicit / automatic attempts |
|---|---:|---:|---:|
| secp256k1 | 15.126 s | 26.036 s | 145 / 417 |
| P-384 | 31.415 s | 32.234 s | 290 / 304 |
| Curve448 | 20.388 s | 21.554 s | 259 / 326 |

The secp256k1 core route repeatedly fails at its recursive child, making the
complete retry materially more expensive than selecting ECM immediately.
P-384 and Curve448 spend much less time on the first failure. This repeated
work is charged; neither larger budgets nor cross-construction caching is
needed to meet the three-field contract.

| Existing input | Core-only median | Automatic median | Attempts, both arms unless shown |
|---|---:|---:|---:|
| P-521 | 1.378 s | 1.373 s | 170 |
| Curve25519 | 0.420 s | 0.416 s | 29 |
| 507-bit fixture | 0.885 s | 20.676 s | 14 / 156, both exhausted |

Automatic selection adds substantial bounded work to the unsuccessful 507-bit
input. The successful core cases do not incur ECM search. Tiny differences
between their medians are host observations, not an optimization claim.

### Fresh-module elaboration

Complete module builds, including Lake startup and ordinary proof checking,
have the following four-sample medians. Both arms use the same finite caller
options and native compilation configuration.

| Input | Explicit ECM | Automatic retry |
|---|---:|---:|
| secp256k1 | 16.250 s | 27.235 s |
| P-384 | 32.911 s | 33.560 s |
| Curve448 | 21.446 s | 22.651 s |

All 60 expected successful builds and 28 expected exhausted/composite builds
match their intended outcomes. The prototype's generic failure text is
`EXHAUSTED`; the production diagnostics are pinned independently in conformance.

### Rendering and replay

Rendering/elaboration timers start after imports and cover reconstruction of
the literal syntax and its elaboration. Direct kernel checks expand local proof
dependencies, finish pending checks, and check the complete proof against its
goal. Each timed check is preceded by rejection of an invalid Boolean equality,
a corrupted subject, and (for non-table certificates) a zero witness. These
controls are outside the timed interval. The unchanged sound checker is used
throughout; no `native_decide`, supplied factor assertions or new axioms are used.

| Certificate | Rendering/elaboration median | Direct kernel median |
|---|---:|---:|
| secp256k1 | 2.694 ms | 3.555 ms |
| P-384 | 4.166 ms | 7.940 ms |
| Curve448 | 5.442 ms | 11.822 ms |
| P-521 | 12.740 ms | 50.086 ms |
| Curve25519 | 3.369 ms | 4.698 ms |

These are four-sample automatic-arm medians, using the explicit/automatic pair
for the new fields and the core/automatic pair for the existing successes.
The raw record retains both arms and all samples.

## Resource accounting and reproduction

`IO.getNumHeartbeats` deltas observe real allocation counters. Raw values are
divided by 1000 to express Lean's user heartbeat units. No counter, initial
baseline, or limit is reset; no work is excluded or moved to a fresh task by the
tactic. Separate executable processes and fresh modules are measurement arms,
not a production tactic escape from caller accounting. The native search is
synchronous and does not poll Lean's elaborator heartbeat checks internally:
a heartbeat overrun can be reported after the search returns, not at the
instant the limit is crossed. Finite attempts bound its schedule; heartbeats
are not a wall-clock timeout. An explicit
`factor := Hex.Nat.Construction.factorSearch` retains core-only construction.

The six successful prototype option probes use only `maxHeartbeats 4000000`:
three numeral goals and three power-expression goals. All six corresponding
default-option probes fail at the heartbeat limit. No `maxRecDepth 1024` is
needed, and no exponent threshold is raised or warning suppressed.

The [production resource record](bench-results/hex-primality-fallback-options-issue-10373.json)
wraps the actual plain tactic with observational counters under the standard
import. All six default-option invocations fail at the heartbeat limit, while
all six invocations with only `maxHeartbeats 4000000` succeed. Successful counter
deltas, rounded to user heartbeat units, are:

| Input | Numeral | Power expression |
|---|---:|---:|
| secp256k1 | 362604 | 362604 |
| P-384 | 441795 | 441838 |
| Curve448 | 287778 | 287839 |

These deltas include the small observation wrapper and are not measured minimum
limits. The three `Nat.Prime` power proofs also pass with the same finite option
in `FieldMathlib.lean`; their counter deltas are not separately measured.
The record retains the actual warnings and every complete suggestion.
The [two failed harness-compilation observations](bench-results/hex-primality-fallback-options-harness-issue-10373.json)
are also retained: a missing public import prevented tactic execution, so they
are not classified as heartbeat failures.

Reproduce current policy comparisons and production resource observations with:

```sh
python3 scripts/bench/primality_fallback_sweep.py --phase native \
  --output /tmp/fallback-native.json
python3 scripts/bench/primality_fallback_sweep.py --phase elaboration \
  --output /tmp/fallback-elaboration.json
python3 scripts/bench/primality_fallback_sweep.py --phase replay \
  --certificates /tmp/fallback-native.json --output /tmp/fallback-replay.json
python3 scripts/bench/primality_fallback_options.py \
  --output /tmp/fallback-options.json
lake build hexprimality_field_probe
.lake/build/bin/hexprimality_field_probe fallback NUMBER
```

The drivers reject existing output files. To reproduce the exact historical
measurements, use the recorded baseline and embedded source snapshots. The
production implementation retains the original `Construction.run` failure API,
adds construction-only subject diagnostics, and exposes `Construction.retry`
for the bounded complete retry. Registration uses `ConstructionExtension`
version 1 and `Hex.Nat.ecmConstructionFactor`; ordinary `SearchExtension`
version 3 and `intFactorSearch` remain separate.

Exact automatic suggestions, the registered-ECM exhaustion guard and Mathlib
power-expression proofs belong to `HexIntFactorFieldConformance`. The ordinary
conformance targets cover absent/malformed registrations, explicit and supplied
certificate precedence, composites, zero and nearly exhausted allowances,
recursive failures, rejected factor data, random-state advancement and event
order. Manual native benchmarks retain explicit targets and add automatic
construction targets with expected attempt hashes 417, 304 and 326. The ordinary
bench suite retains the fixed checker targets.

The [integrated ECM resource observations](hex-primality-ecm-stage2.md#construction-execution-and-shared-schedules)
cover automatic fallback with invocation-local schedules from #10374. They
preserve the exact suggestions and confirm that the three ECM fields still need
an explicit caller heartbeat allowance. The earlier measurements above retain
their original per-curve enumeration implementation.
