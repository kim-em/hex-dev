# Public divisor enumeration measurement protocol

This original campaign is exhausted. The [corrected ownership protocol](hex-int-factor-divisor-protocol-2.md)
registers the subsequent finite campaign; its results do not replace these attempts.

This protocol registers a mode-1, two-sided `τ log₂ τ` claim for public
`Hex.Nat.divisors`, including generation, sorting and array materialization.
It supplements the existing IntFactor package. Phase 4 remains incomplete
until the supplement passes and has an inclusive profile. The bridge APIs
`divisors_eq`, `divisors_list_eq` and `numDivisors_eq_card` transport this
operation; their computational owner is `HexIntFactorBench.runDivisors`.
Publication is outside this protocol.

## Family and derivation

Use the squarefree products of the first 6, 8, 10, 12, 14 and 15 table primes:
`τ = 64, 256, 1024, 4096, 16384, 32768`. The primes are
`2,3,5,7,11,13,17,19,23,29,31,37,41,43,47`. Subjects and every divisor are
below `2^63`, so multiplication/comparison do not cross a `Nat` limb regime.
Opaque checked factorizations are selected by `divisorInputForCount` before
the harness starts timing. No factor search or certificate checking is timed.

`DivisorEnumeration.values` recurses into the tail before extending: each
existing value `d` becomes the consecutive pair `[d, d*p]`. Thus the first
prime varies fastest. The generated order is generally unsorted. The total
number of generated cells and multiplications is a geometric sum, Θ(τ).
Temporary power lists, mapping and flat-mapping allocate Θ(τ) cells as well.

The compiled sort is `List.mergeSortTR₂` (the `csimp` replacement in the
pinned Lean toolchain's `Init/Data/List/Sort/Impl.lean`). Both mutually
recursive orientations split balanced halves down to singletons. For
`τ = 2^k`, `splitRevAt` visits exactly `τ/2` cells per level, for exactly
`k` levels. This gives a Θ(τ log τ) lower bound independent of comparison
order or interleaving. A merge at a node of size `m` uses between `m/2` and
`m-1` comparisons for equal halves, and linear traversal/allocation. Together
these give the matching upper bound. Reversing the first half changes order,
not this recurrence. `toArray` and the harness's complete array checksum are
linear. The model follows structural work, not a fit to observed timings.
The public SPEC's worst-case `O(τ log τ)` contract is unchanged.

`python3 -m scripts.bench.divisor_model` reconstructs the exact generated
order and the two orientations of `mergeSortTR₂`; its operation counts are
in `bench-results/hex-int-factor-divisor-operation-counts.json`. These are
algorithm diagnostics, not native performance measurements. Allocation and
runtime constants can affect the finite-range timing; an inclusive native
profile must establish their shares before acceptance is declared complete.

## Measurement and acceptance

Commit the registration, collector and this protocol before acceptance runs.
Use the repository's pinned LeanBench dependency and the registration defaults:
seven independent child trials per rung, the exact six-rung custom schedule,
warm cache mode, `targetInnerNanos = 1000000000`, `maxSecondsPerCall = 10`,
`signalFloorMultiplier = 1`, and unchanged default slope tolerance `0.15`.
The harness doubles warmup probes from one call to a 1.953125 ms signal floor,
then jumps to a power-of-two batch targeting at least 500 ms. The default
`verdict_warmup_fraction = 0.2` drops the first of the six rungs: the verdict
range is τ = 256..32768. The τ=64 observations remain diagnostic and are
never discarded from the export. Retain all
returned trial points, including lower rungs trimmed by the harness verdict.
There is no extra internal hot-loop batch or discretionary warmup.

Every timed call invokes public `divisors`, hashes the entire returned array
and consumes the hash through `LeanBench.blackBox`. Hashing is inside this
harness's timed loop: it adds Θ(τ), and must be identified in the profile.
`divisor-audit` runs outside timing and exports the complete result at every
rung. The Python collector independently enumerates subset products, sorts
with Python's sort, compares every element and the subject, and checks every
trial's checksum against that audited result. Missing points, mismatched
hashes, incomplete schedules and any verdict other than
`consistent_with_declared_complexity` reject the supplement.

Use designated shared host `chungus2`, logical CPU 7 (and record its SMT
sibling from sysfs). Build before timing, and run no concurrent local build or
profile. `core_telemetry.py` pins measured descendants to CPU 7 and runs its
monitor off that physical core. Sample every 250 ms. Retain host/core state,
load, pressure, raw scheduler samples and timed-region sidecars. Its existing
independent contamination criterion is aggregate foreign-CPU plus sibling
busy time above 0.002 of the timed-region wall time, or missing/malformed
timed-region evidence. This is a sampling estimate, not proof of isolation;
frequency and allocator variation remain possible even for admissible runs.
A spread, verdict or inconvenient timing is never a contamination criterion.

One acceptance attempt is prescribed. Only independently flagged contamination
permits one replacement of the **entire** attempt, for a maximum of two total.
Retain both attempts if replacement occurs, including the raw export and
verdict of the contaminated attempt. No replacement follows an admissible
inconclusive result, validation error, subprocess failure or timeout. Every
admissible attempt must pass; no selection of a favorable trial or run.
If both attempts are contaminated, the remaining dependency is an admissible
measurement window under this exact protocol. Keep Phase 4 incomplete.

From a clean committed tree:

```sh
python3 scripts/bench/intfactor_phase4.py --divisors --cpu 7 \
  --output reports/bench-results/intfactor-divisors-attempt-1.json
```

For an authorized contamination replacement, retain attempt 1 and use the
same command with `attempt-2.json`; commit the retained first attempt before
running so the clean-tree check still applies. Each output has a sibling
`.json.attempt/` directory with raw exports, stdout/stderr, telemetry and
sidecars. Never reuse an output path. `--report ARTIFACT` renders only accepted
records. All rejected records remain explicitly rejected.

Collect an attribution-only profile at `τ=32768`, with a five-second target,
after the unprofiled attempt. Retain the filtered profile, raw profile,
symbol sidecar, capture commands and inclusive summary in repository artifacts.
Profiling is diagnostic and never substitutes its instrumented timings for
acceptance trials. No alternate evidence mode is preregistered: mode 1 has an
independent derivation, so modes 2 and 3 are unavailable as fallback labels.

## Contrary evidence

The old registration commit is `8b54275eb34be820b3aa416306e58d9fb0fe41a5`.
Its initial full collector run returned `runDivisors: verdict=inconclusive`.
The collector deleted the temporary raw export before rejecting and produced
no final artifact. Recovery here uses the committed registration and the
[original issue record](https://github.com/kim-em/hex-dev/issues/9619#issuecomment-5494874295),
not another session's worktree or temporary files. The original raw samples
are unavailable in that record and cannot be reconstructed.

The subsequent diagnostic run returned `consistent_with_declared_complexity`,
`cMin=12.052`, `cMax=14.181`, `β=+0.016`. Its largest-rung trials were
8.731, 6.667 and 6.970 ms (about 29.6% spread). Both outcomes are retained as
contrary diagnostic evidence; neither is acceptance here. They do not identify
host interference, allocation/runtime variation or model error as the cause.
The present structural derivation removes the unsupported assumption that
this family necessarily incurs worst-case merge comparisons. It does not
explain away either old timing result. The seven-trial, telemetry-controlled
experiment tests the unchanged cost model without widening tolerance.

Exploratory capture artifacts are retained in
`bench-results/intfactor-divisors-exploration.tar.gz` with provenance in the
adjacent JSON. `samply record` produced no samples on this host despite usable
perf counters; an independent `perf record` captured 2912 samples. Its
whole-process leaf view places merge, reverse and split at about 47% and
`lean_apply_2` at 16%, supporting investigation of the sort path. This is not
an accepted inclusive profile. The final profile may use `perf record` and
`samply import` with the same timed-region filter, calibration and sensitivity
checks, keeping raw captures and commands. This changes profiling transport,
not the operation, unprofiled timing protocol, or acceptance tolerances.

## Campaign disposition

Both allowed attempts were contaminated (4.8737% and 5.1226% against the
0.2% ceiling). The campaign is exhausted and neither raw consistent verdict
is accepted. The current report records the exact remaining blocker. The
collector additionally records the built benchmark's hash immediately after
building; the rejected captures retained wrapper hashes but lacked that direct
binary hash, and are left unchanged. No new acceptance timing was taken after
this correction.

The inclusive profile's failed initial clock calibration is retained alongside
its successful reprocessing. For samply's perf import, the raw sample sequence
independently fixes the timestamp origin. `normalize_perf.py` requires every
imported timestamp to equal its raw counterpart plus one offset (within one
nanosecond) before correcting `meta.startTime` using the independently recorded wall/monotonic
spawn anchor. All relative sample, marker, counter and lifetime timestamps
remain unchanged, so the profile has one coherent clock. The unchanged
timed-region filter then runs. It does not fit to
timed boundaries. ELF symbol intervals and binary hashes are retained by
`elf_symbols.py` when samply import omits a presymbolication sidecar.
