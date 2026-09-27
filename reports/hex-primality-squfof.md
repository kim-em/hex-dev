# Bounded SQUFOF raw splitting

`Hex.Nat.Squfof.factor` is an explicit, deterministic splitter for inputs below
`2^64`. It uses the fixed ascending 16-multiplier schedule, exact `Nat`/`Int`
arithmetic, a bounded FIFO queue, and one combined forward/reverse step cap per
multiplier. A final validation gate checks every reported proper divisor. The
four public theorems prove divisor soundness and the attempt, step, and queue
bounds for all inputs and limits. The production factorization and certificate
dispatchers do not call this route.

## Corpus and protocol

The committed [corpus](../conformance-fixtures/HexPrimality/squfof-corpus.jsonl)
contains six varied-gap balanced semiprimes at each of 32, 40, 48, 56, and
64 bits. Three per size use independently drawn prime pairs with ratios from
about 1.26 to 1.55; the other three reuse one prime and include near-equal
pairs. Six more pairs retain earlier Brent-rho inputs. Four primes and
unbalanced, square, power, smooth-`p-1`, table, and named-trace controls fill
out the 47 cases. The historical `retained-57` label was corrected to
`retained-50` because its input is 50 bits; older raw files retain the old
label. Semiprime factors are independently checked by deterministic 64-bit
Miller–Rabin, and the [oracle](../scripts/oracle/primality_squfof.py) checks
each emitted factor by Python integer division. It requires completion for
all 36 semiprimes and the two trace cases at 262144 steps. The corpus is a
regression set, not a completeness claim.

The [compiled driver](../bench/HexPrimality/SqufofMeasure.lean) measures raw
SQUFOF and `Internal.rhoFactorCountedWith?`, excluding process startup from its
monotonic-clock interval. The [fixed schedule](../scripts/bench/squfof_evidence.py)
runs two trial-major adjacent `SQUFOF/rho` and `rho/SQUFOF` blocks, then the
additional policy arms. SQUFOF uses queue capacity 128, all 16 multipliers,
ascending 65536-step slices in the adjacent comparison, ascending 131072 and
262144 slices in the policy pass, and reversed order at 262144 steps. Brent rho
uses eight restarts, requested inner fuel 262144 capped by its existing
input-scaled `rhoRestartFuel`, and fixed seeds `1, 27, 10452`; the adjacent
comparison uses seed 1. These are raw splitters with different resource units.
The fixed caps and failure outcomes remain visible in every sample.

The [426 current native samples](bench-results/hex-primality-squfof-native-phase.jsonl)
retain each input, outcome, divisor, cap, attempt total, phase counters and
stop reason per multiplier, peak queue length, elapsed nanoseconds, trial,
arm, and host/CPU context. They include three one-multiplier trace boundaries:
17 forward steps exhaust, 17 forward plus seven reverse steps exhaust at 24,
and 17 plus eight succeed at 25. The earlier [261 native samples](bench-results/hex-primality-squfof-native.jsonl),
[32 pilot samples](bench-results/hex-primality-squfof-pilot.jsonl), and
[15 irregular-candidate samples](bench-results/hex-primality-squfof-candidates.jsonl)
remain as completed observations. The oracle checked all **781** corpus and
sample divisor records, all phase sums in the current samples, and all 752
corpus multiplier diagnostics without an arithmetic stop. The host was
`chungus2` (AMD EPYC 9455, Lean 4.34.1). The context records contain selected
CPU, load, source and executable hashes where recorded, and the exact schedule.
The latest source snapshot was dirty when measured; its source and binary
hashes identify it exactly. No completed sample was discarded.

## Observations

All 36 semiprimes completed at each ascending cap and under the reversed
262144-step policy. The 61-bit prime exhausted all 16 slices:
1,048,576 recurrence steps at 65536, 2,097,152 at 131072, and 4,194,304 at
262144, with no factor. Brent rho also exhausted its eight restarts on that
prime for all three seeds. The 32-bit prime filled the 128-entry queue in
some multiplier attempts. These capped failures are part of the raw results.

For the two adjacent raw timings at 65536 steps, SQUFOF has the lower paired
median on 28 of 36 semiprimes and rho on eight. On the 15 independently drawn
pairs, the split is nine to six. The reused-prime and near-equal cases favor
SQUFOF, sometimes finding an immediate square form; the current counts do
not establish a portfolio benefit. The raw file gives every per-input time,
failure, divisor, and phase counter. On the 64-bit mid-gap input,
raising the per-multiplier cap to 262144 changed the path from two attempts and
121182 total steps to one attempt and 185192 steps. Reversing the multiplier
order changes the work again; all per-input reversed counters are retained in
the raw samples. This is evidence for the explicit API only. Any default
dispatch proposal still needs the preregistered whole-portfolio comparison in
the SPEC.

## Forced-work scaling and cost attribution

The Mathlib-free `runSqufofFuel` registration uses a fixed 61-bit prime and
one multiplier, with fuel `512, 1024, 2048, 4096, 8192`. Each run exhausts
exactly its combined recurrence cap while the queue stays below 128. Its
independently declared linear model is the first applicable evidence mode:
fixed-size arithmetic and bounded queue work make recurrence fuel the varied
cost. The retained [lean-bench export](bench-results/hex-primality-squfof-fuel.json)
and [host record](bench-results/hex-primality-squfof-fuel-context.json) show
per-call times `82.501, 166.298, 324.313, 640.027, 1296` microseconds and a
two-sided **consistent** verdict (`β = -0.013`). The absolute times describe
this host only.

One representative `samply 0.13.1` profile used the compiled raw driver on
the forced 61-bit prime at 16 × 262144 steps (4,194,304 total). The 2033
main-thread samples were mapped to the binary's symbols. Inclusive cost in
`Squfof.search` was 2021 samples (99.4%); `nextForm` appeared in 905 (44.5%).
Leaf cost was approximately 51.5% allocation/free, 29.5% GMP arithmetic,
14.5% Lean runtime, 4.0% SQUFOF code, and 0.5% other. This attributes the
dominant raw-splitter cost to allocation and big-integer arithmetic within the
recurrence. The profile is a forced-work forward-heavy control; it does not
assign a separate reverse-phase fraction to successful inputs.
