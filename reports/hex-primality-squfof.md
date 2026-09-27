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
contains three varied-gap balanced semiprimes at each of 32, 40, 48, 56, and
64 bits; six retained balanced inputs from the existing Brent-rho evidence;
and unbalanced, prime, square, power, smooth-`p-1`, table, and named-trace
controls. Its semiprime factors are independently checked by deterministic
64-bit Miller–Rabin, and the [oracle](../scripts/oracle/squfof_divisors.py)
checks each emitted factor using Python integer division. It requires
completion for every committed semiprime and trace case at the 262144-step
cap. The corpus is a regression set, not a completeness claim.

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

The [261 native samples](bench-results/hex-primality-squfof-native.jsonl) retain
the input, outcome, divisor, counters, caps, elapsed nanoseconds, trial, arm,
and host/CPU context. The [32 additional completed cap samples](bench-results/hex-primality-squfof-pilot.jsonl)
are retained separately. Every reported factor in both files passes independent
division; the oracle checked 322 corpus and sample records in total. The
measurement host was `chungus2` (AMD EPYC 9455, Lean 4.34.1); the selected
CPU, load, executable hash, corpus hash, and exact schedule are in the raw
context records. Host activity was recorded and no completed sample was
discarded.

## Observations

All 21 semiprimes completed at each ascending cap, and all 21 completed under
the reversed 262144-step policy. The 61-bit prime exhausted all 16 slices:
1,048,576 recurrence steps at 65536, 2,097,152 at 131072, and 4,194,304 at
262144, with no factor. Brent rho also exhausted its eight restarts on that
prime for all three seeds. These capped failures are part of the raw results.

The table gives the first ascending 65536-step run's counters and the median
of each arm's two adjacent raw timings in milliseconds. All divisors shown
were independently checked by division.

| Balanced input | `n` | SQUFOF attempts / steps / peak | Divisor | SQUFOF ms | rho ms |
|---|---:|---:|---:|---:|---:|
| 32 near | 3785075929 | 1 / 97 / 0 | 61463 | 0.020 | 0.063 |
| 32 mid | 3896078107 | 1 / 1412 / 5 | 61463 | 0.132 | 0.020 |
| 32 wide | 4249736209 | 1 / 7 / 0 | 61463 | 0.011 | 0.050 |
| 40 near | 966520998899 | 1 / 2 / 0 | 983063 | 0.009 | 0.686 |
| 40 mid | 996620421833 | 1 / 4064 / 2 | 983063 | 0.314 | 0.834 |
| 40 wide | 1087211643409 | 1 / 7 / 0 | 983063 | 0.011 | 0.190 |
| 48 near | 247393482185653 | 1 / 2024 / 1 | 15728681 | 0.166 | 1.044 |
| 48 mid | 255122461656967 | 1 / 4588 / 1 | 15728681 | 0.361 | 1.363 |
| 48 wide | 278315534256499 | 1 / 4427 / 0 | 15728681 | 0.349 | 0.823 |
| 56 near | 63331911535168729 | 1 / 18376 / 2 | 251658263 | 1.419 | 7.267 |
| 56 mid | 65311005970269011 | 1 / 28933 / 0 | 251658263 | 2.220 | 10.268 |
| 56 wide | 71248365779681809 | 1 / 7 / 0 | 251658263 | 0.012 | 10.032 |
| 64 near | 16212959431627901207 | 1 / 2 / 0 | 4026531853 | 0.016 | 21.084 |
| 64 mid | 16719613763203891499 | 2 / 121182 / 1 | 4026531853 | 53.426 | 19.296 |
| 64 wide | 18239578964471317819 | 1 / 57066 / 1 | 4026531853 | 22.076 | 26.041 |

Across the 21 semiprimes, SQUFOF has the lower paired median on 19; rho has
the lower paired median on the 32-bit mid-gap and 64-bit mid-gap inputs. The
retained nearly equal factors often produce an immediate square form, so these
counts do not establish a portfolio benefit. On the 64-bit mid-gap input,
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
