# Complete-support matrix solving and checking

These benchmarks isolate the actual `solveSystem` and `System.check` operations
on complete ternary moment systems. They measure the matrix phase required by
HexSignDet, independently of the polynomial-query phase. They do not measure
root isolation, Tarski queries, recursive BKR production or descriptor operations,
and do not close the separate rank-library performance obligation #10352.

For query count `s`, all `r = 3^s` sign words occur exactly once. Rows are all
words over `[0,1,2]`; columns are all words over `[-1,0,1]`, in the library's
fixed order. Each moment is the sum of the corresponding entry over these
observations. Preparation calls the existing solver, checks every count is one,
and checks both exact integer identities. The solve callback repeats that actual
solve and returns the ordered table hash. The check callback checks the supplied
system using the existing checker. Neither supplies polynomial coefficients or
implements a new query kernel.

Untimed input inspection compares the entire system with the polynomial
reference producer on the
existing maximal-support interpolation family for `s=1,2,3`. No polynomial
comparison is claimed at `s=4,5,6`; their larger matrices represent the same complete
finite moment problem. The independent part of this comparison is that the
Tarski-query moments equal the finite observation sums, in the same row and column
order. Both paths use `solveSystem`, so matching inverse witnesses are a consistency
check rather than an independent inverse oracle. Output hashes are correctness
guards, not proofs. They are bound to deterministic prepared inputs through the
recorded source revision, executable hash and parameter; the child protocol does
not export a separate input digest.

## Cost model derived before measurement

Both callbacks execute `System.check` on an accepted system. It constructs the
moment matrix and computes the dense product of the supplied inverse and moment
matrix. The matrix implementation visits all `r^3` multiply/add pairs, including
zeros. Column distinctness and entry construction take at most `O(r^2 s)` work;
the remaining matrix-vector check takes `O(r^2)` scalar operations. Thus the
checker has `Θ(r^3) = Θ(27^s)` integer coefficient operations.

The solver additionally builds a rational matrix, performs Gauss-Jordan inversion
in `O(r^3)` rational coefficient operations, recovers counts, constructs the
common-denominator integer witness, and runs that same cubic check. This gives
`Θ(r^3)` coefficient operations for the complete solve as well. These laws count
arithmetic operations; they are not constant-bit asymptotic claims. The inventory
records actual inverse, denominator and moment bits. The chosen schedule
`s=1,2,3,4,5` gives matrix sizes `3,9,27,81,243` and samples a finite range.

Both registrations use mode 1 (two-sided parametric), with the source-derived
coefficient-operation law above. Both use six fixed trial-major rounds, a 100 ms repeat target and
an operational 180 s child timeout. The shared harness gives each operation its
own verdict. The timeout is not a scientific absolute performance budget.
An inconclusive observation remains an outstanding gate; it is never promoted
by compilation, fixture equality or a successful smoke check.

## Matrix dimension as the parameter

The `runSolveDimension` and `runCheckDimension` registrations call the same
solver and checker, preparing the same complete ternary systems. Their
parameter is the literal matrix dimension `r`, with schedule
`3,9,27,81,243,729` and corresponding query counts `1,…,6`. The declared
law is the same `Θ(r³)` arithmetic-operation bound. Each registration retains
six trial-major rounds, a 100 ms repeat target and a 180 s operational timeout.
Preparation and untimed validation remain outside each callback.

This parameter gives the fitter a substantial logarithmic range, including
after its fixed warmup fraction. It does not make integer/rational bit costs
constant, establish general Tarski-query complexity or guarantee a conclusive
verdict. The original query-count registrations and archived observations
remain separate. No original sample is relabelled or removed.

Use `inspect-maximal-matrix-dimensions` to verify all six inputs. Literal
inverse identities, multiplicities, moment values and sizes are checked for
every dimension; the independent polynomial-moment comparison remains limited
to query counts one through three. The dimension-parameter collector validates
72 expected samples and the actual row/column dimension associated with every
raw parameter:

```sh
python3 scripts/bench/sign_det_maximal_matrix.py --parameter matrix-size \
  --output /absolute/path/outside/the/repository/matrix-dimensions
```

The collector's default `--parameter queries` preserves validation of the
original schedule and its `27^s` declaration. The dimension mode records schema
v2, its parameter choice and the `r^3` declaration. It introduces no new
matrix implementation, query primitive or CI job.

## Retained dimension-parameter collection

The [dimension collection](data/sign-det-maximal-matrices/ff35bd9da-dimensions/metadata.json)
contains all 72 completed samples from clean source
`ff35bd9daacfca51b62f931d5b6d7afd9e143614` on `chungus2`, leased CPU 41.
Both arms pass schedule, exact-result, timing and provenance validation.
Source, executable and pinned harness bindings agree before and after
collection. All 257 recorded source hashes were checked against the measured
revision. The [source archive](data/sign-det-maximal-matrices/ff35bd9da-dimensions/archive.json)
reconstructs that checkout from main ancestor
`69c2c363f9789e497f5106cf65756253b420809b`; the measured commit need not
survive the squash merge. The archive retains every export and child log,
including the untimed inventory.

| Matrix size | Queries | Solve median (ms) | Check median (ms) |
| ---: | ---: | ---: | ---: |
| 3 | 1 | 0.016546 | 0.002246 |
| 9 | 2 | 0.270661 | 0.021804 |
| 27 | 3 | 4.627596 | 0.253301 |
| 81 | 4 | 80.826140 | 3.252235 |
| 243 | 5 | 1449.698225 | 51.440856 |
| 729 | 6 | 26580.263278 | 991.465444 |

The fitter drops one leading parameter under its unchanged warmup setting.
It fits the normalized ratios `time/r³` over `r=9,…,729`, with sufficient
logarithmic span. Both verdicts remain **inconclusive**: solve has normalized
slope `−0.384273` and ratio range `68.608306…371.276430` ns; check has slope
`−0.563903` and range `2.559146…29.910025` ns. These slopes describe the
normalized ratios, not the unnormalized timing exponent. Both exceed the
fixed `0.15` tolerance in the faster-than-declared direction. This resolves
the previous insufficient-range limitation without establishing the cubic
wall-time gate. The [summary](data/sign-det-maximal-matrices/ff35bd9da-dimensions/summary.json)
reports no validation errors. The collector's exit status 1 records these
inconclusive verdicts, rather than lost or failed samples.

At size 729, median process peak RSS is 119.785 MiB for solve and 119.406 MiB
for check. These observations include input preparation and process startup;
they are not allocation counts or isolated callback memory. All allocation
counters remain absent. Smaller sizes use repeated inner calls; solve uses
one call per sample at sizes 81 and above, while check uses one at sizes 243
and 729. The [table data](data/sign-det-maximal-matrices/ff35bd9da-dimensions/table.json)
retains timing and resident-set medians for all six sizes.

No model, fit setting or completed sample was changed after this observation,
and no unchanged rerun was used. The declared law counts scalar operations;
unequal scalar costs and lower-order terms remain possible explanations of
the finite timing behavior, not established conclusions. The earlier profile
at size 243 supplies attribution for that input only. General bit-cost
analysis and the remaining Phase-4 obligations are still outstanding.

## Collection

Build with `lake build hexsigndet_bench`, commit the measured sources, then run
`python3 scripts/bench/sign_det_maximal_matrix.py --output <fresh-directory>`.
Use a worktree with an isolated executable. The collector leases one CPU,
records host load, validates the pinned clean harness and build freshness,
archives reconstructible sources and retains both scheduled arms before judging
results. It checks source, executable and harness bindings again afterward.
There is no idle-core preflight, sample filtering or automatic rerun.

## Retained collection

The [a7c9b34fb collection](data/sign-det-maximal-matrices/a7c9b34fb/metadata.json)
records all 60 successful scientific samples in six rounds on `chungus2`, leased
CPU 83. The source revision, executable and clean pinned harness match before
and after collection. The archived patch reconstructs every recorded source hash.
Both result sets pass the exact-result, schedule, timing and provenance checks.
The collector exits 1 because both harness verdicts are **inconclusive**; there
are no scientific validation errors. Every completed sample remains unchanged.

| Queries | Matrix size | Solve median (ms) | Check median (ms) |
| ---: | ---: | ---: | ---: |
| 1 | 3 | 0.016488 | 0.002248 |
| 2 | 9 | 0.269938 | 0.021710 |
| 3 | 27 | 4.604734 | 0.250973 |
| 4 | 81 | 79.824321 | 3.207957 |
| 5 | 243 | 1435.856224 | 51.128041 |

These are complete-solve and supplied-system-check timings. Preparation is outside
the timed callbacks; child resident-set observations include preparation and runtime
startup, and must not be described as isolated matrix allocation or peak live heap.
Neither operation has an allocated-byte counter.

The harness omits parameters below 2 when forming normalized ratios. Its fixed
20% warmup setting drops zero of the four remaining ratios, as recorded in both
exports. The retained parameter range is `s=2,…,5`, whose logarithmic span `log(5/2)` is less than the
pinned fitter's minimum span 1. Consequently it reports no slope and uses its
unchanged multiplicative range check. The normalized median constants vary by
3.70 for solve and 8.36 for check, exceeding its 1.5 narrow-range allowance.
This is the faster-than-declared direction over these finite inputs, and remains
an outstanding performance gate. It is not evidence of a passing upper bound;
these registrations did not qualify for that mode.

The source-derived cubic scalar-operation count is separate from the unresolved
wall-time scaling. In particular, the rational elimination skips zero multipliers.
The existing [one-column elimination inventory](data/sign-det-compare/6f07e03db/inventory-full.jsonl)
uses this identical moment matrix and visits 6, 54, 378, 2430 and 15066 nonzero
multipliers. Re-running `inspect-full` with the measured executable reproduces
that inventory exactly. These finite counts equal `2(6^s - 3^s)`. Since each
elimination updates two rows of length `3^s`, it executes
`4(18^s - 9^s)` rational multiply/add pairs in those row additions, alongside
the cubic integer check. The rational and integer operations need not have equal
wall-time costs. The separate size-243 check median is about 3.6% of the solve
median; this is a comparison of separate timings, not profile attribution of
3.6% inside a solve call. The cubic scalar-operation bound alone does not predict
which part dominates at these finite sizes.

The `inverseIdentityScalarPairs` inventory field is computed from the dense-loop
model (`r^3`), not a sampled operation counter. The elimination counts above come
from the existing one-column inspection of the actual row-reduction states.
At the largest solve inputs and largest check input, the harness uses one inner
call per sample; smaller inputs use repeated calls. All six completed trials at
each size are retained.

The current input sizes can expose lower-order overhead and
unequal costs of scalar operations; these possibilities are not established by
these timings. The profile below identifies the dominant phase for solve at `s=5`; a wider independently
planned schedule or a separately derived model for that phase is still needed
before correcting its wall-time declaration. The check schedule also needs a
wider range before its cubic term can be assessed. No fit setting or complexity law has been changed to obtain a
passing result. No unchanged rerun has been collected.

This matrix-phase evidence does not establish the growing-degree polynomial query
track, maximal-support end-to-end production, ordinary-kernel matrix replay costs,
allocation accounting, or full #10377 Phase-4 completion. The existing interpolation
fixtures and earlier untimed inventories remain unchanged.

## Representative solve profile

The [retained size-243 capture](data/sign-det-maximal-matrices/profile-4540051d3/metadata.json)
profiles one actual cold solve from clean source `4540051d3`, with the same
executable hash as the scientific collection. It has one operation region and
the expected result hash. Profiling duration is not a scientific timing baseline.
Preparation, result consumption and process startup are outside the filtered
operation region. Raw perf data, recovered profiles, symbol information and an
unchanging copy of the debuggee are retained in the durable directory named by
[the analysis manifest](data/sign-det-maximal-matrices/profile-4540051d3/analysis.json).
The source archive, collector, region sidecar, tool bindings and analysis commands
are committed alongside the summaries. The filtered profile and symbol table are
also committed, so the caller analysis can be replayed without the host archive;
re-importing the original perf capture still requires that archive.

All 577 raw/imported timestamps agree with one common origin and zero residual.
The parent wall/monotonic anchor was captured immediately before launch. Filtering
retains 281 operation samples, rejects 290 bench-thread samples outside the
region, and reports zero other-thread samples inside. Six other-thread samples
are outside the region. The timing-window confidence
and ±5 ms leaf-distribution sensitivity checks pass. The timing-window calibration
residual is 0.841 ms against its 20.1005 ms effective limit.

| Function with inclusive samples | Samples / 281 | Share (%) |
| --- | ---: | ---: |
| Matrix inversion / row reduction | 263 | 93.6 |
| Row addition | 260 | 92.5 |
| Integer system checker | 10 | 3.6 |
| Natural-number gcd | 228 | 81.1 |
| `mpz(uint64)` construction | 170 | 60.5 |

These are overlapping inclusive shares, so they must not be added. The ten
checker samples give limited precision; their agreement with a separately timed
check/solve ratio is not evidence beyond the individual observations. This profile
supports rational elimination as the dominant phase at `s=5`; the source's
cubic integer check is a small part of the complete solve here. It does not
establish the dominant phase at every size or justify an optimization by itself.

The shared leaf classifier reports 43.77% GMP, 29.89% allocator, 21.35% Lean
runtime, 0.36% Hex code and 4.63% other samples. Allocator CPU samples are not
allocated-byte measurements. The classifier groups Rat/Fin helpers under runtime,
so these categories must not be confused with the inclusive phase table.

A separate [caller-path check](data/sign-det-maximal-matrices/profile-4540051d3/stack-plausibility-v2.json)
finds no unexpected or unresolved callee beneath gcd, and every recovered GMP add/shift path
there has the uint64 constructor as its immediate caller. Of the 228 gcd samples,
224 also contain row addition. Of the 170 constructor samples, 168 are under gcd,
and 165 contain both gcd and row addition. These are sampled caller partitions,
not counts of executed gcd calls.

The linked runtime promotes machine-word natural operands into GMP values on
these constructor paths. This identifies runtime conversion overhead; it does
not establish that every other gcd operand is small or exclude operand-size work
elsewhere. The [pinned Lean constructor source](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/runtime/mpz.cpp#L40)
constructs the value from two 32-bit portions. Disassemblies from
the retained executable confirm that constructor calls GMP add and shift.
The [symbol record](data/sign-det-maximal-matrices/profile-4540051d3/constructor-symbols.json)
shows that the `C1Em` disassembly and `C2Em` profile symbol are aliases at the same
address, with the same size (132 bytes).
This checks specific stack concerns; timing-window confidence does not prove
unwind edges, and the path check does not validate every edge of every stack.
The captured runtime behavior is consistent with the pinned Lean implementation
of `mpz(uint64)`; no duplicated arithmetic implementation is introduced here.
