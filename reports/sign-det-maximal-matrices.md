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

Untimed input inspection additionally compares the entire system, including its
integer inverse and denominator, with the polynomial reference producer on the
existing maximal-support interpolation family for `s=1,2,3`. No polynomial
comparison is claimed at `s=4,5`; their larger matrices represent the same complete
finite moment problem. Output hashes are correctness guards, not proofs.

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

The harness drops the first parameter for its fixed 20% warmup trim. The retained
parameter range is `s=2,…,5`, whose logarithmic span `log(5/2)` is less than the
pinned fitter's minimum span 1. Consequently it reports no slope and uses its
unchanged multiplicative range check. The normalized median constants vary by
3.70 for solve and 8.36 for check, exceeding its 1.5 narrow-range allowance.
This is the faster-than-declared direction over these finite inputs, and remains
an outstanding performance gate. It is not evidence of a passing upper bound;
these registrations did not qualify for that mode.

The source-derived cubic scalar-operation count is separate from the unresolved
wall-time scaling. The current input sizes can expose lower-order overhead and
unequal costs of scalar operations; these possibilities are not established by
these timings. A representative profile and a wider independently planned schedule
are needed before deciding whether the wall-time declaration or implementation
needs correction. No fit setting or complexity law has been changed to obtain a
passing result. No unchanged rerun has been collected.

This matrix-phase evidence does not establish the growing-degree polynomial query
track, maximal-support end-to-end production, ordinary-kernel matrix replay costs,
allocation accounting, or full #10377 Phase-4 completion. The existing interpolation
fixtures and earlier untimed inventories remain unchanged.
