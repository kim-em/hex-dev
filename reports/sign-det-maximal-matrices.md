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

Both registrations use six fixed trial-major rounds, a 100 ms repeat target and
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

No scientific observations are recorded in this initial declaration.
