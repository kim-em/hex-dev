# HexGenericRank performance

## Registered workloads and ceilings

The `symbolic` family registers producer and compiled checker separately for
all 216 combinations of dimensions 2/4/8, variables 1/2/4/8, factor support caps
1/4/16 and total degree caps 1/2/4, at full and low rank (432 registrations).
Each fixed mode-3 registration has a preregistered 5 second per-call ceiling,
five measured repeats and a 1 millisecond inner-loop floor. Checker certificates
are prepared before its timer. The fixed trial-major schedule is lean-bench's.

Full-rank inputs have a polynomial first row and the remaining identity rows.
Low-rank inputs factor through rank n/2; their leading block is diagonal with
one polynomial diagonal entry. These are structured support-growth workloads,
not a model for worst-case minor swell. Support/degree labels bound the factor
polynomials; multiplication can increase realised entry support and degree.
Untimed instrumentation records the maximum entry support across both actual
producer passes, including the augmented pivot block.

Comparator: **no-comparable-surface-in-named-comparator**. python-flint has no
multivariate polynomial matrix surface; SymPy is used only as an exact oracle.
