# Reduced and full sign-table construction

`runSmallReduced` and `runSmallFull` construct sign tables for the same prepared
root domain P=X²−1 on the whole line and s copies of X, with s=1,…,5. Both
use direct moment products. The timed bodies include query construction,
matrix solving and checked table production. The reduced arm checks recursive
support evidence; the full arm solves the entire ternary system. Untimed
preparation checks both tables against exactly two sign words, all negative
and all positive, each with count one. `inspect-small` separately verifies
literal dimensions and counts, not just matching result hashes.

The reduced arm declares Θ(s log s) on this two-root family: every balanced
node has a bounded matrix, and its query and sign slots are scanned in Θ(k)
work for a node containing k input polynomials. The full arm declares Θ(27^s)
scalar work from the dense inverse-identity check on the 3^s square moment
matrix. This is a finite-input wall-time model, not a bit-complexity claim for
arbitrary s. Rational row reduction may instead dominate; `inspect-full`
records the actual elimination updates and matrix dimensions to assess that
possibility. A model mismatch remains an inconclusive result, not a passing
upper bound.

`paired-small` uses the shared LeanBench sampler and summary for each arm. Six
fixed trial-major rounds keep the arms adjacent for every s and alternate
AB/BA order. Each completed arm is flushed before the next child. The Python
wrapper leases one CPU automatically, records host load as context, checks
that every child ran at the clean measured revision, validates the complete
sample stream and retains all verdicts. It never filters a completed sample
or automatically reruns an inconclusive result. Pairwise signed differences
and ratios are computed from adjacent samples before taking their medians.

This fixed-degree, fixed-coefficient family has support two. It does not cover
maximal support, growing degree or coefficient bits, nested field depth,
modulo-product comparisons, or descriptor operations. Child RSS includes
untimed preparation; allocation bytes and peak intermediate bits need separate
measurements. The larger sparse-family report covers s=64,…,2048 and is not
replaced by this reduced/full comparison.

## Recorded observations

The clean matched measurements and full-matrix inventory will be retained here
once collected from this source revision. Their raw streams, source and binary
hashes, and any model mismatch will be reported without changing the declared
models or discarding runs.
