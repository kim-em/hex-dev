# Monic-clean operation counts

Build one isolated diagnostic binary from the committed ordinary Lake target
using `scripts/bench/build_nested_normalization_counts.py`. The existing
observer wraps actual polynomial gcd/xgcd workers and Lean/GMP integer gcd
entries; callback counters are grouped by predecessor depth. Forwarding
wrappers are excluded, and different abstraction layers are never summed.
This binary supplies counts only, with no timing interpretation.

Run exactly the depth-one and depth-two m = 16 monic endpoints once each,
using `monic depth 16 trace`. Retain stdout, stderr, the diagnostic build
manifest, generated-C source hashes and both executable hashes. Workload
markers exclude context preparation, final queries and serialization from
counters. Check emitted workload hashes/values against the previously checked
functional endpoints and use the independent FLINT oracle to validate values,
signs, defining heads and top-level callback counts. Retain every completed
run; do not retry for a preferred count.

The 48 timing observations remain bound to their original uninstrumented
source/executable and protocol. These new diagnostic observations neither
replace those timings nor extend their measured boundary. Counts apply to
these two concrete inputs, not a general asymptotic model or all required
Phase 4 families.
