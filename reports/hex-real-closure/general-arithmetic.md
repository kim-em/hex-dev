# General selected-root arithmetic: functional timing anchor

This compiled, Mathlib-free fixed benchmark records the cost of one runnable
arithmetic example. It makes no scaling claim and does not discharge the tower
performance requirements of #10378.

`Hex.RealClosure.Bench.runGeneral` validates the reducible polynomial
`(X²−2)(X−3) = X³−3X²−2X+6`. The interval `(0,4)` and negative first-derivative
sign select `√2`. Rational coefficients have denominator one and numerator
magnitude at most six. The call packs `X`, the nonliteral zero `X²−2`, and
`X−3`, checks addition cancellation, computes the local gcd/cofactor inverse of
`X−3`, and checks that its product denotes one. It includes descriptor
validation and the selected-sign queries used by these operations.

The fixed lean-bench registration performs a warmup and ten measured calls.
One CPU was selected using the shared host CPU lease, and all completed samples
were retained. The observed median was **5.539 ms**, with a range of
**5.490–5.618 ms** on the recorded host. All ten hashes equal the expected value
one. Peak RSS across the measured child processes was 63,876–68,184 kB; this is
process memory, not a per-operation allocation count.

The [export](general-arithmetic-anchor.json) retains every measured duration,
hash and runner metadata. The [log](general-arithmetic-anchor.log) retains the
harness output. The [context](general-arithmetic-anchor-context.json) records
CPU affinity, host load, source and executable hashes, and the exact command.
The recorded commit was dirty because the measured additions were not yet
committed; the hashes identify their contents.

Run `lake build hexrealclosure_bench`, then
`.lake/build/bin/hexrealclosure_bench run Hex.RealClosure.Bench.runGeneral`.

No speedup is inferred from older canonical-root measurements: this is a
single-arm observation. A formal evaluation still needs the specified depth
and coefficient families, nested sign/zero and BKR counts, splitting and
transport costs, clean/eager comparisons on identical semantic inputs, tower8
and MetiTarski workloads, and representative attribution. The current shared
selected-sign implementation repeats preparation for each nonconstant query;
a reusable prepared selected-root handle is requested in #10377.
