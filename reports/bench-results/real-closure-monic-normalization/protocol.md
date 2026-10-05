# Monic-clean production packing

The input tower starts with alpha₀ = 2 and successively selects the positive
root alphaᵢ of `(X² - alphaᵢ₋₁)(X - 3)` in `(0,2]`. These monic defining heads
have clean coefficients, and every actual `Algebraic.Context.canReduce` flag
must be true. Use production `Algebraic.Element` arithmetic/packing throughout,
without an extra eager remainder or an irreducibility fast path.

At depths 1 and 2, compute `(1 + alpha)^m / (alpha - 3)` for
m = 2, 4, 8, 16. The existing nested driver emits complete typed stored values,
defining heads and root/query graphs; ordinary native readers/replay must pass.
Independent pinned FLINT arithmetic uses Q(gamma), gamma^(2^depth) = 2,
with alphaᵢ = gamma^(2^(depth-i)). It checks each selected definition,
original value and sign, enabled reduction flags and stored degree bounds.

Collect six fixed trial-major rounds in depth-major, then increasing-m order
through the eight `Measure.Depth{1,2}.monic{2,4,8,16}` lean-bench registrations.
Use the existing fixed runner, one measured outer repeat per invocation and
`min-total-seconds = 0.5`; each child auto-tunes its inner repeats. Acquire one
automatically selected CPU lease and inherit affinity in the children.
All 48 completed exports, logs, statuses and host activity are retained.
No quiet-core check, sample exclusion or rerun is authorized by this protocol.

Preparation precedes timing. The measured body retrieves its actual typed
input through IO, performs product/division using production packing, and
encodes/hashes the stored result. Final query evidence and native reading/
replay are outside timing. Expected result hashes are bound to the independently
checked untimed endpoints before collection. Freeze the protocol/source commit,
record it beside the target build and executable SHA-256, and retain the exact
registration source, compiler/dependency pins and all functional endpoints.

Report every per-call observation (`total_nanos / inner_repeats`), full ranges,
medians and inner-repeat counts, together with stored coefficient degrees/bits,
value/query bytes and graph nodes/occurrences. These fixed-family observations
make no asymptotic claim and are not a matched comparison with the nonmonic
family: its roots and defining heads differ. Repeated zero tests, separate
scalar/kernel counters, the three-way policy/head/irreducibility attribution,
and the other required Phase 4 families remain separate obligations.
