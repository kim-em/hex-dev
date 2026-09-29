# Ordinary-kernel replay with nested coefficients

These probes check supplied BKR graph evidence over actual iterated
`RationalFn` fields. They use the existing lawful field and equality instances,
ordinary arithmetic, and the existing infinitesimal sign operation. Acceptance
and rejection are proved by `decide +kernel` after unfolding the checker
boundary. The axiom guards permit only `propext`, `Classical.choice` and
`Quot.sound`.

## Arithmetic boundary

The logical definitions of planned multiplication, squaring, field division,
gcd and extended gcd reduce to the existing reference polynomial operations.
The native definitions retain the existing Karatsuba, Newton and half-gcd
engines through generic, proved `@[csimp]` equalities. The public agreement
theorems preserve the exact quotient, remainder, gcd scaling and Bezout
coefficients. Exposed default plans let the kernel reach those logical bodies
inside rational-function arithmetic.

This supplies the schoolbook logical closure required by
[hex-poly-fast](../HexPolyFast/SPEC/hex-poly-fast.md#kernel-exposure-and-trust).
It introduces no new arithmetic algorithm or coefficient instance. The clipped
Karatsuba interface is outside this change.

## Supplied evidence

At depth zero, the supplied generator, square and double are `1`, `1` and `2`.
At depth `i`, the coefficient field is the rational-function field over the
previous field, with positive infinitesimal variable `εᵢ`. Supply these literal
polynomial numerators with denominator one:

- `gᵢ = εᵢ(gᵢ₋₁ + εᵢ)`;
- its square: coefficients `[0, 0, gᵢ₋₁², 2gᵢ₋₁, 1]`;
- its double: coefficients `[0, 2gᵢ₋₁, 2]`.

The fixture stores the square and double recursively as coefficients; it does
not run multiplication or a certificate producer to prepare them. The newest
variable and preceding field both occur in the data.

The root polynomial is `P=X` on the whole line. One leaf contains all three
sign candidates for the query `gᵢ`, with counts `[0,0,1]`, three supplied
Tarski-query chains, and a literal scaled inverse. A parent for the two queries
`[gᵢ,gᵢ]` has two edges referring to that same leaf. This exercises the existing
same-level graph sharing over nested coefficient types.

Acceptance verifies the literal field identities, endpoint signs, query
bindings, matrix identities and child support evidence. Arithmetic rejection
changes one positive initial scale from `1` to `2`; context, endpoints, queries,
matrices and reported signs remain unchanged. Rejection therefore needs the
polynomial identity check. The separate stale-context probe changes the leaf's
context and exercises early rejection.

The ordinary CI target `HexSignDetMathlibProofProbe` includes acceptance and
arithmetic rejection at depths one and two, and stale-context rejection at
depth one. The explicit manual target `HexSignDetMathlibNestedProofProbe`
contains the more memory-intensive depth-three proofs.

## Measurement protocol

`scripts/bench/sign_det_nested_kernel.py` uses the shared fresh-module harness.
It compares each proof module with a module having the same imports and no
proof body. Imports are warm; only that module's generated outputs are removed
before each measured build. Six trial-major rounds rotate the seven pairs and
alternate adjacent `AB`/`BA` order. The automatically selected CPU is leased,
not required to be idle. Raw wall times, child CPU times, peak RSS, compiler
output, axiom inventories, source hashes and host context are retained.

For example, from a clean checkout with warm dependencies:

```sh
python3 scripts/bench/sign_det_nested_kernel.py --samples 6 --timeout 300 \
  --output /absolute/path/outside/the/repository/nested-kernel.json
```

Each completed arm is flushed to the accompanying `.samples.jsonl`, including
failed arms. These are fresh-module observations: they include elaboration,
checker reduction, kernel verification and artifact writing. The paired delta
is not an isolated kernel timer or an asymptotic complexity result. This
protocol has no scientific acceptance budget inferred from its timeout.

## Scope

These probes do not construct a shared graph of coefficient-sign proofs across
field levels. They do not prove JSON byte roundtrips or apply the mathematical
root-count theorem to an ambient real closed model. Those are separate
obligations, as are the full Phase-4 gates and the required Tau Ceti Thom
foundations. See also the
[native nested-field conformance](sign-det-nested-fields.md) and
[semantic theorem application probes](sign-det-semantic-probes.md).
