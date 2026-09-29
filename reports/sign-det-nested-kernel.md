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
variable and preceding field both occur in the data. These generators have
denominator one, so their costs do not represent nontrivial fraction
cancellation.

The root polynomial is `P=X` on the whole line. One leaf contains all three
sign candidates for the query `gᵢ`, with counts `[0,0,1]`, three supplied
Tarski-query chains, and a literal scaled inverse. A parent for the two queries
`[gᵢ,gᵢ]` has two edges referring to that same leaf. This exercises the existing
same-level graph sharing over nested coefficient types.

Additional depth-one/two probes supply `p/(p+1)`, `p/(p+2)`, their sum and
the first fraction's square through literal normalization certificates, where
`p=ε(γ+ε)` and `γ` is the preceding generator. Their Bezout identities are
checked by the kernel. Graph acceptance and rejection of a positive but wrong
square exercise nonunit-denominator multiplication. Separate arithmetic proofs
compute addition with distinct denominators and self-division with a nonunit
polynomial cancellation factor. The archived v1 seven-pair collection measures
the polynomial-generator family, not these additional fraction probes. The current
twenty-pair sweep also includes fraction arithmetic, graph acceptance/rejection,
and separate replay of all eight supplied normalization certificates. The
original `ofCert` declarations remain warm imports for those probes. Addition
uses distinct coprime denominators; nonconstant polynomial cancellation is
exercised by self-division.

Acceptance verifies the literal field identities, endpoint signs, query
bindings, matrix identities and child support evidence. Arithmetic rejection
changes one positive initial scale from `1` to `2`; context, endpoints, queries,
matrices and reported signs remain unchanged. Separate `ArithmeticCause` modules read the actual forged moment, prove every
chain guard before its initial identity passes, and prove that identity and
the chain replay fail while the original chain passes. Their costs are separate
from the graph rejection modules. The separate stale-context probe changes the leaf's
context and exercises early rejection.

The proof scripts use proved checker equalities to compute the uncached
query-chain specification. Child-entry sharing is retained, but the squarefree
chain is checked again for each moment; these timings do not measure the
native domain cache.

Each nonzero coefficient sign calls the predecessor sign twice. At depth `d`,
one sign may therefore make `2^d` rational sign calls; a zero numerator
short-circuits. Arithmetic adds further predecessor work. There is no additive
bound in depth or shared coefficient-sign evidence in these probes.

The ordinary CI target `HexSignDetMathlibProofProbe` includes acceptance,
arithmetic rejection and stale-context rejection at depths one and two, plus
the fraction probes. The explicit manual target
`HexSignDetMathlibNestedProofProbe` contains the more memory-intensive
depth-three proofs, including stale-context rejection. The full default
`lake build` does not include that manual target. Run
`lake build HexSignDetMathlibNestedProofProbe` after changing the nested inputs
or their arithmetic dependencies; allow roughly 18 GiB resident memory for
the observed depth-three acceptance module.

## Measurement protocol

`scripts/bench/sign_det_nested_kernel.py` uses the shared fresh-module harness.
It compares each proof module with a module having the same imports and no
proof body. Imports are warm; only that module's generated outputs are removed
before each measured build. Six trial-major rounds rotate the twenty pairs and
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

## Recorded costs

The clean source `6f332afb870644a553c712e0a4d1cec6784f14ee` supplied
42 adjacent pairs (84 completed arms) on `chungus2`, automatically leased
CPU 1, with one Lean thread. Lean is 4.35.0-rc3, Mathlib is
`d870b9068518a0870842d15a0cd42637ec30b587`, and Tau Ceti is
`ff72a2e86930d5268476ee33d55ab054ed1c3ea5`. The collection used a separate
owned build directory with warm dependencies. Repository and dependency
checkouts were clean. Every candidate inventory contained only the three
standard axioms. Baselines declare nothing and print no inventory.

| Depth | Operation | Import-only median (s) | Proof median (s) | Median paired difference (s) | Proof peak RSS median (GiB) |
|---|---|---:|---:|---:|---:|
| 1 | Acceptance | 2.376 | 3.189 | 0.810 | 1.764 |
| 1 | Arithmetic rejection | 2.384 | 2.960 | 0.540 | 1.692 |
| 1 | Stale-context rejection | 2.373 | 2.681 | 0.304 | 1.641 |
| 2 | Acceptance | 2.375 | 9.471 | 7.108 | 2.937 |
| 2 | Arithmetic rejection | 2.386 | 5.463 | 3.079 | 2.190 |
| 3 | Acceptance | 2.438 | 112.991 | 110.477 | 17.490 |
| 3 | Arithmetic rejection | 2.387 | 52.161 | 49.544 | 8.449 |

Peak resident sets include imports and the rebuild process; they are not
allocated-byte counts or isolated theorem memory. The high depth-three peak
supports keeping that target outside routine CI. These finite observations
do not establish a bound for arbitrary nested fields or satisfy all Phase-4
gates. No rerun was used, and host activity was retained with every arm.

The recorded source predates the separate fraction probes, the depth-two/three
stale-context probes, and the additional proofs identifying the arithmetic
rejection cause. Those additions are not measured by this collection. Raw
records retain schema v1 and its original metadata. The archived v1 source
names the manual library as its primary target; the recorded stale-context
summary omits some fixed graph sizes. All measured modules and source hashes are present. The current
schema v2 identifies each pair's actual build target, gives consistent graph
sizes, and includes this report in source provenance.

- [Complete collection](data/sign-det-nested-kernel/6f332afb8/nested-kernel.json)
  and [incremental arm records](data/sign-det-nested-kernel/6f332afb8/nested-kernel.json.samples.jsonl).
- [Source archive and checksums](data/sign-det-nested-kernel/6f332afb8/archive.json)
  and [exact source patch](data/sign-det-nested-kernel/6f332afb8/committed-source.patch).
- [Collection log](data/sign-det-nested-kernel/6f332afb8/collection.log)
  and [table data](data/sign-det-nested-kernel/6f332afb8/summary.json).

The archive reconstructs the measured checkout from the retained main
ancestor `f53917bfc7f96a68491441222e7128ffee3bd916` and the exact patch.
All 212 source hashes were verified against that checkout before archiving.
The measurement commit need not remain in the merged branch's history.

## Rational-function compatibility

The existing rational-function certificate probes were remeasured at clean
source `2616e53b0bd7de1d52896d06b9a968f270d5c76d`, using their unchanged
six-round schedule and the shared retained-arm wrapper. All 72 completed arms
remain in the [collection](data/sign-det-nested-kernel/2616e53b0-rationalfn/rationalfn-compatibility.json)
and [sidecar](data/sign-det-nested-kernel/2616e53b0-rationalfn/rationalfn-compatibility.json.samples.jsonl),
with [source reconstruction](data/sign-det-nested-kernel/2616e53b0-rationalfn/archive.json).
The existing five-second fresh-module budgets passed. Replay and rejection
medians ranged from 0.756 to 0.858 seconds, with approximately 0.817 GiB
peak resident sets. This is a compatibility observation on this host, not a
controlled before/after comparison or evidence for general normalization cost.

## Scope

These probes do not construct a shared graph of coefficient-sign proofs across
field levels. They do not prove JSON byte roundtrips or apply the mathematical
root-count theorem to an ambient real closed model. Those are separate
obligations, as are the full Phase-4 gates and the required Tau Ceti Thom
foundations. See also the
[native nested-field conformance](sign-det-nested-fields.md) and
[semantic theorem application probes](sign-det-semantic-probes.md).
