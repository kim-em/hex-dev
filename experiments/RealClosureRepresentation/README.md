# Real-closure representation prototype

Build and run from this directory:

```sh
lake build representationPrototype HexRationalFn.Field
.lake/build/bin/representationPrototype
```

The package uses the repository's pinned Lean toolchain and actual `HexPoly`
sources through `srcDir = "../.."`. It has no package dependencies and imports
no Mathlib. It is an interface experiment, not a released library or a
performance benchmark.

`Prototype.lean` represents `a+bX` at the selected root `1` of the reducible
polynomial `X²-1`. All computed zeros share one representation; nonzero
representations need not be canonical. In particular `X` and `1` differ
structurally, while their difference is stored as zero. Ordinary operation
instances reuse `DensePoly` normalization, division, gcd and extended gcd
without a `Field` instance. It also exercises operation-only powers and
leading-coefficient normalization, including a semantically monic result whose
leading coefficient is not structurally `1`. Kernel-checked examples repeat the construction
over this noncanonical predecessor. The generic `remainder_degree` theorem
uses the existing polynomial cancellation theorem and proved interpretation
of the example operations. This example is rational-valued; it does not
implement general algebraic root selection or dynamic splitting.

`Search.lean` proves that a single successful finite trial establishes
accessibility for an unbounded first-success search starting earlier. The
runtime loop receives only an erased accessibility proof. Its example uses
rational Liouville partial-sum bounds for `X²-8/5`, separating at precision
three. It computes through earlier inconclusive trials; it does not return a
precomputed answer. The real containment/transcendence proof is separate,
and this per-input witness does not provide a universal constant registration.

All proposition checks use the ordinary kernel. There are no added axioms,
`sorry`, `native_decide`, partial definitions or unsafe casts in the experiment.
Printed axiom dependencies are only the standard Lean axioms. The source
`HexPoly` modules retain their existing proved compiler replacements.

Expected output:

```text
finite-witness total sign: 1
structurally equal roots: false
zero difference: true
normalized size: 1
division remainder zero: true
gcd degree: 1
xgcd degree: 1
```

The [family execution contract](../../SPEC/real-closure-execution.md) records
the remaining interpretation, recursion and performance obligations. This
experiment does not establish the cost of canonical-zero normalization in
deep towers, and makes no Phase-4 claim.

This workspace reuses the root package artifacts and dependency checkouts.
Before invoking Lake, run `python3 experiments/RealClosureAlgebraic/audit.py
--live` from the repository root. If it reports a stale local manifest after
a root dependency change, refresh that manifest with
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d experiments/RealClosureRepresentation update Hex`.
