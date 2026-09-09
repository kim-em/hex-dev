# hex-real-algebraic

Executable real algebraic numbers with exact comparison, developed in the
[Hex monorepo](https://github.com/kim-em/hex-dev). The implementation is
Mathlib-free and reuses canonical `AlgebraicNumber` arithmetic and isolations.
It has not yet been published as a split repository.

```lean
import HexRealAlgebraic

open Hex
open Hex.RealAlgebraicNumber (ofRat ofAlgebraic? sqrt?)

#guard sqrt? (ofRat (9 / 4)) == some (ofRat (3 / 2))
#guard (ofRat (-3 / 2)).floor == -2
#guard (ZPoly.realAlgebraicRoots #p[-2, 0, 1]).size == 2
#guard (ofAlgebraic? AlgebraicNumber.I).isNone
```

`RealAlgebraicNumber` is the subtype of canonical algebraic numbers whose
stored `isReal` test succeeds. Use `ofAlgebraic?` or `ofRoot?` for checked
construction; nonreal input returns `none`. `ofAlgebraic a h` packages a
value with an existing reality proof. Arithmetic retains canonical structural
equality and checks closure once at the stored precision.

The API includes arithmetic, casts, natural and integer powers, scalar
multiplication, exact `compare`, decidable `<` and `≤`, `min`, `max`, `sign`,
`abs`, `conj`, `toRat?`, `floor`, `ceil`, and dyadic `approx`. `sqrt?` returns
the nonnegative square root or `none` for negative input; `sqrt a h` takes a
proof of nonnegativity. `Repr` emits an ordinary checked Lean expression that
reconstructs the value.

`RealAlgebraicPoly.ofArray` normalizes real coefficient arrays.
`RealAlgebraicPoly.roots` returns `.all` for zero and `.finite` otherwise,
with distinct increasing roots and positive multiplicities. Inspect `finite?`
when the zero polynomial matters: `toArray` intentionally returns an empty
array for `.all`. `ZPoly.realAlgebraicRoots` returns distinct increasing real
roots and uses the integer API's empty-array convention for every constant.

Core order-law classes and `Lean.Grind.Field` / `Lean.Grind.OrderedRing` are
conditional on the proof-only `RealAlgebraicNumber.Laws`. The
[Mathlib companion](../HexRealAlgebraicMathlib/README.md) proves this package
and provides the ordinary Mathlib field and linear-order structures. None of
its proofs enters the computational dependency graph.

See the [joint specification](../SPEC/Libraries/hex-real-algebraic.md) for
contracts, approximation bounds, and comparison semantics. Comparison always
agrees with `AlgebraicNumber.realCompare`; its cost includes exact refinement
at the separation precision of the product of the minimal polynomials.

## Verification

```sh
lake build HexRealAlgebraic.Conformance HexRealAlgebraic.ReprChecks hexrealalgebraic_conformance
.lake/build/bin/hexrealalgebraic_conformance
lake build hexrealalgebraic_emit_fixtures
.lake/build/bin/hexrealalgebraic_emit_fixtures > /tmp/real-algebraic.jsonl
python3 scripts/oracle/real_algebraic_flint.py /tmp/real-algebraic.jsonl --require-oracles
```

The core checks run without external oracles. The CI oracle uses pinned
python-flint 0.9.0 / FLINT 3.6.0: exact `qqbar` comparisons and arithmetic,
certified integer-root balls, and a test-only binding for general
algebraic-coefficient roots. Inputs and answers carry integer polynomials and
certified dyadic discs. Missing optional components produce explicit skips;
`HEX_REQUIRE_ORACLES=1` makes them required in CI. Wrong answers and
inconclusive root matching always fail.

For the required local profile, add `--local` to the emitter and `--profile
local` to the oracle command. It adds a degree-twelve root product and
reproducible randomized construction paths. The emitter's `--repr` mode
regenerates the Lean expressions in
[ReprChecks.lean](../conformance/HexRealAlgebraic/ReprChecks.lean), which CI
compiles and compares against fresh output.
