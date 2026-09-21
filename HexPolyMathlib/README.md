# hex-poly-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-poly`](https://github.com/leanprover/hex-poly).

It converts between `Hex.DensePoly R` and `Polynomial R`, proves that the
conversions form a ring equivalence, and transfers the executable Euclidean
operations to Mathlib's polynomial semantics.

# Quickstart

```toml
[[require]]
name = "hex-poly-mathlib"
git = "https://github.com/leanprover/hex-poly-mathlib.git"
rev = "main"
```

```lean
import HexPolyMathlib
```

# Functionality

The package exposes the dense-polynomial conversions, their inverse laws, and
the ring and Euclidean-operation correspondence used by downstream proofs.

`HexPolyMathlib.Interpret.interpret` also supports noncanonical executable
coefficients through an operation-preserving, zero-reflecting map into a
field. It preserves degree, arithmetic, derivatives and Horner evaluation;
both division outputs agree with Mathlib. The raw gcd is associated to
Mathlib's normalized gcd, and interpreted xgcd coefficients satisfy the
Bézout identity. `Interpret.sub_isZero` identifies zero-difference checks
with semantic polynomial equality without assuming an injective coefficient
map. `Interpret.monicize_leading` proves semantic monicity of the actual
monicization output for every nonzero input.

The pseudo-division correspondence preserves the recorded multiplier and
relates both outputs to scaled field division. It proves reconstruction,
strict remainder degree and positive sign correction. Plain `pseudoGcd` has
exactly the common divisors of its inputs in the semantic field, including
for integer and noncanonical source coefficients.

# Verification

Runtime-only clients should depend on `hex-poly`. This package is for theorem
statements and interoperability involving Mathlib. See the
[SPEC](SPEC/hex-poly-mathlib.md) for the conversion laws and theorem map.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
