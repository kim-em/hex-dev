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

# Verification

Runtime-only clients should depend on `hex-poly`. This package is for theorem
statements and interoperability involving Mathlib. See the
[SPEC](SPEC/hex-poly-mathlib.md) for the conversion laws and theorem map.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
