# hex-arith

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Low-level exact arithmetic for Hex, implemented in Lean 4 without Mathlib.

The package provides wide `UInt64` operations, extended gcd, modular powers
and inverses, primality helpers, and Barrett and Montgomery reduction. Its
native wide-word implementation is part of the package build and is covered by
the same theorem-facing API as the portable arithmetic layer.

# Quickstart

```toml
[[require]]
name = "hex-arith"
git = "https://github.com/leanprover/hex-arith.git"
rev = "main"
```

```lean
import HexArith
```

# Functionality

The umbrella exposes the `Hex.Barrett` and `Hex.Montgomery` contexts,
`Hex.extGcd`, the `Nat` modular-arithmetic lemmas, and wide-word operations.
Reduction contexts make their modulus and range invariants explicit; hot-loop
clients can reuse a context rather than recomputing constants.

# Verification

See the [SPEC](SPEC/hex-arith.md) for contracts, edge cases, and performance
policy. Benchmarks and conformance targets run in
[`hex-dev`](https://github.com/kim-em/hex-dev).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
