# hex-mod-arith-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-mod-arith`](https://github.com/leanprover/hex-mod-arith).

The package converts `Hex.ZMod64 p` residues to `ZMod p`, proves a ring
equivalence, and transfers the executable word-modular operations to the
standard Mathlib semantics.

# Quickstart

```toml
[[require]]
name = "hex-mod-arith-mathlib"
git = "https://github.com/leanprover/hex-mod-arith-mathlib.git"
rev = "main"
```

```lean
import HexModArithMathlib
```

# Functionality

The bridge exposes conversion in both directions, the ring equivalence, and
compatibility lemmas for the word-modular operations.

# Verification

Use the computational package directly when Mathlib semantics are unnecessary.
See the [SPEC](SPEC/hex-mod-arith-mathlib.md) for conversion and compatibility
theorems.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
