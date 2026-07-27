# hex-mod-arith

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Fast `UInt64`-backed modular arithmetic for Lean 4, independent of Mathlib.

The central type is `Hex.ZMod64 p`. Its public constructors and operations
preserve reduced representatives, while bounds typeclasses make the arithmetic
preconditions available to both the implementation and proofs. Default,
Barrett, and Montgomery multiplication surfaces support different workload
shapes without changing residue semantics.

# Quickstart

```toml
[[require]]
name = "hex-mod-arith"
git = "https://github.com/leanprover/hex-mod-arith.git"
rev = "main"
```

```lean
import HexModArith
open Hex
```

# Functionality

The package includes executable inversion, powers, prime-modulus results, ring
instances, and hot-loop wrappers. It also ships native modular-arithmetic code;
ordinary Lake builds link it automatically.

# Verification

For the equivalence with Mathlib's `ZMod`, use
[`hex-mod-arith-mathlib`](https://github.com/leanprover/hex-mod-arith-mathlib).
See the [SPEC](SPEC/hex-mod-arith.md) for modulus restrictions and performance
budgets.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
