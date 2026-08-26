# hex-poly

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Normalized dense univariate polynomials for Lean 4, with no Mathlib dependency.

`Hex.DensePoly R` stores coefficients in ascending order and maintains the
canonical invariant that trailing zeroes are removed. The library supplies
constructors, arithmetic, evaluation, division, gcd-related operations,
content, and Chinese-remainder helpers used throughout Hex.

# Quickstart

```toml
[[require]]
name = "hex-poly"
git = "https://github.com/leanprover/hex-poly.git"
rev = "main"
```

```lean
import HexPoly
open Hex
```

# Functionality

All public operations return normalized polynomials. Algorithms may use mutable
arrays internally, but the public representation and its equality are
canonical. For interoperability with Mathlib's `Polynomial`, use
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

# Verification

See the [SPEC](SPEC/hex-poly.md) for representation invariants, executable
contracts, complexity expectations, and test strategy.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
