# hex-poly-z

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Dense integer polynomials for Lean 4, implemented without Mathlib.

`Hex.ZPoly` is the integer specialization of `Hex.DensePoly`. The package
provides content and primitive-part decomposition, rational normalization,
coefficientwise congruence, square-free decomposition support, and executable
Mignotte bounds used by the factorization and root-isolation stacks.

# Quickstart

```toml
[[require]]
name = "hex-poly-z"
git = "https://github.com/leanprover/hex-poly-z.git"
rev = "main"
```

```lean
import HexPolyZ
open Hex
```

# Functionality

The executable API covers content, primitive parts, rational normalization,
coefficient congruence, decomposition helpers, and conservative factor bounds.

# Verification

The zero polynomial, constants, signs, and content have explicit normalization
conventions documented in the [SPEC](SPEC/hex-poly-z.md). For equivalence with
`Polynomial ℤ` and the theorem-level bounds, use
[`hex-poly-z-mathlib`](https://github.com/leanprover/hex-poly-z-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
