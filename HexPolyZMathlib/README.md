# hex-poly-z-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib semantics and analytic bounds for
[`hex-poly-z`](https://github.com/leanprover/hex-poly-z).

The package identifies `Hex.ZPoly` with `Polynomial ℤ` and develops the
square-free, discriminant, Hadamard, Mahler-separation, Mignotte, and parsing
results shared by integer factorization and certified root isolation.

# Quickstart

```toml
[[require]]
name = "hex-poly-z-mathlib"
git = "https://github.com/leanprover/hex-poly-z-mathlib.git"
rev = "main"
```

```lean
import HexPolyZMathlib
```

# Functionality

The proof-facing API includes the `ZPoly` equivalence, square-free transport,
polynomial parsing, and the discriminant, Hadamard, Mahler, and Mignotte bounds.

# Verification

The computational representation remains in the Mathlib-free package. This
package owns theorem statements over `Polynomial ℤ`, `Polynomial ℚ`, and
`Polynomial ℂ`. See the [SPEC](SPEC/hex-poly-z-mathlib.md) for the theorem map.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
