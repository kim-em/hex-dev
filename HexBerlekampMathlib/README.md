# hex-berlekamp-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib correspondence and proof-facing tactics for
[`hex-berlekamp`](https://github.com/leanprover/hex-berlekamp).

The package relates `Hex.FpPoly p` to `Polynomial (ZMod p)`, proves the
soundness of executable Rabin and factorization certificates, and supplies
factorization tactics for Mathlib polynomials.

# Quickstart

```toml
[[require]]
name = "hex-berlekamp-mathlib"
git = "https://github.com/leanprover/hex-berlekamp-mathlib.git"
rev = "main"
```

```lean
import HexBerlekampMathlib
```

# Functionality

The package provides finite-field polynomial conversion, Rabin-certificate
soundness, factorization transport, and the Mathlib `factor_poly` extension.

# Verification

The public umbrella excludes regression tests; those are compiled by the
release test target. The computational algorithms stay in the Mathlib-free
package. See the [SPEC](SPEC/hex-berlekamp-mathlib.md) for the correspondence
theorems and trust boundary.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
