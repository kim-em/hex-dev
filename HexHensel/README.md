# hex-hensel

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable Hensel lifting for dense integer polynomials, implemented in Lean 4
without Mathlib.

The library supports linear and quadratic two-factor lifting and ordered
multifactor lifting from modulus `p` to powers of `p`. Conversion between
`Hex.ZPoly` and `Hex.FpPoly p` is part of the public surface used by integer
factorization.

# Quickstart

```toml
[[require]]
name = "hex-hensel"
git = "https://github.com/leanprover/hex-hensel.git"
rev = "main"
```

```lean
import HexHensel
open Hex
```

# Functionality

Preconditions such as modular factor products and Bezout data are explicit;
failed executable checks are represented rather than assumed. The
[`hex-hensel-mathlib`](https://github.com/leanprover/hex-hensel-mathlib)
bridge supplies polynomial correctness and uniqueness theorems.

# Verification

See the [SPEC](SPEC/hex-hensel.md) for contracts, lifting schedules, and
benchmark/conformance coverage.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
