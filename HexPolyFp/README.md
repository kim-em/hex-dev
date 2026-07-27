# hex-poly-fp

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Executable dense polynomials over `Hex.ZMod64 p`, implemented without Mathlib.

`Hex.FpPoly p` extends the normalized `Hex.DensePoly` surface with finite-field
division, Frobenius powers, square-free decomposition, modular composition,
quotient rings, and packed multiplication. These are the computational
foundations for Berlekamp factorization and Hensel lifting.

# Quickstart

```toml
[[require]]
name = "hex-poly-fp"
git = "https://github.com/leanprover/hex-poly-fp.git"
rev = "main"
```

```lean
import HexPolyFp
open Hex
```

# Functionality

Prime-field operations carry the required primality and word-size hypotheses
in their types. The packed multiplier is an optimization; normalization and
field-polynomial semantics remain the public contract.

# Verification

See the [SPEC](SPEC/hex-poly-fp.md) for supported modulus bounds, algorithms,
conformance fixtures, and benchmark families.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
