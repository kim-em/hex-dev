# hex-hensel-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Correctness and uniqueness theorems for
[`hex-hensel`](https://github.com/leanprover/hex-hensel).

This Mathlib package relates the executable lifts to `Polynomial ℤ`, carries
coprimality through powers of the lifting modulus, and provides the proof
surface consumed by certified integer factorization.

# Quickstart

```toml
[[require]]
name = "hex-hensel-mathlib"
git = "https://github.com/leanprover/hex-hensel-mathlib.git"
rev = "main"
```

```lean
import HexHenselMathlib
```

# Functionality

The package exposes the polynomial lift invariant, correctness of each lifting
schedule, coprimality preservation, and uniqueness at the lifted modulus.

# Verification

Use `hex-hensel` alone for computation. See the
[SPEC](SPEC/hex-hensel-mathlib.md) for the executable-to-Mathlib correspondence
and the precise lifting hypotheses.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
