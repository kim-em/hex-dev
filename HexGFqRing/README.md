# hex-gfq-ring

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Canonical executable quotient rings `F_p[x] / (f)` for Lean 4, without
Mathlib.

Elements are reduced polynomial representatives modulo a fixed nonconstant
modulus. Construction and arithmetic preserve that canonical representation,
and the package supplies normalized addition, multiplication, powers, and ring
instances used by finite-field factorization.

# Quickstart

```toml
[[require]]
name = "hex-gfq-ring"
git = "https://github.com/leanprover/hex-gfq-ring.git"
rev = "main"
```

```lean
import HexGFqRing
open Hex
```

# Functionality

The public surface covers canonical reduction, normalized ring operations,
powers, and the quotient-ring instances used by the finite-field layer.

# Verification

This package promises quotient-ring operations; field-only operations belong
to the separate field layer and require irreducibility. See the
[SPEC](SPEC/hex-gfq-ring.md) for invariants and complexity expectations.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
