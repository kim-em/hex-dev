# hex-berlekamp

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Certified finite-field polynomial factorization and irreducibility testing in
Lean 4, implemented without Mathlib.

The library provides Rabin irreducibility, distinct-degree factorization, the
Berlekamp Frobenius matrix and fixed-space kernel, split-step factorization,
and compact certificates suitable for elaborator-generated proof terms.

# Quickstart

```toml
[[require]]
name = "hex-berlekamp"
git = "https://github.com/leanprover/hex-berlekamp.git"
rev = "main"
```

```lean
import HexBerlekamp
open Hex
```

# Functionality

`factor_poly` and `irreducibility` run search in compiled elaborator code and
emit checked certificates. The public umbrella contains production APIs only;
the tactic regression modules are built by the package's dedicated test
target.

# Verification

Exact conformance against python-flint is a required release check. FLINT
timings are informational optimization evidence. The required performance
checks are the absolute Rabin
and distinct-degree budgets stated in the [SPEC](SPEC/hex-berlekamp.md).

For statements over Mathlib's `Polynomial (ZMod p)`, use
[`hex-berlekamp-mathlib`](https://github.com/leanprover/hex-berlekamp-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
