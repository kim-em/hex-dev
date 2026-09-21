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
arrays internally. Trailing stored zeros are removed; nonzero coefficients
need not have canonical representatives. For interoperability with Mathlib's
`Polynomial`, use
[`hex-poly-mathlib`](https://github.com/leanprover/hex-poly-mathlib).

`Hex.DensePoly.Interpret.map` transports polynomials through a zero-reflecting
coefficient map. Its lemmas cover arithmetic, derivative, Horner evaluation,
division, gcd, extended gcd, powers and monicization without ring or field
instances on the source. Scalar operation preservation is an explicit
hypothesis. Structural equality remains distinct from equality after
interpretation. Semantic monicization does not supply the literal
`leadingCoeff = 1` witness required by `divModMonic` and `modByMonic`;
use general division unless that structural witness is available.

`pseudoDivMod` is the shared fraction-free division kernel. `pseudoDiv` records
its multiplier, and `positivePseudoDiv` corrects a negative multiplier together
with both outputs. `pseudoGcd` follows the plain remainder sequence with a
proved decrease in stored degree. It computes a gcd over the fraction field
up to a nonzero scalar; integer coefficients keep their ordinary domain
operations.

# Verification

See the [SPEC](SPEC/hex-poly.md) for representation invariants, executable
contracts, complexity expectations, and test strategy.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
