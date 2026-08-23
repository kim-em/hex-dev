# hex-real-roots-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib semantics and a one-call elaborator for
[`hex-real-roots`](https://github.com/leanprover/hex-real-roots).

This package proves the half-open form of Sturm's theorem, connects the
executable signed-remainder chain to `Polynomial ℝ`, proves soundness and
completeness of the isolator, transports through squarefree cores, and presents
the result as ordinary rational intervals with proof fields.

# Quickstart

```toml
[[require]]
name = "hex-real-roots-mathlib"
git = "https://github.com/leanprover/hex-real-roots-mathlib.git"
rev = "main"
```

```lean
import HexRealRootsMathlib
```

# Functionality

```lean
import HexRealRootsMathlib

open Hex Polynomial

noncomputable def roots :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℤ)

example : roots.intervals =
    #v[((0 : ℚ), (2 : ℚ)), ((2 : ℚ), (4 : ℚ))] := rfl
```

The input may be a closed `Hex.ZPoly` or a closed integer-coefficient
`Polynomial ℤ`, `Polynomial ℚ`, or `Polynomial ℝ` expression. Repeated roots
are handled automatically by isolating the squarefree core and transporting
the result back. The zero polynomial is rejected because it has infinitely many
real roots.

An optional exact width refines every interval:

```lean
import HexRealRootsMathlib

open Hex Polynomial

noncomputable def tight :=
  isolate_roots (width := 2 ^ (-20 : ℤ))
    (X ^ 4 - 2 : Polynomial ℝ)
```

The result is `Hex.IsolatedRealRoots P n`, whose fields state:

- `unique_root`: interval `i` contains exactly one real root;
- `covers`: every real root lies in one returned interval; and
- `ordered`: intervals are sorted and pairwise disjoint.

The interval vector is literal data, so endpoint extraction is often `rfl` and
the semantic fields can be consumed directly by `simp`, `grind`, or ordinary
proof terms.

# Verification

The elaborator runs compiled search, reifies the Sturm chain and intervals, and
emits a small proof term whose count checks reduce in the kernel. It does not
ask the kernel to repeat bisection. Descartes search is never trusted: every
output interval and the final root total are certified by Sturm counts.

See the [SPEC](SPEC/hex-real-roots-mathlib.md) and the Hex manual's real-roots
chapter for the theorem chain and checked examples.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
