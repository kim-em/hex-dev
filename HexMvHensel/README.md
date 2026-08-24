# hex-mv-hensel

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-mv-hensel` implements checked multivariate Hensel lifting over the
integers. It translates an evaluation point to the origin, solves the
univariate partial-fraction equation, introduces the remaining variables one
at a time, and independently checks the reconstructed factor tuple.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-mv-hensel"
git = "https://github.com/leanprover/hex-mv-hensel.git"
rev = "main"
```

```lean
import HexMvHensel

open Hex Hex.MvHensel Hex.MvPoly

-- Build `Input` from a target, its univariate images, prescribed leading
-- coefficients, and a partial-fraction witness, then run:
-- #eval lift input
-- #eval liftWith Config.default input
```

# Functionality

- Coordinate translation with `shift`, `unshift`, `imageAt`, and `lcIn`.
- Arbitrary-precision symmetric modular arithmetic for multivariate terms.
- Production and prime-power lifting of univariate partial fractions.
- Recursive multivariate diophantine correction inside a degree box.
- Leading-coefficient seeding and stagewise extended EEZ lifting.
- Bounded retry through `liftWith`, with explicit structured failures.
- Independent certificate replay through `check`.

# Verification

`valid` checks the six input conditions before lifting. A successful result
always passes the independent checker; `check_sound` turns that Boolean
replay into exact product, image, and leading-coefficient statements.
Conditional completeness uses an executable shifted Kronecker coefficient
bound and uniqueness of compatible lift tuples.

```lean
theorem lift_checks {inp : Input n cmp cmp'} {cert : Cert n cmp}
    (h : lift inp = .ok cert) : check inp cert = true
```

The computational library is Mathlib-free. Algebraic correspondence and
UFD-facing consequences belong in its Mathlib bridge package.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
