# hex-truncated-series

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-truncated-series` provides fixed-precision power series, arithmetic,
precision changes, Newton operations, composition, and reversion. It depends
on [`hex-basic`](https://github.com/leanprover/hex-basic). See
[`hex-truncated-series-mathlib`](https://github.com/leanprover/hex-truncated-series-mathlib)
for the correspondence with Mathlib's `PowerSeries`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-truncated-series"
git = "https://github.com/leanprover/hex-truncated-series.git"
rev = "main"
```

```lean
import HexTruncatedSeries

open Hex Hex.TSeries

def geometric : TSeries Int 6 :=
  ofFn fun _ => 1

#guard (geometric * (1 - X)).coeff 0 == 1
#guard (geometric * (1 - X)).coeff 4 == 0

def reversible : TSeries Rat 6 := X - X ^ 2

#guard comp reversible (revOfUnit reversible 1) == X
#guard revLagrange reversible 1 == revOfUnit reversible 1
```

# Functionality

- Fixed-length `TSeries R n` values with total coefficient access,
  coefficient extensionality, constants, `X`, arithmetic, and powers.
- Precision changes with `truncate` and `extend`; coefficient shifts with
  `mulXPow` and exact `divXPow?`; represented valuation with `valuation?`.
- Formal derivative and integral with an explicit, precision-indexed
  `NatInverses` capability.
- Witness-taking and optional forms of inverse and square root, plus formal
  `exp` and `log`, all using bounded Newton iteration.
- Brent--Kung composition and Newton reversion, with direct Horner and
  Lagrange implementations as verified reference routes.

# Verification

The representation has a proved lightweight commutative-ring structure.
Every precision-changing operation has coefficient laws, each Newton
operation satisfies its defining equation and uniqueness contract, and the
bounded implementations agree with their full forms. The two independent
reversion routes agree under their shared hypotheses:

```lean
theorem revLagrange_eq [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    revLagrange b v = revOfUnit b v
```

The quotient interpretation and correspondence with Mathlib power series
live in
[`hex-truncated-series-mathlib`](https://github.com/leanprover/hex-truncated-series-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this
published mirror. Contributions are welcome as pull requests to the
`SPEC/` directory there: describe the behaviour you want and leave the
implementation to the maintainer.
