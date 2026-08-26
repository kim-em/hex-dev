# hex-truncated-series-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-truncated-series-mathlib` is the Mathlib correspondence layer for
[`hex-truncated-series`](https://github.com/leanprover/hex-truncated-series).
It identifies fixed-precision series with `PowerSeries R` modulo `X ^ n` and
transports the executable operations. It depends on Mathlib and
`hex-truncated-series`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-truncated-series-mathlib"
git = "https://github.com/leanprover/hex-truncated-series-mathlib.git"
rev = "main"
```

```lean
import HexTruncatedSeriesMathlib

open Hex HexTruncatedSeriesMathlib

#check (quotEquiv (R := Rat) (n := 6))

example (f : PowerSeries Rat) :
    ofPowerSeries (n := 6) (f ^ 2) =
      Hex.TSeries.pow (ofPowerSeries f) 2 :=
  ofPowerSeries_pow f 2
```

# Functionality

- A Mathlib `CommRing (TSeries R n)` instance pinned to the executable
  operations from `hex-truncated-series`.
- Coefficient truncation `ofPowerSeries`, the ring homomorphism
  `ofPowerSeriesHom`, its surjectivity and kernel, and the quotient ring
  equivalence `quotEquiv`.
- Correspondence for constants, `X`, powers, truncation, multiplication by a
  power of `X`, and differentiation.
- Transfer theorems for inverse, substitution, compositional inverse,
  exponential, and logarithm, plus power-series square-root existence and
  uniqueness above a supplied constant root.
- A low-priority `NatInverses` instance for rational algebras.

# Verification

The headline equivalence identifies fixed-precision series exactly with the
quotient by the discarded tail:

```lean
noncomputable def quotEquiv [CommRing R] :
    (PowerSeries R ⧸
      Ideal.span {(PowerSeries.X : PowerSeries R) ^ n}) ≃+*
        TSeries R n
```

Its action on representatives and every listed operation correspondence are
proved. There is no executable algorithm in this companion; those operations
and their Mathlib-free correctness proofs live in
[`hex-truncated-series`](https://github.com/leanprover/hex-truncated-series).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this
published mirror. Contributions are welcome as pull requests to the
`SPEC/` directory there: describe the behaviour you want and leave the
implementation to the maintainer.
