# hex-poly-z-gcd-theory

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-poly-z-gcd-theory` transports the verified gcd API from
[`hex-poly-z-gcd`](https://github.com/leanprover/hex-poly-z-gcd) to Mathlib's
`Polynomial ℤ`. It depends on `hex-poly-z-gcd`, `hex-poly-z-theory`, and
`hex-poly-theory`; executable computation remains in the Mathlib-free
package.

# Quickstart

```toml
[[require]]
name = "hex-poly-z-gcd-theory"
git = "https://github.com/leanprover/hex-poly-z-gcd-theory.git"
rev = "main"
```

```lean
import HexPolyZGcdTheory

open Hex

example (f h : ZPoly) :
    HexPolyZTheory.equiv (ZPoly.gcd f h) ∣
      HexPolyZTheory.equiv f :=
  HexPolyZGcdTheory.gcd_dvd_left f h
```

# Functionality

- Left and right divisibility of the transported checked gcd.
- The greatest-common-divisor universal property in `Polynomial ℤ`.
- Transported greatestness for an arbitrary accepted
  `ZPoly.CoprimeCofactors` witness.
- Exact-division success characterized by nonzero polynomial divisibility.

# Verification

This package contains correspondence proofs and no new executable gcd
algorithm. Its theorems transport the Mathlib-free certificate and maximality
results through `HexPolyZTheory.equiv`.

```lean
theorem divExact?_eq_dvd (f g : ZPoly) :
    (ZPoly.divExact? f g).isSome = true ↔
      g ≠ 0 ∧ HexPolyZTheory.equiv g ∣ HexPolyZTheory.equiv f
```

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want and leave
the implementation to the maintainer.
