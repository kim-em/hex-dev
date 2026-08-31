# hex-poly-z-gcd-mathlib

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexPolyZGcd`
Computational performance owner: `HexPolyZGcd`

## Purpose

This library transports the verified executable integer-polynomial gcd API
from `hex-poly-z-gcd` across `HexPolyZMathlib.equiv` to Mathlib's
`Polynomial ℤ`. It contains proof-facing correspondence results and no gcd
implementation of its own.

## API

For `f h d g : Hex.ZPoly`:

```lean
theorem gcd_dvd_left (f h) : e (gcd f h) ∣ e f
theorem gcd_dvd_right (f h) : e (gcd f h) ∣ e h

theorem dvd_gcd (d f h) :
    e d ∣ e f → e d ∣ e h → e d ∣ e (gcd f h)

theorem coprimeCofactors_greatest
    (hc : CoprimeCofactors f h g) (d) :
    e d ∣ e f → e d ∣ e h → e d ∣ e g

theorem divExact?_eq_dvd (f g) :
    (divExact? f g).isSome = true ↔ g ≠ 0 ∧ e g ∣ e f
```

The nonzero condition in the final statement is necessary: executable exact
division rejects a zero divisor, while Mathlib divisibility admits `0 ∣ 0`.

## Proof boundary

The computational package proves exact cofactor identities, cofactor
coprimality, normalization, and maximality without importing Mathlib. This
companion uses the existing dense-polynomial ring equivalence and its
divisibility correspondence to restate those results over `Polynomial ℤ`.
