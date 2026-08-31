# hex-mod-arith-mathlib (depends on hex-mod-arith + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`; its conversion helpers only
state the representation correspondence and introduce no independent arithmetic.

Computational conformance owner: `HexModArith`
Computational performance owner: `HexModArith`

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.
