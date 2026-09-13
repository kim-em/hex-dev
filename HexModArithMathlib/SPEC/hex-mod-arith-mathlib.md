# hex-mod-arith-mathlib (depends on hex-mod-arith + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`; its conversion helpers only
state the representation correspondence and introduce no independent arithmetic.

Computational conformance owner: `HexModArith`
Computational performance owner: `HexModArith`

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.

`HexModArithMathlib.Ring` transports Mathlib's `CommRing` laws along this
equivalence while retaining the executable operations, including powers,
casts, and scalar multiplication. The instance is scoped to
`HexModArithMathlib.ZMod64`: imports alone preserve the existing local
structure-selection discipline of downstream bridges. It requires only
`ZMod64.Bounds p`, so it also covers composite moduli and modulus one.
