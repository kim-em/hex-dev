# hex-mod-arith-theory (depends on hex-mod-arith + Mathlib)

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.

`HexModArithTheory.Ring` transports Mathlib's `CommRing` laws along this
equivalence while retaining the executable operations, including powers,
casts, and scalar multiplication. The instance is scoped to
`HexModArithTheory.ZMod64`: imports alone preserve the existing local
structure-selection discipline of downstream bridges. It requires only
`ZMod64.Bounds p`, so it also covers composite moduli and modulus one.
