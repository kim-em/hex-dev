module

public import HexModArith.Basic
public import HexModArith.HotLoop
public import HexModArith.Prime
public import HexModArith.Ring

public section

/-!
The `HexModArith` library provides `UInt64`-backed modular arithmetic,
starting from the reduced `ZMod64` core, its bounds typeclass, the basic
additive API, executable inversion and exponentiation helpers, the ring-facing
`Lean.Grind` surface, the prime-modulus theorem layer, the default modular
multiplication surface, and the opt-in Barrett/Montgomery hot-loop wrappers.
-/
