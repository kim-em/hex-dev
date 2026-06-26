import HexBerlekampMathlib.Basic

/-!
The `HexBerlekampMathlib` library contains the Mathlib-facing correctness
surface for executable Berlekamp factorization and Rabin irreducibility tests.

It exposes the transfer from `FpPoly p` to `Polynomial (ZMod p)`, the first
irreducibility theorem statements, and the decidability surface needed by
downstream proof layers.
-/
