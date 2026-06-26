module

public import HexGF2Mathlib.Basic
public import HexGF2Mathlib.Field

public section

/-!
The `HexGF2Mathlib` library connects the packed `HexGF2` execution path to the
generic proof-facing polynomial and finite-field constructions.

It exposes the packed-polynomial equivalence `Hex.GF2Poly ≃+* Hex.FpPoly 2`
together with the corresponding single-word/arbitrary-degree `GF(2^n)`
correspondence modules.
-/
