import HexGF2Mathlib.Basic
import HexGF2Mathlib.Field

/-!
The `HexGF2Mathlib` library bridges the packed `HexGF2` execution path to the
generic proof-facing polynomial and finite-field constructions.

It exposes the packed-polynomial bridge `Hex.GF2Poly ≃+* Hex.FpPoly 2`
together with the corresponding single-word/arbitrary-degree `GF(2^n)` bridge
modules.
-/
