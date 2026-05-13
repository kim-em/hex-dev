import HexModArithMathlib.Basic

/-!
The `HexModArithMathlib` library bridges executable `Hex.ZMod64` residues to
Mathlib's `ZMod` API.

It exposes the concrete conversion functions and the ring equivalence between
`ZMod64 p` and `ZMod p`, providing the proof-facing entry point for downstream
finite-field and polynomial bridges.
-/
