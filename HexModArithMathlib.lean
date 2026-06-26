module

public import HexModArithMathlib.Basic

public section

/-!
The `HexModArithMathlib` library identifies executable `Hex.ZMod64` residues
with Mathlib's `ZMod` API.

It exposes the concrete conversion functions and the ring equivalence between
`ZMod64 p` and `ZMod p`, providing the proof-facing entry point for downstream
finite-field and polynomial correspondences.
-/
