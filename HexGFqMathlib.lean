module

public import HexGFqMathlib.Basic
public import HexGFqMathlib.GF2q

public section

/-!
Mathlib-side correspondence lemmas for the canonical finite-field convenience
constructors.

The executable `HexGFq` layer keeps `GFq` and optimized `GF2q` separate so the
representation choice stays explicit.  This module packages the existing
`HexGF2Mathlib` packed-to-generic ring equivalence as the SPEC-facing
equivalence between the optimized binary Conway field and the generic Conway
field.
-/
