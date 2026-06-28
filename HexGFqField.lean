import HexGFqField.Basic
import HexGFqField.Operations

/-!
Thin finite-field wrapper for executable `F_p[x] / (f)`.

`HexGFqField` reuses the quotient-ring representation from `HexGFqRing`
unchanged: `GFqField.FiniteField` is just a wrapper around reduced residues,
with explicit conversions, quotient-backed arithmetic, exponentiation, and the
Frobenius map `a ↦ a ^ p`.
-/
