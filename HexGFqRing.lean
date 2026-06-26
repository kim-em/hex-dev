module

public import HexGFqRing.Basic
public import HexGFqRing.Operations

public section

/-!
Canonical quotient-ring API for executable `F_p[x] / (f)`.

The current surface provides quotient elements as reduced polynomial
representatives modulo a fixed nonconstant modulus together with normalized
ring operations, exponentiation, and the quotient-side algebra-instance surface.
-/
