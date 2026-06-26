module

public import HexPolyZ.Basic
public import HexPolyZ.Mignotte

public section

/-!
The `HexPolyZ` library specializes the generic dense polynomial library to
integer coefficients, exposing the `ZPoly` alias together with congruence,
content, primitive-part, and conservative executable Mignotte-bound APIs used
by the factoring pipeline.
-/
