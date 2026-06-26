import HexPolyZ.Basic
import HexPolyZ.Mignotte
import HexPolyZ.Conformance

/-!
The `HexPolyZ` library specializes the generic dense polynomial library to
integer coefficients, exposing the `ZPoly` alias together with congruence,
content, primitive-part, and conservative executable Mignotte-bound APIs used
by the factoring pipeline.
-/
