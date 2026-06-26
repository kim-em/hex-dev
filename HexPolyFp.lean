import HexPolyFp.Basic
import HexPolyFp.Packed
import HexPolyFp.PrimeField
import HexPolyFp.Compose
import HexPolyFp.Enumeration
import HexPolyFp.Frobenius
import HexPolyFp.SquareFree
import HexPolyFp.ModCompose
import HexPolyFp.Quotient
import HexPolyFp.QuotientFrobenius
import HexPolyFp.Conformance

/-!
`HexPolyFp` specializes the executable dense-polynomial API to
`Hex.ZMod64 p`, exposing `FpPoly p` together with Frobenius-power
computations, square-free decomposition, and modular composition
modulo a monic polynomial.
-/
