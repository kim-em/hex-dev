module

public import HexPolyFp.Basic
public import HexPolyFp.Packed
public import HexPolyFp.PrimeField
public import HexPolyFp.Compose
public import HexPolyFp.Enumeration
public import HexPolyFp.Frobenius
public import HexPolyFp.SquareFree
public import HexPolyFp.ModCompose
public import HexPolyFp.Quotient
public import HexPolyFp.QuotientFrobenius

public section

/-!
`HexPolyFp` specializes the executable dense-polynomial API to
`Hex.ZMod64 p`, exposing `FpPoly p` together with Frobenius-power
computations, square-free decomposition, and modular composition
modulo a monic polynomial.
-/
