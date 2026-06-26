module

public import HexGF2.Basic
public import HexGF2.Clmul
public import HexGF2.CommonIrreducibility
public import HexGF2.Euclid
public import HexGF2.Field
public import HexGF2.Irreducibility
public import HexGF2.Multiply
public import HexGF2.RabinSoundness

public section

/-!
The `HexGF2` library exposes the packed `GF(2)` polynomial core:
normalized `GF2Poly` words, bit/degree accessors, XOR addition, shifts by
powers of `x`, carry-less-multiply-backed polynomial multiplication, and the
derived division, gcd, and extended-gcd APIs together with both the single-word
and arbitrary-degree packed `GF(2^n)` wrapper surfaces.
-/
