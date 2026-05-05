import HexGF2.Basic
import HexGF2.Clmul
import HexGF2.Conformance
import HexGF2.CrossCheck
import HexGF2.Euclid
import HexGF2.Field
import HexGF2.Multiply
import HexGF2.Smoke

/-!
The `HexGF2` library exposes the packed `GF(2)` polynomial core:
normalized `GF2Poly` words, bit/degree accessors, XOR addition, shifts by
powers of `x`, carry-less-multiply-backed polynomial multiplication, and the
derived division, gcd, and extended-gcd APIs together with both the single-word
and arbitrary-degree packed `GF(2^n)` wrapper surfaces.
-/
