import HexConway.Basic

/-!
Core conformance checks for the Tier 1 committed Conway-polynomial lookup
surface in `HexConway`.

Oracle: committed Lübeck cache plus optional `conway-polynomials`
Mode: always
Covered operations:
- `luebeckConwayPolynomial?`
- `SupportedEntry`
- `conwayPoly`
Covered properties:
- the committed `(2, 1)`, `(2, 4)`, and `(3, 1)` lookups agree exactly
  with their packaged `SupportedEntry`
- `conwayPoly` returns the polynomial packaged by its `SupportedEntry`
- each supported Conway polynomial has positive degree
Covered edge cases:
- committed entries for `p ∈ {2, 3, 5, 7, 11, 13}` and `n ∈ {1..6}`
- unsupported degree zero, unsupported larger binary degree, and an
  unsupported prime outside the committed slice
- a binary higher-degree `SupportedEntry` (`(2, 4)`) and an odd-prime
  `SupportedEntry` slice (`(3, 1)`, `(3, 2)`, `(3, 3)`)
-/

namespace Hex
namespace Conway
namespace ConwayConformance

private instance boundsSeventeen : ZMod64.Bounds 17 := ⟨by decide, by decide⟩

private def coeffNats {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def coeffs? (p n : Nat) [ZMod64.Bounds p] : Option (List Nat) :=
  (luebeckConwayPolynomial? p n).map coeffNats

#guard coeffs? 2 1 = some [1, 1]
#guard coeffs? 2 2 = some [1, 1, 1]
#guard coeffs? 2 3 = some [1, 1, 0, 1]
#guard coeffs? 2 4 = some [1, 1, 0, 0, 1]
#guard coeffs? 2 5 = some [1, 0, 1, 0, 0, 1]
#guard coeffs? 2 6 = some [1, 1, 0, 1, 1, 0, 1]

#guard coeffs? 3 1 = some [1, 1]
#guard coeffs? 3 2 = some [2, 2, 1]
#guard coeffs? 3 3 = some [1, 2, 0, 1]
#guard coeffs? 3 4 = some [2, 0, 0, 2, 1]
#guard coeffs? 3 5 = some [1, 2, 0, 0, 0, 1]
#guard coeffs? 3 6 = some [2, 2, 1, 0, 2, 0, 1]

#guard coeffs? 5 1 = some [3, 1]
#guard coeffs? 5 2 = some [2, 4, 1]
#guard coeffs? 5 3 = some [3, 3, 0, 1]
#guard coeffs? 5 4 = some [2, 4, 4, 0, 1]
#guard coeffs? 5 5 = some [3, 4, 0, 0, 0, 1]
#guard coeffs? 5 6 = some [2, 0, 1, 4, 1, 0, 1]

#guard coeffs? 7 1 = some [4, 1]
#guard coeffs? 7 2 = some [3, 6, 1]
#guard coeffs? 7 3 = some [4, 0, 6, 1]
#guard coeffs? 7 4 = some [3, 4, 5, 0, 1]
#guard coeffs? 7 5 = some [4, 1, 0, 0, 0, 1]
#guard coeffs? 7 6 = some [3, 6, 4, 5, 1, 0, 1]

#guard coeffs? 11 1 = some [9, 1]
#guard coeffs? 11 2 = some [2, 7, 1]
#guard coeffs? 11 3 = some [9, 2, 0, 1]
#guard coeffs? 11 4 = some [2, 10, 8, 0, 1]
#guard coeffs? 11 5 = some [9, 0, 10, 0, 0, 1]
#guard coeffs? 11 6 = some [2, 7, 6, 4, 3, 0, 1]

#guard coeffs? 13 1 = some [11, 1]
#guard coeffs? 13 2 = some [2, 12, 1]
#guard coeffs? 13 3 = some [11, 2, 0, 1]
#guard coeffs? 13 4 = some [2, 12, 3, 0, 1]
#guard coeffs? 13 5 = some [11, 4, 0, 0, 0, 1]
#guard coeffs? 13 6 = some [2, 11, 11, 10, 0, 0, 1]

#guard luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 7 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 17 1 = (none : Option (FpPoly 17))

#guard coeffNats luebeckConwayPolynomial_2_1 = [1, 1]
#guard supportedEntry_2_1.poly = luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 1 = some supportedEntry_2_1.poly

#guard conwayPoly 2 1 supportedEntry_2_1 = luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 1 =
  some (conwayPoly 2 1 supportedEntry_2_1)
#guard 0 < FpPoly.degree (conwayPoly 2 1 supportedEntry_2_1)

-- Binary higher-degree entry: `(2, 4)`, using the exported supported entry.
#guard coeffNats supportedEntry_2_4.poly = [1, 1, 0, 0, 1]
#guard supportedEntry_2_4.poly = luebeckConwayPolynomial_2_4
#guard luebeckConwayPolynomial? 2 4 = some supportedEntry_2_4.poly
#guard conwayPoly 2 4 supportedEntry_2_4 = luebeckConwayPolynomial_2_4
#guard luebeckConwayPolynomial? 2 4 =
  some (conwayPoly 2 4 supportedEntry_2_4)
#guard 0 < FpPoly.degree (conwayPoly 2 4 supportedEntry_2_4)

-- Odd-prime entry: `(3, 1)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_1.poly = [1, 1]
#guard supportedEntry_3_1.poly = luebeckConwayPolynomial_3_1
#guard luebeckConwayPolynomial? 3 1 = some supportedEntry_3_1.poly
#guard conwayPoly 3 1 supportedEntry_3_1 = luebeckConwayPolynomial_3_1
#guard luebeckConwayPolynomial? 3 1 =
  some (conwayPoly 3 1 supportedEntry_3_1)
#guard 0 < FpPoly.degree (conwayPoly 3 1 supportedEntry_3_1)

-- Odd-prime entry: `(3, 2)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_2.poly = [2, 2, 1]
#guard supportedEntry_3_2.poly = luebeckConwayPolynomial_3_2
#guard luebeckConwayPolynomial? 3 2 = some supportedEntry_3_2.poly
#guard conwayPoly 3 2 supportedEntry_3_2 = luebeckConwayPolynomial_3_2
#guard luebeckConwayPolynomial? 3 2 =
  some (conwayPoly 3 2 supportedEntry_3_2)
#guard 0 < FpPoly.degree (conwayPoly 3 2 supportedEntry_3_2)

-- Odd-prime entry: `(3, 3)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_3.poly = [1, 2, 0, 1]
#guard supportedEntry_3_3.poly = luebeckConwayPolynomial_3_3
#guard luebeckConwayPolynomial? 3 3 = some supportedEntry_3_3.poly
#guard conwayPoly 3 3 supportedEntry_3_3 = luebeckConwayPolynomial_3_3
#guard luebeckConwayPolynomial? 3 3 =
  some (conwayPoly 3 3 supportedEntry_3_3)
#guard 0 < FpPoly.degree (conwayPoly 3 3 supportedEntry_3_3)

-- Odd-prime entry: `(3, 4)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_4.poly = [2, 0, 0, 2, 1]
#guard supportedEntry_3_4.poly = luebeckConwayPolynomial_3_4
#guard luebeckConwayPolynomial? 3 4 = some supportedEntry_3_4.poly
#guard conwayPoly 3 4 supportedEntry_3_4 = luebeckConwayPolynomial_3_4
#guard luebeckConwayPolynomial? 3 4 =
  some (conwayPoly 3 4 supportedEntry_3_4)
#guard 0 < FpPoly.degree (conwayPoly 3 4 supportedEntry_3_4)

-- Odd-prime entry: `(3, 5)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_5.poly = [1, 2, 0, 0, 0, 1]
#guard supportedEntry_3_5.poly = luebeckConwayPolynomial_3_5
#guard luebeckConwayPolynomial? 3 5 = some supportedEntry_3_5.poly
#guard conwayPoly 3 5 supportedEntry_3_5 = luebeckConwayPolynomial_3_5
#guard luebeckConwayPolynomial? 3 5 =
  some (conwayPoly 3 5 supportedEntry_3_5)
#guard 0 < FpPoly.degree (conwayPoly 3 5 supportedEntry_3_5)

-- Odd-prime entry: `(3, 6)`, using the exported supported entry.
#guard coeffNats supportedEntry_3_6.poly = [2, 2, 1, 0, 2, 0, 1]
#guard supportedEntry_3_6.poly = luebeckConwayPolynomial_3_6
#guard luebeckConwayPolynomial? 3 6 = some supportedEntry_3_6.poly
#guard conwayPoly 3 6 supportedEntry_3_6 = luebeckConwayPolynomial_3_6
#guard luebeckConwayPolynomial? 3 6 =
  some (conwayPoly 3 6 supportedEntry_3_6)
#guard 0 < FpPoly.degree (conwayPoly 3 6 supportedEntry_3_6)

-- Odd-prime entry: `(5, 1)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_1.poly = [3, 1]
#guard supportedEntry_5_1.poly = luebeckConwayPolynomial_5_1
#guard luebeckConwayPolynomial? 5 1 = some supportedEntry_5_1.poly
#guard conwayPoly 5 1 supportedEntry_5_1 = luebeckConwayPolynomial_5_1
#guard luebeckConwayPolynomial? 5 1 =
  some (conwayPoly 5 1 supportedEntry_5_1)
#guard 0 < FpPoly.degree (conwayPoly 5 1 supportedEntry_5_1)

-- Odd-prime entry: `(5, 2)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_2.poly = [2, 4, 1]
#guard supportedEntry_5_2.poly = luebeckConwayPolynomial_5_2
#guard luebeckConwayPolynomial? 5 2 = some supportedEntry_5_2.poly
#guard conwayPoly 5 2 supportedEntry_5_2 = luebeckConwayPolynomial_5_2
#guard luebeckConwayPolynomial? 5 2 =
  some (conwayPoly 5 2 supportedEntry_5_2)
#guard 0 < FpPoly.degree (conwayPoly 5 2 supportedEntry_5_2)

-- Odd-prime entry: `(5, 3)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_3.poly = [3, 3, 0, 1]
#guard supportedEntry_5_3.poly = luebeckConwayPolynomial_5_3
#guard luebeckConwayPolynomial? 5 3 = some supportedEntry_5_3.poly
#guard conwayPoly 5 3 supportedEntry_5_3 = luebeckConwayPolynomial_5_3
#guard luebeckConwayPolynomial? 5 3 =
  some (conwayPoly 5 3 supportedEntry_5_3)
#guard 0 < FpPoly.degree (conwayPoly 5 3 supportedEntry_5_3)

-- Odd-prime entry: `(5, 4)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_4.poly = [2, 4, 4, 0, 1]
#guard supportedEntry_5_4.poly = luebeckConwayPolynomial_5_4
#guard luebeckConwayPolynomial? 5 4 = some supportedEntry_5_4.poly
#guard conwayPoly 5 4 supportedEntry_5_4 = luebeckConwayPolynomial_5_4
#guard luebeckConwayPolynomial? 5 4 =
  some (conwayPoly 5 4 supportedEntry_5_4)
#guard 0 < FpPoly.degree (conwayPoly 5 4 supportedEntry_5_4)

-- Odd-prime entry: `(5, 5)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_5.poly = [3, 4, 0, 0, 0, 1]
#guard supportedEntry_5_5.poly = luebeckConwayPolynomial_5_5
#guard luebeckConwayPolynomial? 5 5 = some supportedEntry_5_5.poly
#guard conwayPoly 5 5 supportedEntry_5_5 = luebeckConwayPolynomial_5_5
#guard luebeckConwayPolynomial? 5 5 =
  some (conwayPoly 5 5 supportedEntry_5_5)
#guard 0 < FpPoly.degree (conwayPoly 5 5 supportedEntry_5_5)

-- Odd-prime entry: `(5, 6)`, using the exported supported entry.
#guard coeffNats supportedEntry_5_6.poly = [2, 0, 1, 4, 1, 0, 1]
#guard supportedEntry_5_6.poly = luebeckConwayPolynomial_5_6
#guard luebeckConwayPolynomial? 5 6 = some supportedEntry_5_6.poly
#guard conwayPoly 5 6 supportedEntry_5_6 = luebeckConwayPolynomial_5_6
#guard luebeckConwayPolynomial? 5 6 =
  some (conwayPoly 5 6 supportedEntry_5_6)
#guard 0 < FpPoly.degree (conwayPoly 5 6 supportedEntry_5_6)

-- Odd-prime entry: `(13, 1)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_1.poly = [11, 1]
#guard supportedEntry_13_1.poly = luebeckConwayPolynomial_13_1
#guard luebeckConwayPolynomial? 13 1 = some supportedEntry_13_1.poly
#guard conwayPoly 13 1 supportedEntry_13_1 = luebeckConwayPolynomial_13_1
#guard luebeckConwayPolynomial? 13 1 =
  some (conwayPoly 13 1 supportedEntry_13_1)
#guard 0 < FpPoly.degree (conwayPoly 13 1 supportedEntry_13_1)

-- Odd-prime entry: `(13, 2)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_2.poly = [2, 12, 1]
#guard supportedEntry_13_2.poly = luebeckConwayPolynomial_13_2
#guard luebeckConwayPolynomial? 13 2 = some supportedEntry_13_2.poly
#guard conwayPoly 13 2 supportedEntry_13_2 = luebeckConwayPolynomial_13_2
#guard luebeckConwayPolynomial? 13 2 =
  some (conwayPoly 13 2 supportedEntry_13_2)
#guard 0 < FpPoly.degree (conwayPoly 13 2 supportedEntry_13_2)

-- Odd-prime entry: `(13, 3)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_3.poly = [11, 2, 0, 1]
#guard supportedEntry_13_3.poly = luebeckConwayPolynomial_13_3
#guard luebeckConwayPolynomial? 13 3 = some supportedEntry_13_3.poly
#guard conwayPoly 13 3 supportedEntry_13_3 = luebeckConwayPolynomial_13_3
#guard luebeckConwayPolynomial? 13 3 =
  some (conwayPoly 13 3 supportedEntry_13_3)
#guard 0 < FpPoly.degree (conwayPoly 13 3 supportedEntry_13_3)

-- Odd-prime entry: `(13, 4)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_4.poly = [2, 12, 3, 0, 1]
#guard supportedEntry_13_4.poly = luebeckConwayPolynomial_13_4
#guard luebeckConwayPolynomial? 13 4 = some supportedEntry_13_4.poly
#guard conwayPoly 13 4 supportedEntry_13_4 = luebeckConwayPolynomial_13_4
#guard luebeckConwayPolynomial? 13 4 =
  some (conwayPoly 13 4 supportedEntry_13_4)
#guard 0 < FpPoly.degree (conwayPoly 13 4 supportedEntry_13_4)

-- Odd-prime entry: `(13, 5)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_5.poly = [11, 4, 0, 0, 0, 1]
#guard supportedEntry_13_5.poly = luebeckConwayPolynomial_13_5
#guard luebeckConwayPolynomial? 13 5 = some supportedEntry_13_5.poly
#guard conwayPoly 13 5 supportedEntry_13_5 = luebeckConwayPolynomial_13_5
#guard luebeckConwayPolynomial? 13 5 =
  some (conwayPoly 13 5 supportedEntry_13_5)
#guard 0 < FpPoly.degree (conwayPoly 13 5 supportedEntry_13_5)

-- Odd-prime entry: `(13, 6)`, using the exported supported entry.
#guard coeffNats supportedEntry_13_6.poly = [2, 11, 11, 10, 0, 0, 1]
#guard supportedEntry_13_6.poly = luebeckConwayPolynomial_13_6
#guard luebeckConwayPolynomial? 13 6 = some supportedEntry_13_6.poly
#guard conwayPoly 13 6 supportedEntry_13_6 = luebeckConwayPolynomial_13_6
#guard luebeckConwayPolynomial? 13 6 =
  some (conwayPoly 13 6 supportedEntry_13_6)
#guard 0 < FpPoly.degree (conwayPoly 13 6 supportedEntry_13_6)

end ConwayConformance
end Conway
end Hex
