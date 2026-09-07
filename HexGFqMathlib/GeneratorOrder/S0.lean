/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

/-- The Conway generator of GF(2^1) has order 1. -/
theorem orderOf_gen_2_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_1 Hex.FpPoly.X) = 2 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_1

/-- The Conway generator of GF(2^2) has order 3. -/
theorem orderOf_gen_2_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_2 Hex.FpPoly.X) = 2 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_2

/-- The Conway generator of GF(2^3) has order 7. -/
theorem orderOf_gen_2_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_3 Hex.FpPoly.X) = 2 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_3

/-- The Conway generator of GF(2^4) has order 15. -/
theorem orderOf_gen_2_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_4 Hex.FpPoly.X) = 2 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_4

/-- The Conway generator of GF(2^5) has order 31. -/
theorem orderOf_gen_2_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_5 Hex.FpPoly.X) = 2 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_5

/-- The Conway generator of GF(2^6) has order 63. -/
theorem orderOf_gen_2_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_6 Hex.FpPoly.X) = 2 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_6

/-- The Conway generator of GF(2^7) has order 127. -/
theorem orderOf_gen_2_7 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_7 Hex.FpPoly.X) = 2 ^ 7 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_7

/-- The Conway generator of GF(2^8) has order 255. -/
theorem orderOf_gen_2_8 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_8 Hex.FpPoly.X) = 2 ^ 8 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_8

/-- The Conway generator of GF(2^9) has order 511. -/
theorem orderOf_gen_2_9 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_9 Hex.FpPoly.X) = 2 ^ 9 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_9

/-- The Conway generator of GF(2^10) has order 1023. -/
theorem orderOf_gen_2_10 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_10 Hex.FpPoly.X) = 2 ^ 10 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_10

/-- The Conway generator of GF(2^11) has order 2047. -/
theorem orderOf_gen_2_11 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_11 Hex.FpPoly.X) = 2 ^ 11 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_11

/-- The Conway generator of GF(2^12) has order 4095. -/
theorem orderOf_gen_2_12 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_12 Hex.FpPoly.X) = 2 ^ 12 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_12

/-- The Conway generator of GF(2^13) has order 8191. -/
theorem orderOf_gen_2_13 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_13 Hex.FpPoly.X) = 2 ^ 13 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_13

/-- The Conway generator of GF(2^14) has order 16383. -/
theorem orderOf_gen_2_14 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_14 Hex.FpPoly.X) = 2 ^ 14 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_14

/-- The Conway generator of GF(2^15) has order 32767. -/
theorem orderOf_gen_2_15 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_15 Hex.FpPoly.X) = 2 ^ 15 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_15

/-- The Conway generator of GF(2^16) has order 65535. -/
theorem orderOf_gen_2_16 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_16 Hex.FpPoly.X) = 2 ^ 16 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_16

/-- The Conway generator of GF(3^1) has order 2. -/
theorem orderOf_gen_3_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_1 Hex.FpPoly.X) = 3 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_1

/-- The Conway generator of GF(3^2) has order 8. -/
theorem orderOf_gen_3_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_2 Hex.FpPoly.X) = 3 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_2

/-- The Conway generator of GF(3^3) has order 26. -/
theorem orderOf_gen_3_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_3 Hex.FpPoly.X) = 3 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_3

/-- The Conway generator of GF(3^4) has order 80. -/
theorem orderOf_gen_3_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_4 Hex.FpPoly.X) = 3 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_4

/-- The Conway generator of GF(3^5) has order 242. -/
theorem orderOf_gen_3_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_5 Hex.FpPoly.X) = 3 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_5

/-- The Conway generator of GF(3^6) has order 728. -/
theorem orderOf_gen_3_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_6 Hex.FpPoly.X) = 3 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_6

/-- The Conway generator of GF(3^7) has order 2186. -/
theorem orderOf_gen_3_7 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_7 Hex.FpPoly.X) = 3 ^ 7 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_7

/-- The Conway generator of GF(3^8) has order 6560. -/
theorem orderOf_gen_3_8 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_8 Hex.FpPoly.X) = 3 ^ 8 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_8

/-- The Conway generator of GF(5^1) has order 4. -/
theorem orderOf_gen_5_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_1 Hex.FpPoly.X) = 5 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_1

/-- The Conway generator of GF(5^2) has order 24. -/
theorem orderOf_gen_5_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_2 Hex.FpPoly.X) = 5 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_2

/-- The Conway generator of GF(5^3) has order 124. -/
theorem orderOf_gen_5_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_3 Hex.FpPoly.X) = 5 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_3

/-- The Conway generator of GF(5^4) has order 624. -/
theorem orderOf_gen_5_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_4 Hex.FpPoly.X) = 5 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_4

/-- The Conway generator of GF(5^5) has order 3124. -/
theorem orderOf_gen_5_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_5 Hex.FpPoly.X) = 5 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_5

/-- The Conway generator of GF(5^6) has order 15624. -/
theorem orderOf_gen_5_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_6 Hex.FpPoly.X) = 5 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_6

/-- The Conway generator of GF(5^7) has order 78124. -/
theorem orderOf_gen_5_7 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_7 Hex.FpPoly.X) = 5 ^ 7 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_7

/-- The Conway generator of GF(5^8) has order 390624. -/
theorem orderOf_gen_5_8 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_8 Hex.FpPoly.X) = 5 ^ 8 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_8

/-- The Conway generator of GF(7^1) has order 6. -/
theorem orderOf_gen_7_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_1 Hex.FpPoly.X) = 7 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_1

/-- The Conway generator of GF(7^2) has order 48. -/
theorem orderOf_gen_7_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_2 Hex.FpPoly.X) = 7 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_2

/-- The Conway generator of GF(7^3) has order 342. -/
theorem orderOf_gen_7_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_3 Hex.FpPoly.X) = 7 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_3

/-- The Conway generator of GF(7^4) has order 2400. -/
theorem orderOf_gen_7_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_4 Hex.FpPoly.X) = 7 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_4

/-- The Conway generator of GF(7^5) has order 16806. -/
theorem orderOf_gen_7_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_5 Hex.FpPoly.X) = 7 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_5

/-- The Conway generator of GF(7^6) has order 117648. -/
theorem orderOf_gen_7_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_6 Hex.FpPoly.X) = 7 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_6

/-- The Conway generator of GF(7^7) has order 823542. -/
theorem orderOf_gen_7_7 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_7 Hex.FpPoly.X) = 7 ^ 7 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_7

/-- The Conway generator of GF(7^8) has order 5764800. -/
theorem orderOf_gen_7_8 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_8 Hex.FpPoly.X) = 7 ^ 8 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_8

/-- The Conway generator of GF(11^1) has order 10. -/
theorem orderOf_gen_11_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_1 Hex.FpPoly.X) = 11 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_1

/-- The Conway generator of GF(11^2) has order 120. -/
theorem orderOf_gen_11_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_2 Hex.FpPoly.X) = 11 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_2

/-- The Conway generator of GF(11^3) has order 1330. -/
theorem orderOf_gen_11_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_3 Hex.FpPoly.X) = 11 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_3

/-- The Conway generator of GF(11^4) has order 14640. -/
theorem orderOf_gen_11_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_4 Hex.FpPoly.X) = 11 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_4

/-- The Conway generator of GF(11^5) has order 161050. -/
theorem orderOf_gen_11_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_5 Hex.FpPoly.X) = 11 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_5

/-- The Conway generator of GF(11^6) has order 1771560. -/
theorem orderOf_gen_11_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_6 Hex.FpPoly.X) = 11 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_6

/-- The Conway generator of GF(13^1) has order 12. -/
theorem orderOf_gen_13_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_1 Hex.FpPoly.X) = 13 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_1

/-- The Conway generator of GF(13^2) has order 168. -/
theorem orderOf_gen_13_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_2 Hex.FpPoly.X) = 13 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_2

/-- The Conway generator of GF(13^3) has order 2196. -/
theorem orderOf_gen_13_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_3 Hex.FpPoly.X) = 13 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_3

/-- The Conway generator of GF(13^4) has order 28560. -/
theorem orderOf_gen_13_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_4 Hex.FpPoly.X) = 13 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_4

/-- The Conway generator of GF(13^5) has order 371292. -/
theorem orderOf_gen_13_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_5 Hex.FpPoly.X) = 13 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_5

/-- The Conway generator of GF(13^6) has order 4826808. -/
theorem orderOf_gen_13_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_6 Hex.FpPoly.X) = 13 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_6

/-- The Conway generator of GF(17^1) has order 16. -/
theorem orderOf_gen_17_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_17_1 Hex.FpPoly.X) = 17 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_17_1

/-- The Conway generator of GF(17^2) has order 288. -/
theorem orderOf_gen_17_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_17_2 Hex.FpPoly.X) = 17 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_17_2

/-- The Conway generator of GF(17^3) has order 4912. -/
theorem orderOf_gen_17_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_17_3 Hex.FpPoly.X) = 17 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_17_3

/-- The Conway generator of GF(17^4) has order 83520. -/
theorem orderOf_gen_17_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_17_4 Hex.FpPoly.X) = 17 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_17_4

/-- The Conway generator of GF(19^1) has order 18. -/
theorem orderOf_gen_19_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_19_1 Hex.FpPoly.X) = 19 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_19_1

/-- The Conway generator of GF(19^2) has order 360. -/
theorem orderOf_gen_19_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_19_2 Hex.FpPoly.X) = 19 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_19_2

/-- The Conway generator of GF(19^3) has order 6858. -/
theorem orderOf_gen_19_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_19_3 Hex.FpPoly.X) = 19 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_19_3

/-- The Conway generator of GF(19^4) has order 130320. -/
theorem orderOf_gen_19_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_19_4 Hex.FpPoly.X) = 19 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_19_4

/-- The Conway generator of GF(23^1) has order 22. -/
theorem orderOf_gen_23_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_23_1 Hex.FpPoly.X) = 23 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_23_1

/-- The Conway generator of GF(23^2) has order 528. -/
theorem orderOf_gen_23_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_23_2 Hex.FpPoly.X) = 23 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_23_2

/-- The Conway generator of GF(23^3) has order 12166. -/
theorem orderOf_gen_23_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_23_3 Hex.FpPoly.X) = 23 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_23_3

/-- The Conway generator of GF(23^4) has order 279840. -/
theorem orderOf_gen_23_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_23_4 Hex.FpPoly.X) = 23 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_23_4

/-- The Conway generator of GF(29^1) has order 28. -/
theorem orderOf_gen_29_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_29_1 Hex.FpPoly.X) = 29 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_29_1

/-- The Conway generator of GF(29^2) has order 840. -/
theorem orderOf_gen_29_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_29_2 Hex.FpPoly.X) = 29 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_29_2

/-- The Conway generator of GF(29^3) has order 24388. -/
theorem orderOf_gen_29_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_29_3 Hex.FpPoly.X) = 29 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_29_3

/-- The Conway generator of GF(29^4) has order 707280. -/
theorem orderOf_gen_29_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_29_4 Hex.FpPoly.X) = 29 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_29_4

/-- The Conway generator of GF(31^1) has order 30. -/
theorem orderOf_gen_31_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_31_1 Hex.FpPoly.X) = 31 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_31_1

/-- The Conway generator of GF(31^2) has order 960. -/
theorem orderOf_gen_31_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_31_2 Hex.FpPoly.X) = 31 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_31_2

/-- The Conway generator of GF(31^3) has order 29790. -/
theorem orderOf_gen_31_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_31_3 Hex.FpPoly.X) = 31 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_31_3

/-- The Conway generator of GF(31^4) has order 923520. -/
theorem orderOf_gen_31_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_31_4 Hex.FpPoly.X) = 31 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_31_4

/-- The Conway generator of GF(37^1) has order 36. -/
theorem orderOf_gen_37_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_37_1 Hex.FpPoly.X) = 37 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_37_1

/-- The Conway generator of GF(37^2) has order 1368. -/
theorem orderOf_gen_37_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_37_2 Hex.FpPoly.X) = 37 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_37_2

/-- The Conway generator of GF(37^3) has order 50652. -/
theorem orderOf_gen_37_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_37_3 Hex.FpPoly.X) = 37 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_37_3

/-- The Conway generator of GF(37^4) has order 1874160. -/
theorem orderOf_gen_37_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_37_4 Hex.FpPoly.X) = 37 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_37_4

/-- The Conway generator of GF(41^1) has order 40. -/
theorem orderOf_gen_41_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_41_1 Hex.FpPoly.X) = 41 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_41_1

/-- The Conway generator of GF(41^2) has order 1680. -/
theorem orderOf_gen_41_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_41_2 Hex.FpPoly.X) = 41 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_41_2

/-- The Conway generator of GF(41^3) has order 68920. -/
theorem orderOf_gen_41_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_41_3 Hex.FpPoly.X) = 41 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_41_3

/-- The Conway generator of GF(41^4) has order 2825760. -/
theorem orderOf_gen_41_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_41_4 Hex.FpPoly.X) = 41 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_41_4

/-- The Conway generator of GF(43^1) has order 42. -/
theorem orderOf_gen_43_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_43_1 Hex.FpPoly.X) = 43 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_43_1

/-- The Conway generator of GF(43^2) has order 1848. -/
theorem orderOf_gen_43_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_43_2 Hex.FpPoly.X) = 43 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_43_2

/-- The Conway generator of GF(43^3) has order 79506. -/
theorem orderOf_gen_43_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_43_3 Hex.FpPoly.X) = 43 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_43_3

/-- The Conway generator of GF(43^4) has order 3418800. -/
theorem orderOf_gen_43_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_43_4 Hex.FpPoly.X) = 43 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_43_4

/-- The Conway generator of GF(47^1) has order 46. -/
theorem orderOf_gen_47_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_47_1 Hex.FpPoly.X) = 47 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_47_1

/-- The Conway generator of GF(47^2) has order 2208. -/
theorem orderOf_gen_47_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_47_2 Hex.FpPoly.X) = 47 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_47_2

/-- The Conway generator of GF(47^3) has order 103822. -/
theorem orderOf_gen_47_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_47_3 Hex.FpPoly.X) = 47 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_47_3

/-- The Conway generator of GF(47^4) has order 4879680. -/
theorem orderOf_gen_47_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_47_4 Hex.FpPoly.X) = 47 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_47_4

/-- The Conway generator of GF(53^1) has order 52. -/
theorem orderOf_gen_53_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_53_1 Hex.FpPoly.X) = 53 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_53_1

/-- The Conway generator of GF(53^2) has order 2808. -/
theorem orderOf_gen_53_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_53_2 Hex.FpPoly.X) = 53 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_53_2

/-- The Conway generator of GF(53^3) has order 148876. -/
theorem orderOf_gen_53_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_53_3 Hex.FpPoly.X) = 53 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_53_3

/-- The Conway generator of GF(53^4) has order 7890480. -/
theorem orderOf_gen_53_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_53_4 Hex.FpPoly.X) = 53 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_53_4

/-- The Conway generator of GF(59^1) has order 58. -/
theorem orderOf_gen_59_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_59_1 Hex.FpPoly.X) = 59 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_59_1

/-- The Conway generator of GF(59^2) has order 3480. -/
theorem orderOf_gen_59_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_59_2 Hex.FpPoly.X) = 59 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_59_2

/-- The Conway generator of GF(59^3) has order 205378. -/
theorem orderOf_gen_59_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_59_3 Hex.FpPoly.X) = 59 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_59_3

/-- The Conway generator of GF(59^4) has order 12117360. -/
theorem orderOf_gen_59_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_59_4 Hex.FpPoly.X) = 59 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_59_4

/-- The Conway generator of GF(61^1) has order 60. -/
theorem orderOf_gen_61_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_61_1 Hex.FpPoly.X) = 61 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_61_1

/-- The Conway generator of GF(61^2) has order 3720. -/
theorem orderOf_gen_61_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_61_2 Hex.FpPoly.X) = 61 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_61_2

/-- The Conway generator of GF(61^3) has order 226980. -/
theorem orderOf_gen_61_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_61_3 Hex.FpPoly.X) = 61 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_61_3

/-- The Conway generator of GF(61^4) has order 13845840. -/
theorem orderOf_gen_61_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_61_4 Hex.FpPoly.X) = 61 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_61_4

/-- The Conway generator of GF(67^1) has order 66. -/
theorem orderOf_gen_67_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_67_1 Hex.FpPoly.X) = 67 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_67_1

/-- The Conway generator of GF(67^2) has order 4488. -/
theorem orderOf_gen_67_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_67_2 Hex.FpPoly.X) = 67 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_67_2

/-- The Conway generator of GF(67^3) has order 300762. -/
theorem orderOf_gen_67_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_67_3 Hex.FpPoly.X) = 67 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_67_3

/-- The Conway generator of GF(67^4) has order 20151120. -/
theorem orderOf_gen_67_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_67_4 Hex.FpPoly.X) = 67 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_67_4

/-- The Conway generator of GF(71^1) has order 70. -/
theorem orderOf_gen_71_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_71_1 Hex.FpPoly.X) = 71 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_71_1

/-- The Conway generator of GF(71^2) has order 5040. -/
theorem orderOf_gen_71_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_71_2 Hex.FpPoly.X) = 71 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_71_2

/-- The Conway generator of GF(71^3) has order 357910. -/
theorem orderOf_gen_71_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_71_3 Hex.FpPoly.X) = 71 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_71_3

/-- The Conway generator of GF(71^4) has order 25411680. -/
theorem orderOf_gen_71_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_71_4 Hex.FpPoly.X) = 71 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_71_4

/-- The Conway generator of GF(73^1) has order 72. -/
theorem orderOf_gen_73_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_73_1 Hex.FpPoly.X) = 73 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_73_1

/-- The Conway generator of GF(73^2) has order 5328. -/
theorem orderOf_gen_73_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_73_2 Hex.FpPoly.X) = 73 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_73_2

/-- The Conway generator of GF(73^3) has order 389016. -/
theorem orderOf_gen_73_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_73_3 Hex.FpPoly.X) = 73 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_73_3

/-- The Conway generator of GF(73^4) has order 28398240. -/
theorem orderOf_gen_73_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_73_4 Hex.FpPoly.X) = 73 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_73_4

/-- The Conway generator of GF(79^1) has order 78. -/
theorem orderOf_gen_79_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_79_1 Hex.FpPoly.X) = 79 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_79_1

/-- The Conway generator of GF(79^2) has order 6240. -/
theorem orderOf_gen_79_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_79_2 Hex.FpPoly.X) = 79 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_79_2

/-- The Conway generator of GF(79^3) has order 493038. -/
theorem orderOf_gen_79_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_79_3 Hex.FpPoly.X) = 79 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_79_3

/-- The Conway generator of GF(79^4) has order 38950080. -/
theorem orderOf_gen_79_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_79_4 Hex.FpPoly.X) = 79 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_79_4

/-- The Conway generator of GF(83^1) has order 82. -/
theorem orderOf_gen_83_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_83_1 Hex.FpPoly.X) = 83 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_83_1

/-- The Conway generator of GF(83^2) has order 6888. -/
theorem orderOf_gen_83_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_83_2 Hex.FpPoly.X) = 83 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_83_2

/-- The Conway generator of GF(83^3) has order 571786. -/
theorem orderOf_gen_83_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_83_3 Hex.FpPoly.X) = 83 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_83_3

/-- The Conway generator of GF(83^4) has order 47458320. -/
theorem orderOf_gen_83_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_83_4 Hex.FpPoly.X) = 83 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_83_4

/-- The Conway generator of GF(89^1) has order 88. -/
theorem orderOf_gen_89_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_89_1 Hex.FpPoly.X) = 89 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_89_1

/-- The Conway generator of GF(89^2) has order 7920. -/
theorem orderOf_gen_89_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_89_2 Hex.FpPoly.X) = 89 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_89_2

/-- The Conway generator of GF(89^3) has order 704968. -/
theorem orderOf_gen_89_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_89_3 Hex.FpPoly.X) = 89 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_89_3

/-- The Conway generator of GF(89^4) has order 62742240. -/
theorem orderOf_gen_89_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_89_4 Hex.FpPoly.X) = 89 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_89_4

/-- The Conway generator of GF(97^1) has order 96. -/
theorem orderOf_gen_97_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_97_1 Hex.FpPoly.X) = 97 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_97_1

/-- The Conway generator of GF(97^2) has order 9408. -/
theorem orderOf_gen_97_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_97_2 Hex.FpPoly.X) = 97 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_97_2

/-- The Conway generator of GF(97^3) has order 912672. -/
theorem orderOf_gen_97_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_97_3 Hex.FpPoly.X) = 97 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_97_3

/-- The Conway generator of GF(97^4) has order 88529280. -/
theorem orderOf_gen_97_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_97_4 Hex.FpPoly.X) = 97 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_97_4

end HexGFqMathlib
