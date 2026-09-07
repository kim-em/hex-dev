/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

/-- The Conway generator of GF(887^1) has order 886. -/
theorem orderOf_gen_887_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_887_1 Hex.FpPoly.X) = 887 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_887_1

/-- The Conway generator of GF(887^2) has order 786768. -/
theorem orderOf_gen_887_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_887_2 Hex.FpPoly.X) = 887 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_887_2

/-- The Conway generator of GF(887^3) has order 697864102. -/
theorem orderOf_gen_887_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_887_3 Hex.FpPoly.X) = 887 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_887_3

/-- The Conway generator of GF(887^4) has order 619005459360. -/
theorem orderOf_gen_887_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_887_4 Hex.FpPoly.X) = 887 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_887_4

/-- The Conway generator of GF(907^1) has order 906. -/
theorem orderOf_gen_907_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_907_1 Hex.FpPoly.X) = 907 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_907_1

/-- The Conway generator of GF(907^2) has order 822648. -/
theorem orderOf_gen_907_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_907_2 Hex.FpPoly.X) = 907 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_907_2

/-- The Conway generator of GF(907^3) has order 746142642. -/
theorem orderOf_gen_907_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_907_3 Hex.FpPoly.X) = 907 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_907_3

/-- The Conway generator of GF(907^4) has order 676751377200. -/
theorem orderOf_gen_907_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_907_4 Hex.FpPoly.X) = 907 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_907_4

/-- The Conway generator of GF(911^1) has order 910. -/
theorem orderOf_gen_911_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_911_1 Hex.FpPoly.X) = 911 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_911_1

/-- The Conway generator of GF(911^2) has order 829920. -/
theorem orderOf_gen_911_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_911_2 Hex.FpPoly.X) = 911 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_911_2

/-- The Conway generator of GF(911^3) has order 756058030. -/
theorem orderOf_gen_911_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_911_3 Hex.FpPoly.X) = 911 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_911_3

/-- The Conway generator of GF(911^4) has order 688768866240. -/
theorem orderOf_gen_911_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_911_4 Hex.FpPoly.X) = 911 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_911_4

/-- The Conway generator of GF(919^1) has order 918. -/
theorem orderOf_gen_919_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_919_1 Hex.FpPoly.X) = 919 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_919_1

/-- The Conway generator of GF(919^2) has order 844560. -/
theorem orderOf_gen_919_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_919_2 Hex.FpPoly.X) = 919 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_919_2

/-- The Conway generator of GF(919^3) has order 776151558. -/
theorem orderOf_gen_919_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_919_3 Hex.FpPoly.X) = 919 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_919_3

/-- The Conway generator of GF(919^4) has order 713283282720. -/
theorem orderOf_gen_919_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_919_4 Hex.FpPoly.X) = 919 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_919_4

/-- The Conway generator of GF(929^1) has order 928. -/
theorem orderOf_gen_929_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_929_1 Hex.FpPoly.X) = 929 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_929_1

/-- The Conway generator of GF(929^2) has order 863040. -/
theorem orderOf_gen_929_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_929_2 Hex.FpPoly.X) = 929 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_929_2

/-- The Conway generator of GF(929^3) has order 801765088. -/
theorem orderOf_gen_929_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_929_3 Hex.FpPoly.X) = 929 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_929_3

/-- The Conway generator of GF(929^4) has order 744839767680. -/
theorem orderOf_gen_929_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_929_4 Hex.FpPoly.X) = 929 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_929_4

/-- The Conway generator of GF(937^1) has order 936. -/
theorem orderOf_gen_937_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_937_1 Hex.FpPoly.X) = 937 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_937_1

/-- The Conway generator of GF(937^2) has order 877968. -/
theorem orderOf_gen_937_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_937_2 Hex.FpPoly.X) = 937 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_937_2

/-- The Conway generator of GF(937^3) has order 822656952. -/
theorem orderOf_gen_937_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_937_3 Hex.FpPoly.X) = 937 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_937_3

/-- The Conway generator of GF(937^4) has order 770829564960. -/
theorem orderOf_gen_937_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_937_4 Hex.FpPoly.X) = 937 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_937_4

/-- The Conway generator of GF(941^1) has order 940. -/
theorem orderOf_gen_941_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_941_1 Hex.FpPoly.X) = 941 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_941_1

/-- The Conway generator of GF(941^2) has order 885480. -/
theorem orderOf_gen_941_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_941_2 Hex.FpPoly.X) = 941 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_941_2

/-- The Conway generator of GF(941^3) has order 833237620. -/
theorem orderOf_gen_941_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_941_3 Hex.FpPoly.X) = 941 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_941_3

/-- The Conway generator of GF(941^4) has order 784076601360. -/
theorem orderOf_gen_941_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_941_4 Hex.FpPoly.X) = 941 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_941_4

/-- The Conway generator of GF(947^1) has order 946. -/
theorem orderOf_gen_947_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_947_1 Hex.FpPoly.X) = 947 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_947_1

/-- The Conway generator of GF(947^2) has order 896808. -/
theorem orderOf_gen_947_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_947_2 Hex.FpPoly.X) = 947 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_947_2

/-- The Conway generator of GF(947^3) has order 849278122. -/
theorem orderOf_gen_947_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_947_3 Hex.FpPoly.X) = 947 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_947_3

/-- The Conway generator of GF(947^4) has order 804266382480. -/
theorem orderOf_gen_947_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_947_4 Hex.FpPoly.X) = 947 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_947_4

/-- The Conway generator of GF(953^1) has order 952. -/
theorem orderOf_gen_953_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_953_1 Hex.FpPoly.X) = 953 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_953_1

/-- The Conway generator of GF(953^2) has order 908208. -/
theorem orderOf_gen_953_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_953_2 Hex.FpPoly.X) = 953 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_953_2

/-- The Conway generator of GF(953^3) has order 865523176. -/
theorem orderOf_gen_953_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_953_3 Hex.FpPoly.X) = 953 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_953_3

/-- The Conway generator of GF(953^4) has order 824843587680. -/
theorem orderOf_gen_953_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_953_4 Hex.FpPoly.X) = 953 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_953_4

/-- The Conway generator of GF(967^1) has order 966. -/
theorem orderOf_gen_967_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_967_1 Hex.FpPoly.X) = 967 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_967_1

/-- The Conway generator of GF(967^2) has order 935088. -/
theorem orderOf_gen_967_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_967_2 Hex.FpPoly.X) = 967 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_967_2

/-- The Conway generator of GF(967^3) has order 904231062. -/
theorem orderOf_gen_967_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_967_3 Hex.FpPoly.X) = 967 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_967_3

/-- The Conway generator of GF(967^4) has order 874391437920. -/
theorem orderOf_gen_967_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_967_4 Hex.FpPoly.X) = 967 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_967_4

/-- The Conway generator of GF(971^1) has order 970. -/
theorem orderOf_gen_971_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_971_1 Hex.FpPoly.X) = 971 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_971_1

/-- The Conway generator of GF(971^2) has order 942840. -/
theorem orderOf_gen_971_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_971_2 Hex.FpPoly.X) = 971 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_971_2

/-- The Conway generator of GF(971^3) has order 915498610. -/
theorem orderOf_gen_971_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_971_3 Hex.FpPoly.X) = 971 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_971_3

/-- The Conway generator of GF(971^4) has order 888949151280. -/
theorem orderOf_gen_971_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_971_4 Hex.FpPoly.X) = 971 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_971_4

/-- The Conway generator of GF(977^1) has order 976. -/
theorem orderOf_gen_977_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_977_1 Hex.FpPoly.X) = 977 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_977_1

/-- The Conway generator of GF(977^2) has order 954528. -/
theorem orderOf_gen_977_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_977_2 Hex.FpPoly.X) = 977 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_977_2

/-- The Conway generator of GF(977^3) has order 932574832. -/
theorem orderOf_gen_977_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_977_3 Hex.FpPoly.X) = 977 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_977_3

/-- The Conway generator of GF(977^4) has order 911125611840. -/
theorem orderOf_gen_977_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_977_4 Hex.FpPoly.X) = 977 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_977_4

/-- The Conway generator of GF(983^1) has order 982. -/
theorem orderOf_gen_983_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_983_1 Hex.FpPoly.X) = 983 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_983_1

/-- The Conway generator of GF(983^2) has order 966288. -/
theorem orderOf_gen_983_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_983_2 Hex.FpPoly.X) = 983 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_983_2

/-- The Conway generator of GF(983^3) has order 949862086. -/
theorem orderOf_gen_983_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_983_3 Hex.FpPoly.X) = 983 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_983_3

/-- The Conway generator of GF(983^4) has order 933714431520. -/
theorem orderOf_gen_983_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_983_4 Hex.FpPoly.X) = 983 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_983_4

/-- The Conway generator of GF(991^1) has order 990. -/
theorem orderOf_gen_991_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_991_1 Hex.FpPoly.X) = 991 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_991_1

/-- The Conway generator of GF(991^2) has order 982080. -/
theorem orderOf_gen_991_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_991_2 Hex.FpPoly.X) = 991 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_991_2

/-- The Conway generator of GF(991^3) has order 973242270. -/
theorem orderOf_gen_991_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_991_3 Hex.FpPoly.X) = 991 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_991_3

/-- The Conway generator of GF(991^4) has order 964483090560. -/
theorem orderOf_gen_991_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_991_4 Hex.FpPoly.X) = 991 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_991_4

/-- The Conway generator of GF(997^1) has order 996. -/
theorem orderOf_gen_997_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_997_1 Hex.FpPoly.X) = 997 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_997_1

/-- The Conway generator of GF(997^2) has order 994008. -/
theorem orderOf_gen_997_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_997_2 Hex.FpPoly.X) = 997 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_997_2

/-- The Conway generator of GF(997^3) has order 991026972. -/
theorem orderOf_gen_997_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_997_3 Hex.FpPoly.X) = 997 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_997_3

/-- The Conway generator of GF(997^4) has order 988053892080. -/
theorem orderOf_gen_997_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_997_4 Hex.FpPoly.X) = 997 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_997_4

end HexGFqMathlib
