/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

/-- The Conway generator of GF(101^1) has order 100. -/
theorem orderOf_gen_101_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_101_1 Hex.FpPoly.X) = 101 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_101_1

/-- The Conway generator of GF(101^2) has order 10200. -/
theorem orderOf_gen_101_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_101_2 Hex.FpPoly.X) = 101 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_101_2

/-- The Conway generator of GF(101^3) has order 1030300. -/
theorem orderOf_gen_101_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_101_3 Hex.FpPoly.X) = 101 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_101_3

/-- The Conway generator of GF(101^4) has order 104060400. -/
theorem orderOf_gen_101_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_101_4 Hex.FpPoly.X) = 101 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_101_4

/-- The Conway generator of GF(103^1) has order 102. -/
theorem orderOf_gen_103_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_103_1 Hex.FpPoly.X) = 103 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_103_1

/-- The Conway generator of GF(103^2) has order 10608. -/
theorem orderOf_gen_103_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_103_2 Hex.FpPoly.X) = 103 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_103_2

/-- The Conway generator of GF(103^3) has order 1092726. -/
theorem orderOf_gen_103_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_103_3 Hex.FpPoly.X) = 103 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_103_3

/-- The Conway generator of GF(103^4) has order 112550880. -/
theorem orderOf_gen_103_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_103_4 Hex.FpPoly.X) = 103 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_103_4

/-- The Conway generator of GF(107^1) has order 106. -/
theorem orderOf_gen_107_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_107_1 Hex.FpPoly.X) = 107 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_107_1

/-- The Conway generator of GF(107^2) has order 11448. -/
theorem orderOf_gen_107_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_107_2 Hex.FpPoly.X) = 107 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_107_2

/-- The Conway generator of GF(107^3) has order 1225042. -/
theorem orderOf_gen_107_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_107_3 Hex.FpPoly.X) = 107 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_107_3

/-- The Conway generator of GF(107^4) has order 131079600. -/
theorem orderOf_gen_107_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_107_4 Hex.FpPoly.X) = 107 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_107_4

/-- The Conway generator of GF(109^1) has order 108. -/
theorem orderOf_gen_109_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_109_1 Hex.FpPoly.X) = 109 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_109_1

/-- The Conway generator of GF(109^2) has order 11880. -/
theorem orderOf_gen_109_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_109_2 Hex.FpPoly.X) = 109 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_109_2

/-- The Conway generator of GF(109^3) has order 1295028. -/
theorem orderOf_gen_109_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_109_3 Hex.FpPoly.X) = 109 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_109_3

/-- The Conway generator of GF(109^4) has order 141158160. -/
theorem orderOf_gen_109_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_109_4 Hex.FpPoly.X) = 109 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_109_4

/-- The Conway generator of GF(113^1) has order 112. -/
theorem orderOf_gen_113_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_113_1 Hex.FpPoly.X) = 113 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_113_1

/-- The Conway generator of GF(113^2) has order 12768. -/
theorem orderOf_gen_113_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_113_2 Hex.FpPoly.X) = 113 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_113_2

/-- The Conway generator of GF(113^3) has order 1442896. -/
theorem orderOf_gen_113_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_113_3 Hex.FpPoly.X) = 113 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_113_3

/-- The Conway generator of GF(113^4) has order 163047360. -/
theorem orderOf_gen_113_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_113_4 Hex.FpPoly.X) = 113 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_113_4

/-- The Conway generator of GF(127^1) has order 126. -/
theorem orderOf_gen_127_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_127_1 Hex.FpPoly.X) = 127 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_127_1

/-- The Conway generator of GF(127^2) has order 16128. -/
theorem orderOf_gen_127_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_127_2 Hex.FpPoly.X) = 127 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_127_2

/-- The Conway generator of GF(127^3) has order 2048382. -/
theorem orderOf_gen_127_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_127_3 Hex.FpPoly.X) = 127 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_127_3

/-- The Conway generator of GF(127^4) has order 260144640. -/
theorem orderOf_gen_127_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_127_4 Hex.FpPoly.X) = 127 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_127_4

/-- The Conway generator of GF(131^1) has order 130. -/
theorem orderOf_gen_131_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_131_1 Hex.FpPoly.X) = 131 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_131_1

/-- The Conway generator of GF(131^2) has order 17160. -/
theorem orderOf_gen_131_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_131_2 Hex.FpPoly.X) = 131 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_131_2

/-- The Conway generator of GF(131^3) has order 2248090. -/
theorem orderOf_gen_131_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_131_3 Hex.FpPoly.X) = 131 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_131_3

/-- The Conway generator of GF(131^4) has order 294499920. -/
theorem orderOf_gen_131_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_131_4 Hex.FpPoly.X) = 131 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_131_4

/-- The Conway generator of GF(137^1) has order 136. -/
theorem orderOf_gen_137_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_137_1 Hex.FpPoly.X) = 137 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_137_1

/-- The Conway generator of GF(137^2) has order 18768. -/
theorem orderOf_gen_137_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_137_2 Hex.FpPoly.X) = 137 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_137_2

/-- The Conway generator of GF(137^3) has order 2571352. -/
theorem orderOf_gen_137_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_137_3 Hex.FpPoly.X) = 137 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_137_3

/-- The Conway generator of GF(137^4) has order 352275360. -/
theorem orderOf_gen_137_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_137_4 Hex.FpPoly.X) = 137 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_137_4

/-- The Conway generator of GF(139^1) has order 138. -/
theorem orderOf_gen_139_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_139_1 Hex.FpPoly.X) = 139 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_139_1

/-- The Conway generator of GF(139^2) has order 19320. -/
theorem orderOf_gen_139_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_139_2 Hex.FpPoly.X) = 139 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_139_2

/-- The Conway generator of GF(139^3) has order 2685618. -/
theorem orderOf_gen_139_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_139_3 Hex.FpPoly.X) = 139 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_139_3

/-- The Conway generator of GF(139^4) has order 373301040. -/
theorem orderOf_gen_139_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_139_4 Hex.FpPoly.X) = 139 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_139_4

/-- The Conway generator of GF(149^1) has order 148. -/
theorem orderOf_gen_149_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_149_1 Hex.FpPoly.X) = 149 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_149_1

/-- The Conway generator of GF(149^2) has order 22200. -/
theorem orderOf_gen_149_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_149_2 Hex.FpPoly.X) = 149 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_149_2

/-- The Conway generator of GF(149^3) has order 3307948. -/
theorem orderOf_gen_149_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_149_3 Hex.FpPoly.X) = 149 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_149_3

/-- The Conway generator of GF(149^4) has order 492884400. -/
theorem orderOf_gen_149_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_149_4 Hex.FpPoly.X) = 149 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_149_4

/-- The Conway generator of GF(151^1) has order 150. -/
theorem orderOf_gen_151_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_151_1 Hex.FpPoly.X) = 151 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_151_1

/-- The Conway generator of GF(151^2) has order 22800. -/
theorem orderOf_gen_151_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_151_2 Hex.FpPoly.X) = 151 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_151_2

/-- The Conway generator of GF(151^3) has order 3442950. -/
theorem orderOf_gen_151_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_151_3 Hex.FpPoly.X) = 151 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_151_3

/-- The Conway generator of GF(151^4) has order 519885600. -/
theorem orderOf_gen_151_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_151_4 Hex.FpPoly.X) = 151 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_151_4

/-- The Conway generator of GF(157^1) has order 156. -/
theorem orderOf_gen_157_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_157_1 Hex.FpPoly.X) = 157 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_157_1

/-- The Conway generator of GF(157^2) has order 24648. -/
theorem orderOf_gen_157_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_157_2 Hex.FpPoly.X) = 157 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_157_2

/-- The Conway generator of GF(157^3) has order 3869892. -/
theorem orderOf_gen_157_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_157_3 Hex.FpPoly.X) = 157 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_157_3

/-- The Conway generator of GF(157^4) has order 607573200. -/
theorem orderOf_gen_157_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_157_4 Hex.FpPoly.X) = 157 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_157_4

/-- The Conway generator of GF(163^1) has order 162. -/
theorem orderOf_gen_163_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_163_1 Hex.FpPoly.X) = 163 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_163_1

/-- The Conway generator of GF(163^2) has order 26568. -/
theorem orderOf_gen_163_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_163_2 Hex.FpPoly.X) = 163 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_163_2

/-- The Conway generator of GF(163^3) has order 4330746. -/
theorem orderOf_gen_163_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_163_3 Hex.FpPoly.X) = 163 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_163_3

/-- The Conway generator of GF(163^4) has order 705911760. -/
theorem orderOf_gen_163_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_163_4 Hex.FpPoly.X) = 163 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_163_4

/-- The Conway generator of GF(167^1) has order 166. -/
theorem orderOf_gen_167_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_167_1 Hex.FpPoly.X) = 167 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_167_1

/-- The Conway generator of GF(167^2) has order 27888. -/
theorem orderOf_gen_167_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_167_2 Hex.FpPoly.X) = 167 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_167_2

/-- The Conway generator of GF(167^3) has order 4657462. -/
theorem orderOf_gen_167_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_167_3 Hex.FpPoly.X) = 167 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_167_3

/-- The Conway generator of GF(167^4) has order 777796320. -/
theorem orderOf_gen_167_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_167_4 Hex.FpPoly.X) = 167 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_167_4

/-- The Conway generator of GF(173^1) has order 172. -/
theorem orderOf_gen_173_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_173_1 Hex.FpPoly.X) = 173 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_173_1

/-- The Conway generator of GF(173^2) has order 29928. -/
theorem orderOf_gen_173_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_173_2 Hex.FpPoly.X) = 173 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_173_2

/-- The Conway generator of GF(173^3) has order 5177716. -/
theorem orderOf_gen_173_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_173_3 Hex.FpPoly.X) = 173 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_173_3

/-- The Conway generator of GF(173^4) has order 895745040. -/
theorem orderOf_gen_173_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_173_4 Hex.FpPoly.X) = 173 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_173_4

/-- The Conway generator of GF(179^1) has order 178. -/
theorem orderOf_gen_179_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_179_1 Hex.FpPoly.X) = 179 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_179_1

/-- The Conway generator of GF(179^2) has order 32040. -/
theorem orderOf_gen_179_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_179_2 Hex.FpPoly.X) = 179 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_179_2

/-- The Conway generator of GF(179^3) has order 5735338. -/
theorem orderOf_gen_179_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_179_3 Hex.FpPoly.X) = 179 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_179_3

/-- The Conway generator of GF(179^4) has order 1026625680. -/
theorem orderOf_gen_179_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_179_4 Hex.FpPoly.X) = 179 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_179_4

/-- The Conway generator of GF(181^1) has order 180. -/
theorem orderOf_gen_181_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_181_1 Hex.FpPoly.X) = 181 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_181_1

/-- The Conway generator of GF(181^2) has order 32760. -/
theorem orderOf_gen_181_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_181_2 Hex.FpPoly.X) = 181 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_181_2

/-- The Conway generator of GF(181^3) has order 5929740. -/
theorem orderOf_gen_181_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_181_3 Hex.FpPoly.X) = 181 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_181_3

/-- The Conway generator of GF(181^4) has order 1073283120. -/
theorem orderOf_gen_181_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_181_4 Hex.FpPoly.X) = 181 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_181_4

/-- The Conway generator of GF(191^1) has order 190. -/
theorem orderOf_gen_191_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_191_1 Hex.FpPoly.X) = 191 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_191_1

/-- The Conway generator of GF(191^2) has order 36480. -/
theorem orderOf_gen_191_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_191_2 Hex.FpPoly.X) = 191 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_191_2

/-- The Conway generator of GF(191^3) has order 6967870. -/
theorem orderOf_gen_191_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_191_3 Hex.FpPoly.X) = 191 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_191_3

/-- The Conway generator of GF(191^4) has order 1330863360. -/
theorem orderOf_gen_191_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_191_4 Hex.FpPoly.X) = 191 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_191_4

/-- The Conway generator of GF(193^1) has order 192. -/
theorem orderOf_gen_193_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_193_1 Hex.FpPoly.X) = 193 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_193_1

/-- The Conway generator of GF(193^2) has order 37248. -/
theorem orderOf_gen_193_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_193_2 Hex.FpPoly.X) = 193 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_193_2

/-- The Conway generator of GF(193^3) has order 7189056. -/
theorem orderOf_gen_193_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_193_3 Hex.FpPoly.X) = 193 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_193_3

/-- The Conway generator of GF(193^4) has order 1387488000. -/
theorem orderOf_gen_193_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_193_4 Hex.FpPoly.X) = 193 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_193_4

/-- The Conway generator of GF(197^1) has order 196. -/
theorem orderOf_gen_197_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_197_1 Hex.FpPoly.X) = 197 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_197_1

/-- The Conway generator of GF(197^2) has order 38808. -/
theorem orderOf_gen_197_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_197_2 Hex.FpPoly.X) = 197 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_197_2

/-- The Conway generator of GF(197^3) has order 7645372. -/
theorem orderOf_gen_197_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_197_3 Hex.FpPoly.X) = 197 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_197_3

/-- The Conway generator of GF(197^4) has order 1506138480. -/
theorem orderOf_gen_197_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_197_4 Hex.FpPoly.X) = 197 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_197_4

/-- The Conway generator of GF(199^1) has order 198. -/
theorem orderOf_gen_199_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_199_1 Hex.FpPoly.X) = 199 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_199_1

/-- The Conway generator of GF(199^2) has order 39600. -/
theorem orderOf_gen_199_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_199_2 Hex.FpPoly.X) = 199 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_199_2

/-- The Conway generator of GF(199^3) has order 7880598. -/
theorem orderOf_gen_199_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_199_3 Hex.FpPoly.X) = 199 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_199_3

/-- The Conway generator of GF(199^4) has order 1568239200. -/
theorem orderOf_gen_199_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_199_4 Hex.FpPoly.X) = 199 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_199_4

/-- The Conway generator of GF(211^1) has order 210. -/
theorem orderOf_gen_211_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_211_1 Hex.FpPoly.X) = 211 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_211_1

/-- The Conway generator of GF(211^2) has order 44520. -/
theorem orderOf_gen_211_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_211_2 Hex.FpPoly.X) = 211 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_211_2

/-- The Conway generator of GF(211^3) has order 9393930. -/
theorem orderOf_gen_211_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_211_3 Hex.FpPoly.X) = 211 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_211_3

/-- The Conway generator of GF(211^4) has order 1982119440. -/
theorem orderOf_gen_211_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_211_4 Hex.FpPoly.X) = 211 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_211_4

/-- The Conway generator of GF(223^1) has order 222. -/
theorem orderOf_gen_223_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_223_1 Hex.FpPoly.X) = 223 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_223_1

/-- The Conway generator of GF(223^2) has order 49728. -/
theorem orderOf_gen_223_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_223_2 Hex.FpPoly.X) = 223 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_223_2

/-- The Conway generator of GF(223^3) has order 11089566. -/
theorem orderOf_gen_223_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_223_3 Hex.FpPoly.X) = 223 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_223_3

/-- The Conway generator of GF(223^4) has order 2472973440. -/
theorem orderOf_gen_223_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_223_4 Hex.FpPoly.X) = 223 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_223_4

/-- The Conway generator of GF(227^1) has order 226. -/
theorem orderOf_gen_227_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_227_1 Hex.FpPoly.X) = 227 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_227_1

/-- The Conway generator of GF(227^2) has order 51528. -/
theorem orderOf_gen_227_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_227_2 Hex.FpPoly.X) = 227 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_227_2

/-- The Conway generator of GF(227^3) has order 11697082. -/
theorem orderOf_gen_227_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_227_3 Hex.FpPoly.X) = 227 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_227_3

/-- The Conway generator of GF(227^4) has order 2655237840. -/
theorem orderOf_gen_227_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_227_4 Hex.FpPoly.X) = 227 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_227_4

/-- The Conway generator of GF(229^1) has order 228. -/
theorem orderOf_gen_229_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_229_1 Hex.FpPoly.X) = 229 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_229_1

/-- The Conway generator of GF(229^2) has order 52440. -/
theorem orderOf_gen_229_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_229_2 Hex.FpPoly.X) = 229 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_229_2

/-- The Conway generator of GF(229^3) has order 12008988. -/
theorem orderOf_gen_229_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_229_3 Hex.FpPoly.X) = 229 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_229_3

/-- The Conway generator of GF(229^4) has order 2750058480. -/
theorem orderOf_gen_229_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_229_4 Hex.FpPoly.X) = 229 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_229_4

/-- The Conway generator of GF(233^1) has order 232. -/
theorem orderOf_gen_233_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_233_1 Hex.FpPoly.X) = 233 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_233_1

/-- The Conway generator of GF(233^2) has order 54288. -/
theorem orderOf_gen_233_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_233_2 Hex.FpPoly.X) = 233 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_233_2

/-- The Conway generator of GF(233^3) has order 12649336. -/
theorem orderOf_gen_233_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_233_3 Hex.FpPoly.X) = 233 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_233_3

/-- The Conway generator of GF(233^4) has order 2947295520. -/
theorem orderOf_gen_233_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_233_4 Hex.FpPoly.X) = 233 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_233_4

/-- The Conway generator of GF(239^1) has order 238. -/
theorem orderOf_gen_239_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_239_1 Hex.FpPoly.X) = 239 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_239_1

/-- The Conway generator of GF(239^2) has order 57120. -/
theorem orderOf_gen_239_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_239_2 Hex.FpPoly.X) = 239 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_239_2

/-- The Conway generator of GF(239^3) has order 13651918. -/
theorem orderOf_gen_239_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_239_3 Hex.FpPoly.X) = 239 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_239_3

/-- The Conway generator of GF(239^4) has order 3262808640. -/
theorem orderOf_gen_239_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_239_4 Hex.FpPoly.X) = 239 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_239_4

/-- The Conway generator of GF(241^1) has order 240. -/
theorem orderOf_gen_241_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_241_1 Hex.FpPoly.X) = 241 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_241_1

/-- The Conway generator of GF(241^2) has order 58080. -/
theorem orderOf_gen_241_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_241_2 Hex.FpPoly.X) = 241 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_241_2

/-- The Conway generator of GF(241^3) has order 13997520. -/
theorem orderOf_gen_241_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_241_3 Hex.FpPoly.X) = 241 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_241_3

/-- The Conway generator of GF(241^4) has order 3373402560. -/
theorem orderOf_gen_241_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_241_4 Hex.FpPoly.X) = 241 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_241_4

/-- The Conway generator of GF(251^1) has order 250. -/
theorem orderOf_gen_251_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_251_1 Hex.FpPoly.X) = 251 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_251_1

/-- The Conway generator of GF(251^2) has order 63000. -/
theorem orderOf_gen_251_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_251_2 Hex.FpPoly.X) = 251 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_251_2

/-- The Conway generator of GF(251^3) has order 15813250. -/
theorem orderOf_gen_251_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_251_3 Hex.FpPoly.X) = 251 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_251_3

/-- The Conway generator of GF(251^4) has order 3969126000. -/
theorem orderOf_gen_251_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_251_4 Hex.FpPoly.X) = 251 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_251_4

/-- The Conway generator of GF(257^1) has order 256. -/
theorem orderOf_gen_257_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_257_1 Hex.FpPoly.X) = 257 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_257_1

/-- The Conway generator of GF(257^2) has order 66048. -/
theorem orderOf_gen_257_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_257_2 Hex.FpPoly.X) = 257 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_257_2

/-- The Conway generator of GF(257^3) has order 16974592. -/
theorem orderOf_gen_257_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_257_3 Hex.FpPoly.X) = 257 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_257_3

/-- The Conway generator of GF(257^4) has order 4362470400. -/
theorem orderOf_gen_257_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_257_4 Hex.FpPoly.X) = 257 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_257_4

/-- The Conway generator of GF(263^1) has order 262. -/
theorem orderOf_gen_263_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_263_1 Hex.FpPoly.X) = 263 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_263_1

/-- The Conway generator of GF(263^2) has order 69168. -/
theorem orderOf_gen_263_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_263_2 Hex.FpPoly.X) = 263 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_263_2

/-- The Conway generator of GF(263^3) has order 18191446. -/
theorem orderOf_gen_263_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_263_3 Hex.FpPoly.X) = 263 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_263_3

/-- The Conway generator of GF(263^4) has order 4784350560. -/
theorem orderOf_gen_263_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_263_4 Hex.FpPoly.X) = 263 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_263_4

/-- The Conway generator of GF(269^1) has order 268. -/
theorem orderOf_gen_269_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_269_1 Hex.FpPoly.X) = 269 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_269_1

/-- The Conway generator of GF(269^2) has order 72360. -/
theorem orderOf_gen_269_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_269_2 Hex.FpPoly.X) = 269 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_269_2

/-- The Conway generator of GF(269^3) has order 19465108. -/
theorem orderOf_gen_269_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_269_3 Hex.FpPoly.X) = 269 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_269_3

/-- The Conway generator of GF(269^4) has order 5236114320. -/
theorem orderOf_gen_269_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_269_4 Hex.FpPoly.X) = 269 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_269_4

end HexGFqMathlib
