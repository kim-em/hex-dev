/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFq.Entry

public section

namespace Hex.GFq

/-- Instance-selected field for C(2, 1). -/
instance committedEntry_2_1 : CommittedEntry 2 1 where
  entry := Hex.Conway.supportedEntry_2_1

/-- Instance-selected field for C(2, 2). -/
instance committedEntry_2_2 : CommittedEntry 2 2 where
  entry := Hex.Conway.supportedEntry_2_2

/-- Instance-selected field for C(2, 3). -/
instance committedEntry_2_3 : CommittedEntry 2 3 where
  entry := Hex.Conway.supportedEntry_2_3

/-- Instance-selected field for C(2, 4). -/
instance committedEntry_2_4 : CommittedEntry 2 4 where
  entry := Hex.Conway.supportedEntry_2_4

/-- Instance-selected field for C(2, 5). -/
instance committedEntry_2_5 : CommittedEntry 2 5 where
  entry := Hex.Conway.supportedEntry_2_5

/-- Instance-selected field for C(2, 6). -/
instance committedEntry_2_6 : CommittedEntry 2 6 where
  entry := Hex.Conway.supportedEntry_2_6

/-- Instance-selected field for C(2, 7). -/
instance committedEntry_2_7 : CommittedEntry 2 7 where
  entry := Hex.Conway.supportedEntry_2_7

/-- Instance-selected field for C(2, 8). -/
instance committedEntry_2_8 : CommittedEntry 2 8 where
  entry := Hex.Conway.supportedEntry_2_8

/-- Instance-selected field for C(2, 9). -/
instance committedEntry_2_9 : CommittedEntry 2 9 where
  entry := Hex.Conway.supportedEntry_2_9

/-- Instance-selected field for C(2, 10). -/
instance committedEntry_2_10 : CommittedEntry 2 10 where
  entry := Hex.Conway.supportedEntry_2_10

/-- Instance-selected field for C(2, 11). -/
instance committedEntry_2_11 : CommittedEntry 2 11 where
  entry := Hex.Conway.supportedEntry_2_11

/-- Instance-selected field for C(2, 12). -/
instance committedEntry_2_12 : CommittedEntry 2 12 where
  entry := Hex.Conway.supportedEntry_2_12

/-- Instance-selected field for C(2, 13). -/
instance committedEntry_2_13 : CommittedEntry 2 13 where
  entry := Hex.Conway.supportedEntry_2_13

/-- Instance-selected field for C(2, 14). -/
instance committedEntry_2_14 : CommittedEntry 2 14 where
  entry := Hex.Conway.supportedEntry_2_14

/-- Instance-selected field for C(2, 15). -/
instance committedEntry_2_15 : CommittedEntry 2 15 where
  entry := Hex.Conway.supportedEntry_2_15

/-- Instance-selected field for C(2, 16). -/
instance committedEntry_2_16 : CommittedEntry 2 16 where
  entry := Hex.Conway.supportedEntry_2_16

/-- Instance-selected field for C(3, 1). -/
instance committedEntry_3_1 : CommittedEntry 3 1 where
  entry := Hex.Conway.supportedEntry_3_1

/-- Instance-selected field for C(3, 2). -/
instance committedEntry_3_2 : CommittedEntry 3 2 where
  entry := Hex.Conway.supportedEntry_3_2

/-- Instance-selected field for C(3, 3). -/
instance committedEntry_3_3 : CommittedEntry 3 3 where
  entry := Hex.Conway.supportedEntry_3_3

/-- Instance-selected field for C(3, 4). -/
instance committedEntry_3_4 : CommittedEntry 3 4 where
  entry := Hex.Conway.supportedEntry_3_4

/-- Instance-selected field for C(3, 5). -/
instance committedEntry_3_5 : CommittedEntry 3 5 where
  entry := Hex.Conway.supportedEntry_3_5

/-- Instance-selected field for C(3, 6). -/
instance committedEntry_3_6 : CommittedEntry 3 6 where
  entry := Hex.Conway.supportedEntry_3_6

/-- Instance-selected field for C(3, 7). -/
instance committedEntry_3_7 : CommittedEntry 3 7 where
  entry := Hex.Conway.supportedEntry_3_7

/-- Instance-selected field for C(3, 8). -/
instance committedEntry_3_8 : CommittedEntry 3 8 where
  entry := Hex.Conway.supportedEntry_3_8

/-- Instance-selected field for C(5, 1). -/
instance committedEntry_5_1 : CommittedEntry 5 1 where
  entry := Hex.Conway.supportedEntry_5_1

/-- Instance-selected field for C(5, 2). -/
instance committedEntry_5_2 : CommittedEntry 5 2 where
  entry := Hex.Conway.supportedEntry_5_2

/-- Instance-selected field for C(5, 3). -/
instance committedEntry_5_3 : CommittedEntry 5 3 where
  entry := Hex.Conway.supportedEntry_5_3

/-- Instance-selected field for C(5, 4). -/
instance committedEntry_5_4 : CommittedEntry 5 4 where
  entry := Hex.Conway.supportedEntry_5_4

/-- Instance-selected field for C(5, 5). -/
instance committedEntry_5_5 : CommittedEntry 5 5 where
  entry := Hex.Conway.supportedEntry_5_5

/-- Instance-selected field for C(5, 6). -/
instance committedEntry_5_6 : CommittedEntry 5 6 where
  entry := Hex.Conway.supportedEntry_5_6

/-- Instance-selected field for C(5, 7). -/
instance committedEntry_5_7 : CommittedEntry 5 7 where
  entry := Hex.Conway.supportedEntry_5_7

/-- Instance-selected field for C(5, 8). -/
instance committedEntry_5_8 : CommittedEntry 5 8 where
  entry := Hex.Conway.supportedEntry_5_8

/-- Instance-selected field for C(7, 1). -/
instance committedEntry_7_1 : CommittedEntry 7 1 where
  entry := Hex.Conway.supportedEntry_7_1

/-- Instance-selected field for C(7, 2). -/
instance committedEntry_7_2 : CommittedEntry 7 2 where
  entry := Hex.Conway.supportedEntry_7_2

/-- Instance-selected field for C(7, 3). -/
instance committedEntry_7_3 : CommittedEntry 7 3 where
  entry := Hex.Conway.supportedEntry_7_3

/-- Instance-selected field for C(7, 4). -/
instance committedEntry_7_4 : CommittedEntry 7 4 where
  entry := Hex.Conway.supportedEntry_7_4

/-- Instance-selected field for C(7, 5). -/
instance committedEntry_7_5 : CommittedEntry 7 5 where
  entry := Hex.Conway.supportedEntry_7_5

/-- Instance-selected field for C(7, 6). -/
instance committedEntry_7_6 : CommittedEntry 7 6 where
  entry := Hex.Conway.supportedEntry_7_6

/-- Instance-selected field for C(7, 7). -/
instance committedEntry_7_7 : CommittedEntry 7 7 where
  entry := Hex.Conway.supportedEntry_7_7

/-- Instance-selected field for C(7, 8). -/
instance committedEntry_7_8 : CommittedEntry 7 8 where
  entry := Hex.Conway.supportedEntry_7_8

/-- Instance-selected field for C(11, 1). -/
instance committedEntry_11_1 : CommittedEntry 11 1 where
  entry := Hex.Conway.supportedEntry_11_1

/-- Instance-selected field for C(11, 2). -/
instance committedEntry_11_2 : CommittedEntry 11 2 where
  entry := Hex.Conway.supportedEntry_11_2

/-- Instance-selected field for C(11, 3). -/
instance committedEntry_11_3 : CommittedEntry 11 3 where
  entry := Hex.Conway.supportedEntry_11_3

/-- Instance-selected field for C(11, 4). -/
instance committedEntry_11_4 : CommittedEntry 11 4 where
  entry := Hex.Conway.supportedEntry_11_4

/-- Instance-selected field for C(11, 5). -/
instance committedEntry_11_5 : CommittedEntry 11 5 where
  entry := Hex.Conway.supportedEntry_11_5

/-- Instance-selected field for C(11, 6). -/
instance committedEntry_11_6 : CommittedEntry 11 6 where
  entry := Hex.Conway.supportedEntry_11_6

/-- Instance-selected field for C(13, 1). -/
instance committedEntry_13_1 : CommittedEntry 13 1 where
  entry := Hex.Conway.supportedEntry_13_1

/-- Instance-selected field for C(13, 2). -/
instance committedEntry_13_2 : CommittedEntry 13 2 where
  entry := Hex.Conway.supportedEntry_13_2

/-- Instance-selected field for C(13, 3). -/
instance committedEntry_13_3 : CommittedEntry 13 3 where
  entry := Hex.Conway.supportedEntry_13_3

/-- Instance-selected field for C(13, 4). -/
instance committedEntry_13_4 : CommittedEntry 13 4 where
  entry := Hex.Conway.supportedEntry_13_4

/-- Instance-selected field for C(13, 5). -/
instance committedEntry_13_5 : CommittedEntry 13 5 where
  entry := Hex.Conway.supportedEntry_13_5

/-- Instance-selected field for C(13, 6). -/
instance committedEntry_13_6 : CommittedEntry 13 6 where
  entry := Hex.Conway.supportedEntry_13_6

/-- Instance-selected field for C(17, 1). -/
instance committedEntry_17_1 : CommittedEntry 17 1 where
  entry := Hex.Conway.supportedEntry_17_1

/-- Instance-selected field for C(17, 2). -/
instance committedEntry_17_2 : CommittedEntry 17 2 where
  entry := Hex.Conway.supportedEntry_17_2

/-- Instance-selected field for C(17, 3). -/
instance committedEntry_17_3 : CommittedEntry 17 3 where
  entry := Hex.Conway.supportedEntry_17_3

/-- Instance-selected field for C(17, 4). -/
instance committedEntry_17_4 : CommittedEntry 17 4 where
  entry := Hex.Conway.supportedEntry_17_4

/-- Instance-selected field for C(19, 1). -/
instance committedEntry_19_1 : CommittedEntry 19 1 where
  entry := Hex.Conway.supportedEntry_19_1

/-- Instance-selected field for C(19, 2). -/
instance committedEntry_19_2 : CommittedEntry 19 2 where
  entry := Hex.Conway.supportedEntry_19_2

/-- Instance-selected field for C(19, 3). -/
instance committedEntry_19_3 : CommittedEntry 19 3 where
  entry := Hex.Conway.supportedEntry_19_3

/-- Instance-selected field for C(19, 4). -/
instance committedEntry_19_4 : CommittedEntry 19 4 where
  entry := Hex.Conway.supportedEntry_19_4

/-- Instance-selected field for C(23, 1). -/
instance committedEntry_23_1 : CommittedEntry 23 1 where
  entry := Hex.Conway.supportedEntry_23_1

/-- Instance-selected field for C(23, 2). -/
instance committedEntry_23_2 : CommittedEntry 23 2 where
  entry := Hex.Conway.supportedEntry_23_2

/-- Instance-selected field for C(23, 3). -/
instance committedEntry_23_3 : CommittedEntry 23 3 where
  entry := Hex.Conway.supportedEntry_23_3

/-- Instance-selected field for C(23, 4). -/
instance committedEntry_23_4 : CommittedEntry 23 4 where
  entry := Hex.Conway.supportedEntry_23_4

/-- Instance-selected field for C(29, 1). -/
instance committedEntry_29_1 : CommittedEntry 29 1 where
  entry := Hex.Conway.supportedEntry_29_1

/-- Instance-selected field for C(29, 2). -/
instance committedEntry_29_2 : CommittedEntry 29 2 where
  entry := Hex.Conway.supportedEntry_29_2

/-- Instance-selected field for C(29, 3). -/
instance committedEntry_29_3 : CommittedEntry 29 3 where
  entry := Hex.Conway.supportedEntry_29_3

/-- Instance-selected field for C(29, 4). -/
instance committedEntry_29_4 : CommittedEntry 29 4 where
  entry := Hex.Conway.supportedEntry_29_4

/-- Instance-selected field for C(31, 1). -/
instance committedEntry_31_1 : CommittedEntry 31 1 where
  entry := Hex.Conway.supportedEntry_31_1

/-- Instance-selected field for C(31, 2). -/
instance committedEntry_31_2 : CommittedEntry 31 2 where
  entry := Hex.Conway.supportedEntry_31_2

/-- Instance-selected field for C(31, 3). -/
instance committedEntry_31_3 : CommittedEntry 31 3 where
  entry := Hex.Conway.supportedEntry_31_3

/-- Instance-selected field for C(31, 4). -/
instance committedEntry_31_4 : CommittedEntry 31 4 where
  entry := Hex.Conway.supportedEntry_31_4

/-- Instance-selected field for C(37, 1). -/
instance committedEntry_37_1 : CommittedEntry 37 1 where
  entry := Hex.Conway.supportedEntry_37_1

/-- Instance-selected field for C(37, 2). -/
instance committedEntry_37_2 : CommittedEntry 37 2 where
  entry := Hex.Conway.supportedEntry_37_2

/-- Instance-selected field for C(37, 3). -/
instance committedEntry_37_3 : CommittedEntry 37 3 where
  entry := Hex.Conway.supportedEntry_37_3

/-- Instance-selected field for C(37, 4). -/
instance committedEntry_37_4 : CommittedEntry 37 4 where
  entry := Hex.Conway.supportedEntry_37_4

/-- Instance-selected field for C(41, 1). -/
instance committedEntry_41_1 : CommittedEntry 41 1 where
  entry := Hex.Conway.supportedEntry_41_1

/-- Instance-selected field for C(41, 2). -/
instance committedEntry_41_2 : CommittedEntry 41 2 where
  entry := Hex.Conway.supportedEntry_41_2

/-- Instance-selected field for C(41, 3). -/
instance committedEntry_41_3 : CommittedEntry 41 3 where
  entry := Hex.Conway.supportedEntry_41_3

/-- Instance-selected field for C(41, 4). -/
instance committedEntry_41_4 : CommittedEntry 41 4 where
  entry := Hex.Conway.supportedEntry_41_4

/-- Instance-selected field for C(43, 1). -/
instance committedEntry_43_1 : CommittedEntry 43 1 where
  entry := Hex.Conway.supportedEntry_43_1

/-- Instance-selected field for C(43, 2). -/
instance committedEntry_43_2 : CommittedEntry 43 2 where
  entry := Hex.Conway.supportedEntry_43_2

/-- Instance-selected field for C(43, 3). -/
instance committedEntry_43_3 : CommittedEntry 43 3 where
  entry := Hex.Conway.supportedEntry_43_3

/-- Instance-selected field for C(43, 4). -/
instance committedEntry_43_4 : CommittedEntry 43 4 where
  entry := Hex.Conway.supportedEntry_43_4

/-- Instance-selected field for C(47, 1). -/
instance committedEntry_47_1 : CommittedEntry 47 1 where
  entry := Hex.Conway.supportedEntry_47_1

/-- Instance-selected field for C(47, 2). -/
instance committedEntry_47_2 : CommittedEntry 47 2 where
  entry := Hex.Conway.supportedEntry_47_2

/-- Instance-selected field for C(47, 3). -/
instance committedEntry_47_3 : CommittedEntry 47 3 where
  entry := Hex.Conway.supportedEntry_47_3

/-- Instance-selected field for C(47, 4). -/
instance committedEntry_47_4 : CommittedEntry 47 4 where
  entry := Hex.Conway.supportedEntry_47_4

/-- Instance-selected field for C(53, 1). -/
instance committedEntry_53_1 : CommittedEntry 53 1 where
  entry := Hex.Conway.supportedEntry_53_1

/-- Instance-selected field for C(53, 2). -/
instance committedEntry_53_2 : CommittedEntry 53 2 where
  entry := Hex.Conway.supportedEntry_53_2

/-- Instance-selected field for C(53, 3). -/
instance committedEntry_53_3 : CommittedEntry 53 3 where
  entry := Hex.Conway.supportedEntry_53_3

/-- Instance-selected field for C(53, 4). -/
instance committedEntry_53_4 : CommittedEntry 53 4 where
  entry := Hex.Conway.supportedEntry_53_4

/-- Instance-selected field for C(59, 1). -/
instance committedEntry_59_1 : CommittedEntry 59 1 where
  entry := Hex.Conway.supportedEntry_59_1

/-- Instance-selected field for C(59, 2). -/
instance committedEntry_59_2 : CommittedEntry 59 2 where
  entry := Hex.Conway.supportedEntry_59_2

/-- Instance-selected field for C(59, 3). -/
instance committedEntry_59_3 : CommittedEntry 59 3 where
  entry := Hex.Conway.supportedEntry_59_3

/-- Instance-selected field for C(59, 4). -/
instance committedEntry_59_4 : CommittedEntry 59 4 where
  entry := Hex.Conway.supportedEntry_59_4

/-- Instance-selected field for C(61, 1). -/
instance committedEntry_61_1 : CommittedEntry 61 1 where
  entry := Hex.Conway.supportedEntry_61_1

/-- Instance-selected field for C(61, 2). -/
instance committedEntry_61_2 : CommittedEntry 61 2 where
  entry := Hex.Conway.supportedEntry_61_2

/-- Instance-selected field for C(61, 3). -/
instance committedEntry_61_3 : CommittedEntry 61 3 where
  entry := Hex.Conway.supportedEntry_61_3

/-- Instance-selected field for C(61, 4). -/
instance committedEntry_61_4 : CommittedEntry 61 4 where
  entry := Hex.Conway.supportedEntry_61_4

/-- Instance-selected field for C(67, 1). -/
instance committedEntry_67_1 : CommittedEntry 67 1 where
  entry := Hex.Conway.supportedEntry_67_1

/-- Instance-selected field for C(67, 2). -/
instance committedEntry_67_2 : CommittedEntry 67 2 where
  entry := Hex.Conway.supportedEntry_67_2

/-- Instance-selected field for C(67, 3). -/
instance committedEntry_67_3 : CommittedEntry 67 3 where
  entry := Hex.Conway.supportedEntry_67_3

/-- Instance-selected field for C(67, 4). -/
instance committedEntry_67_4 : CommittedEntry 67 4 where
  entry := Hex.Conway.supportedEntry_67_4

/-- Instance-selected field for C(71, 1). -/
instance committedEntry_71_1 : CommittedEntry 71 1 where
  entry := Hex.Conway.supportedEntry_71_1

/-- Instance-selected field for C(71, 2). -/
instance committedEntry_71_2 : CommittedEntry 71 2 where
  entry := Hex.Conway.supportedEntry_71_2

/-- Instance-selected field for C(71, 3). -/
instance committedEntry_71_3 : CommittedEntry 71 3 where
  entry := Hex.Conway.supportedEntry_71_3

/-- Instance-selected field for C(71, 4). -/
instance committedEntry_71_4 : CommittedEntry 71 4 where
  entry := Hex.Conway.supportedEntry_71_4

/-- Instance-selected field for C(73, 1). -/
instance committedEntry_73_1 : CommittedEntry 73 1 where
  entry := Hex.Conway.supportedEntry_73_1

/-- Instance-selected field for C(73, 2). -/
instance committedEntry_73_2 : CommittedEntry 73 2 where
  entry := Hex.Conway.supportedEntry_73_2

/-- Instance-selected field for C(73, 3). -/
instance committedEntry_73_3 : CommittedEntry 73 3 where
  entry := Hex.Conway.supportedEntry_73_3

/-- Instance-selected field for C(73, 4). -/
instance committedEntry_73_4 : CommittedEntry 73 4 where
  entry := Hex.Conway.supportedEntry_73_4

/-- Instance-selected field for C(79, 1). -/
instance committedEntry_79_1 : CommittedEntry 79 1 where
  entry := Hex.Conway.supportedEntry_79_1

/-- Instance-selected field for C(79, 2). -/
instance committedEntry_79_2 : CommittedEntry 79 2 where
  entry := Hex.Conway.supportedEntry_79_2

/-- Instance-selected field for C(79, 3). -/
instance committedEntry_79_3 : CommittedEntry 79 3 where
  entry := Hex.Conway.supportedEntry_79_3

/-- Instance-selected field for C(79, 4). -/
instance committedEntry_79_4 : CommittedEntry 79 4 where
  entry := Hex.Conway.supportedEntry_79_4

/-- Instance-selected field for C(83, 1). -/
instance committedEntry_83_1 : CommittedEntry 83 1 where
  entry := Hex.Conway.supportedEntry_83_1

/-- Instance-selected field for C(83, 2). -/
instance committedEntry_83_2 : CommittedEntry 83 2 where
  entry := Hex.Conway.supportedEntry_83_2

/-- Instance-selected field for C(83, 3). -/
instance committedEntry_83_3 : CommittedEntry 83 3 where
  entry := Hex.Conway.supportedEntry_83_3

/-- Instance-selected field for C(83, 4). -/
instance committedEntry_83_4 : CommittedEntry 83 4 where
  entry := Hex.Conway.supportedEntry_83_4

/-- Instance-selected field for C(89, 1). -/
instance committedEntry_89_1 : CommittedEntry 89 1 where
  entry := Hex.Conway.supportedEntry_89_1

/-- Instance-selected field for C(89, 2). -/
instance committedEntry_89_2 : CommittedEntry 89 2 where
  entry := Hex.Conway.supportedEntry_89_2

/-- Instance-selected field for C(89, 3). -/
instance committedEntry_89_3 : CommittedEntry 89 3 where
  entry := Hex.Conway.supportedEntry_89_3

/-- Instance-selected field for C(89, 4). -/
instance committedEntry_89_4 : CommittedEntry 89 4 where
  entry := Hex.Conway.supportedEntry_89_4

/-- Instance-selected field for C(97, 1). -/
instance committedEntry_97_1 : CommittedEntry 97 1 where
  entry := Hex.Conway.supportedEntry_97_1

/-- Instance-selected field for C(97, 2). -/
instance committedEntry_97_2 : CommittedEntry 97 2 where
  entry := Hex.Conway.supportedEntry_97_2

/-- Instance-selected field for C(97, 3). -/
instance committedEntry_97_3 : CommittedEntry 97 3 where
  entry := Hex.Conway.supportedEntry_97_3

/-- Instance-selected field for C(97, 4). -/
instance committedEntry_97_4 : CommittedEntry 97 4 where
  entry := Hex.Conway.supportedEntry_97_4

end Hex.GFq
