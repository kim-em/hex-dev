/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.PrimitivityCore

public section

namespace HexGFqMathlib

/-- The Conway generator of GF(811^3) has order 533411730. -/
theorem orderOf_gen_811_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_811_3 Hex.FpPoly.X) = 811 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_811_3

/-- The Conway generator of GF(821^1) has order 820. -/
theorem orderOf_gen_821_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_1 Hex.FpPoly.X) = 821 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_1

/-- The Conway generator of GF(821^2) has order 674040. -/
theorem orderOf_gen_821_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_2 Hex.FpPoly.X) = 821 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_2

/-- The Conway generator of GF(821^3) has order 553387660. -/
theorem orderOf_gen_821_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_821_3 Hex.FpPoly.X) = 821 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_821_3

/-- The Conway generator of GF(823^1) has order 822. -/
theorem orderOf_gen_823_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_1 Hex.FpPoly.X) = 823 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_1

/-- The Conway generator of GF(823^2) has order 677328. -/
theorem orderOf_gen_823_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_2 Hex.FpPoly.X) = 823 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_2

/-- The Conway generator of GF(823^3) has order 557441766. -/
theorem orderOf_gen_823_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_823_3 Hex.FpPoly.X) = 823 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_823_3

/-- The Conway generator of GF(827^1) has order 826. -/
theorem orderOf_gen_827_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_1 Hex.FpPoly.X) = 827 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_1

/-- The Conway generator of GF(827^2) has order 683928. -/
theorem orderOf_gen_827_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_2 Hex.FpPoly.X) = 827 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_2

/-- The Conway generator of GF(827^3) has order 565609282. -/
theorem orderOf_gen_827_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_827_3 Hex.FpPoly.X) = 827 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_827_3

/-- The Conway generator of GF(829^1) has order 828. -/
theorem orderOf_gen_829_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_1 Hex.FpPoly.X) = 829 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_1

/-- The Conway generator of GF(829^2) has order 687240. -/
theorem orderOf_gen_829_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_2 Hex.FpPoly.X) = 829 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_2

/-- The Conway generator of GF(829^3) has order 569722788. -/
theorem orderOf_gen_829_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_829_3 Hex.FpPoly.X) = 829 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_829_3

/-- The Conway generator of GF(839^1) has order 838. -/
theorem orderOf_gen_839_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_1 Hex.FpPoly.X) = 839 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_1

/-- The Conway generator of GF(839^2) has order 703920. -/
theorem orderOf_gen_839_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_2 Hex.FpPoly.X) = 839 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_2

/-- The Conway generator of GF(839^3) has order 590589718. -/
theorem orderOf_gen_839_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_839_3 Hex.FpPoly.X) = 839 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_839_3

/-- The Conway generator of GF(853^1) has order 852. -/
theorem orderOf_gen_853_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_1 Hex.FpPoly.X) = 853 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_1

/-- The Conway generator of GF(853^2) has order 727608. -/
theorem orderOf_gen_853_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_2 Hex.FpPoly.X) = 853 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_2

/-- The Conway generator of GF(853^3) has order 620650476. -/
theorem orderOf_gen_853_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_853_3 Hex.FpPoly.X) = 853 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_853_3

/-- The Conway generator of GF(857^1) has order 856. -/
theorem orderOf_gen_857_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_1 Hex.FpPoly.X) = 857 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_1

/-- The Conway generator of GF(857^2) has order 734448. -/
theorem orderOf_gen_857_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_2 Hex.FpPoly.X) = 857 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_2

/-- The Conway generator of GF(857^3) has order 629422792. -/
theorem orderOf_gen_857_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_857_3 Hex.FpPoly.X) = 857 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_857_3

/-- The Conway generator of GF(859^1) has order 858. -/
theorem orderOf_gen_859_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_1 Hex.FpPoly.X) = 859 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_1

/-- The Conway generator of GF(859^2) has order 737880. -/
theorem orderOf_gen_859_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_2 Hex.FpPoly.X) = 859 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_2

/-- The Conway generator of GF(859^3) has order 633839778. -/
theorem orderOf_gen_859_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_859_3 Hex.FpPoly.X) = 859 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_859_3

/-- The Conway generator of GF(863^1) has order 862. -/
theorem orderOf_gen_863_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_1 Hex.FpPoly.X) = 863 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_1

/-- The Conway generator of GF(863^2) has order 744768. -/
theorem orderOf_gen_863_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_2 Hex.FpPoly.X) = 863 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_2

/-- The Conway generator of GF(863^3) has order 642735646. -/
theorem orderOf_gen_863_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_863_3 Hex.FpPoly.X) = 863 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_863_3

/-- The Conway generator of GF(877^1) has order 876. -/
theorem orderOf_gen_877_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_1 Hex.FpPoly.X) = 877 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_1

/-- The Conway generator of GF(877^2) has order 769128. -/
theorem orderOf_gen_877_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_2 Hex.FpPoly.X) = 877 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_2

/-- The Conway generator of GF(877^3) has order 674526132. -/
theorem orderOf_gen_877_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_877_3 Hex.FpPoly.X) = 877 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_877_3

/-- The Conway generator of GF(881^1) has order 880. -/
theorem orderOf_gen_881_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_1 Hex.FpPoly.X) = 881 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_1

/-- The Conway generator of GF(881^2) has order 776160. -/
theorem orderOf_gen_881_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_2 Hex.FpPoly.X) = 881 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_2

/-- The Conway generator of GF(881^3) has order 683797840. -/
theorem orderOf_gen_881_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_881_3 Hex.FpPoly.X) = 881 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_881_3

/-- The Conway generator of GF(883^1) has order 882. -/
theorem orderOf_gen_883_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_1 Hex.FpPoly.X) = 883 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_1

/-- The Conway generator of GF(883^2) has order 779688. -/
theorem orderOf_gen_883_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_2 Hex.FpPoly.X) = 883 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_2

/-- The Conway generator of GF(883^3) has order 688465386. -/
theorem orderOf_gen_883_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_883_3 Hex.FpPoly.X) = 883 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_883_3

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

end HexGFqMathlib
