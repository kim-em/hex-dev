/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(739^1) into GF(739^2). -/
noncomputable def embed_739_1_2 :
    Hex.GFq 739 1 Hex.Conway.supportedEntry_739_1 →+*
      Hex.GFq 739 2 Hex.Conway.supportedEntry_739_2 :=
  conwayEmbed 739 1 2 _ _ Hex.Conway.compat_739_1_2

/-- The canonical embedding of GF(739^1) into GF(739^3). -/
noncomputable def embed_739_1_3 :
    Hex.GFq 739 1 Hex.Conway.supportedEntry_739_1 →+*
      Hex.GFq 739 3 Hex.Conway.supportedEntry_739_3 :=
  conwayEmbed 739 1 3 _ _ Hex.Conway.compat_739_1_3

/-- The canonical embedding of GF(743^1) into GF(743^2). -/
noncomputable def embed_743_1_2 :
    Hex.GFq 743 1 Hex.Conway.supportedEntry_743_1 →+*
      Hex.GFq 743 2 Hex.Conway.supportedEntry_743_2 :=
  conwayEmbed 743 1 2 _ _ Hex.Conway.compat_743_1_2

/-- The canonical embedding of GF(743^1) into GF(743^3). -/
noncomputable def embed_743_1_3 :
    Hex.GFq 743 1 Hex.Conway.supportedEntry_743_1 →+*
      Hex.GFq 743 3 Hex.Conway.supportedEntry_743_3 :=
  conwayEmbed 743 1 3 _ _ Hex.Conway.compat_743_1_3

/-- The canonical embedding of GF(751^1) into GF(751^2). -/
noncomputable def embed_751_1_2 :
    Hex.GFq 751 1 Hex.Conway.supportedEntry_751_1 →+*
      Hex.GFq 751 2 Hex.Conway.supportedEntry_751_2 :=
  conwayEmbed 751 1 2 _ _ Hex.Conway.compat_751_1_2

/-- The canonical embedding of GF(751^1) into GF(751^3). -/
noncomputable def embed_751_1_3 :
    Hex.GFq 751 1 Hex.Conway.supportedEntry_751_1 →+*
      Hex.GFq 751 3 Hex.Conway.supportedEntry_751_3 :=
  conwayEmbed 751 1 3 _ _ Hex.Conway.compat_751_1_3

/-- The canonical embedding of GF(757^1) into GF(757^2). -/
noncomputable def embed_757_1_2 :
    Hex.GFq 757 1 Hex.Conway.supportedEntry_757_1 →+*
      Hex.GFq 757 2 Hex.Conway.supportedEntry_757_2 :=
  conwayEmbed 757 1 2 _ _ Hex.Conway.compat_757_1_2

/-- The canonical embedding of GF(757^1) into GF(757^3). -/
noncomputable def embed_757_1_3 :
    Hex.GFq 757 1 Hex.Conway.supportedEntry_757_1 →+*
      Hex.GFq 757 3 Hex.Conway.supportedEntry_757_3 :=
  conwayEmbed 757 1 3 _ _ Hex.Conway.compat_757_1_3

/-- The canonical embedding of GF(761^1) into GF(761^2). -/
noncomputable def embed_761_1_2 :
    Hex.GFq 761 1 Hex.Conway.supportedEntry_761_1 →+*
      Hex.GFq 761 2 Hex.Conway.supportedEntry_761_2 :=
  conwayEmbed 761 1 2 _ _ Hex.Conway.compat_761_1_2

/-- The canonical embedding of GF(761^1) into GF(761^3). -/
noncomputable def embed_761_1_3 :
    Hex.GFq 761 1 Hex.Conway.supportedEntry_761_1 →+*
      Hex.GFq 761 3 Hex.Conway.supportedEntry_761_3 :=
  conwayEmbed 761 1 3 _ _ Hex.Conway.compat_761_1_3

/-- The canonical embedding of GF(769^1) into GF(769^2). -/
noncomputable def embed_769_1_2 :
    Hex.GFq 769 1 Hex.Conway.supportedEntry_769_1 →+*
      Hex.GFq 769 2 Hex.Conway.supportedEntry_769_2 :=
  conwayEmbed 769 1 2 _ _ Hex.Conway.compat_769_1_2

/-- The canonical embedding of GF(769^1) into GF(769^3). -/
noncomputable def embed_769_1_3 :
    Hex.GFq 769 1 Hex.Conway.supportedEntry_769_1 →+*
      Hex.GFq 769 3 Hex.Conway.supportedEntry_769_3 :=
  conwayEmbed 769 1 3 _ _ Hex.Conway.compat_769_1_3

/-- The canonical embedding of GF(773^1) into GF(773^2). -/
noncomputable def embed_773_1_2 :
    Hex.GFq 773 1 Hex.Conway.supportedEntry_773_1 →+*
      Hex.GFq 773 2 Hex.Conway.supportedEntry_773_2 :=
  conwayEmbed 773 1 2 _ _ Hex.Conway.compat_773_1_2

/-- The canonical embedding of GF(773^1) into GF(773^3). -/
noncomputable def embed_773_1_3 :
    Hex.GFq 773 1 Hex.Conway.supportedEntry_773_1 →+*
      Hex.GFq 773 3 Hex.Conway.supportedEntry_773_3 :=
  conwayEmbed 773 1 3 _ _ Hex.Conway.compat_773_1_3

/-- The canonical embedding of GF(787^1) into GF(787^2). -/
noncomputable def embed_787_1_2 :
    Hex.GFq 787 1 Hex.Conway.supportedEntry_787_1 →+*
      Hex.GFq 787 2 Hex.Conway.supportedEntry_787_2 :=
  conwayEmbed 787 1 2 _ _ Hex.Conway.compat_787_1_2

/-- The canonical embedding of GF(787^1) into GF(787^3). -/
noncomputable def embed_787_1_3 :
    Hex.GFq 787 1 Hex.Conway.supportedEntry_787_1 →+*
      Hex.GFq 787 3 Hex.Conway.supportedEntry_787_3 :=
  conwayEmbed 787 1 3 _ _ Hex.Conway.compat_787_1_3

/-- The canonical embedding of GF(797^1) into GF(797^2). -/
noncomputable def embed_797_1_2 :
    Hex.GFq 797 1 Hex.Conway.supportedEntry_797_1 →+*
      Hex.GFq 797 2 Hex.Conway.supportedEntry_797_2 :=
  conwayEmbed 797 1 2 _ _ Hex.Conway.compat_797_1_2

/-- The canonical embedding of GF(797^1) into GF(797^3). -/
noncomputable def embed_797_1_3 :
    Hex.GFq 797 1 Hex.Conway.supportedEntry_797_1 →+*
      Hex.GFq 797 3 Hex.Conway.supportedEntry_797_3 :=
  conwayEmbed 797 1 3 _ _ Hex.Conway.compat_797_1_3

/-- The canonical embedding of GF(809^1) into GF(809^2). -/
noncomputable def embed_809_1_2 :
    Hex.GFq 809 1 Hex.Conway.supportedEntry_809_1 →+*
      Hex.GFq 809 2 Hex.Conway.supportedEntry_809_2 :=
  conwayEmbed 809 1 2 _ _ Hex.Conway.compat_809_1_2

/-- The canonical embedding of GF(809^1) into GF(809^3). -/
noncomputable def embed_809_1_3 :
    Hex.GFq 809 1 Hex.Conway.supportedEntry_809_1 →+*
      Hex.GFq 809 3 Hex.Conway.supportedEntry_809_3 :=
  conwayEmbed 809 1 3 _ _ Hex.Conway.compat_809_1_3

/-- The canonical embedding of GF(811^1) into GF(811^2). -/
noncomputable def embed_811_1_2 :
    Hex.GFq 811 1 Hex.Conway.supportedEntry_811_1 →+*
      Hex.GFq 811 2 Hex.Conway.supportedEntry_811_2 :=
  conwayEmbed 811 1 2 _ _ Hex.Conway.compat_811_1_2

/-- The canonical embedding of GF(811^1) into GF(811^3). -/
noncomputable def embed_811_1_3 :
    Hex.GFq 811 1 Hex.Conway.supportedEntry_811_1 →+*
      Hex.GFq 811 3 Hex.Conway.supportedEntry_811_3 :=
  conwayEmbed 811 1 3 _ _ Hex.Conway.compat_811_1_3

/-- The canonical embedding of GF(821^1) into GF(821^2). -/
noncomputable def embed_821_1_2 :
    Hex.GFq 821 1 Hex.Conway.supportedEntry_821_1 →+*
      Hex.GFq 821 2 Hex.Conway.supportedEntry_821_2 :=
  conwayEmbed 821 1 2 _ _ Hex.Conway.compat_821_1_2

/-- The canonical embedding of GF(821^1) into GF(821^3). -/
noncomputable def embed_821_1_3 :
    Hex.GFq 821 1 Hex.Conway.supportedEntry_821_1 →+*
      Hex.GFq 821 3 Hex.Conway.supportedEntry_821_3 :=
  conwayEmbed 821 1 3 _ _ Hex.Conway.compat_821_1_3

/-- The canonical embedding of GF(823^1) into GF(823^2). -/
noncomputable def embed_823_1_2 :
    Hex.GFq 823 1 Hex.Conway.supportedEntry_823_1 →+*
      Hex.GFq 823 2 Hex.Conway.supportedEntry_823_2 :=
  conwayEmbed 823 1 2 _ _ Hex.Conway.compat_823_1_2

/-- The canonical embedding of GF(823^1) into GF(823^3). -/
noncomputable def embed_823_1_3 :
    Hex.GFq 823 1 Hex.Conway.supportedEntry_823_1 →+*
      Hex.GFq 823 3 Hex.Conway.supportedEntry_823_3 :=
  conwayEmbed 823 1 3 _ _ Hex.Conway.compat_823_1_3

/-- The canonical embedding of GF(827^1) into GF(827^2). -/
noncomputable def embed_827_1_2 :
    Hex.GFq 827 1 Hex.Conway.supportedEntry_827_1 →+*
      Hex.GFq 827 2 Hex.Conway.supportedEntry_827_2 :=
  conwayEmbed 827 1 2 _ _ Hex.Conway.compat_827_1_2

/-- The canonical embedding of GF(827^1) into GF(827^3). -/
noncomputable def embed_827_1_3 :
    Hex.GFq 827 1 Hex.Conway.supportedEntry_827_1 →+*
      Hex.GFq 827 3 Hex.Conway.supportedEntry_827_3 :=
  conwayEmbed 827 1 3 _ _ Hex.Conway.compat_827_1_3

/-- The canonical embedding of GF(829^1) into GF(829^2). -/
noncomputable def embed_829_1_2 :
    Hex.GFq 829 1 Hex.Conway.supportedEntry_829_1 →+*
      Hex.GFq 829 2 Hex.Conway.supportedEntry_829_2 :=
  conwayEmbed 829 1 2 _ _ Hex.Conway.compat_829_1_2

/-- The canonical embedding of GF(829^1) into GF(829^3). -/
noncomputable def embed_829_1_3 :
    Hex.GFq 829 1 Hex.Conway.supportedEntry_829_1 →+*
      Hex.GFq 829 3 Hex.Conway.supportedEntry_829_3 :=
  conwayEmbed 829 1 3 _ _ Hex.Conway.compat_829_1_3

/-- The canonical embedding of GF(839^1) into GF(839^2). -/
noncomputable def embed_839_1_2 :
    Hex.GFq 839 1 Hex.Conway.supportedEntry_839_1 →+*
      Hex.GFq 839 2 Hex.Conway.supportedEntry_839_2 :=
  conwayEmbed 839 1 2 _ _ Hex.Conway.compat_839_1_2

/-- The canonical embedding of GF(839^1) into GF(839^3). -/
noncomputable def embed_839_1_3 :
    Hex.GFq 839 1 Hex.Conway.supportedEntry_839_1 →+*
      Hex.GFq 839 3 Hex.Conway.supportedEntry_839_3 :=
  conwayEmbed 839 1 3 _ _ Hex.Conway.compat_839_1_3

/-- The canonical embedding of GF(853^1) into GF(853^2). -/
noncomputable def embed_853_1_2 :
    Hex.GFq 853 1 Hex.Conway.supportedEntry_853_1 →+*
      Hex.GFq 853 2 Hex.Conway.supportedEntry_853_2 :=
  conwayEmbed 853 1 2 _ _ Hex.Conway.compat_853_1_2

/-- The canonical embedding of GF(853^1) into GF(853^3). -/
noncomputable def embed_853_1_3 :
    Hex.GFq 853 1 Hex.Conway.supportedEntry_853_1 →+*
      Hex.GFq 853 3 Hex.Conway.supportedEntry_853_3 :=
  conwayEmbed 853 1 3 _ _ Hex.Conway.compat_853_1_3

/-- The canonical embedding of GF(857^1) into GF(857^2). -/
noncomputable def embed_857_1_2 :
    Hex.GFq 857 1 Hex.Conway.supportedEntry_857_1 →+*
      Hex.GFq 857 2 Hex.Conway.supportedEntry_857_2 :=
  conwayEmbed 857 1 2 _ _ Hex.Conway.compat_857_1_2

/-- The canonical embedding of GF(857^1) into GF(857^3). -/
noncomputable def embed_857_1_3 :
    Hex.GFq 857 1 Hex.Conway.supportedEntry_857_1 →+*
      Hex.GFq 857 3 Hex.Conway.supportedEntry_857_3 :=
  conwayEmbed 857 1 3 _ _ Hex.Conway.compat_857_1_3

/-- The canonical embedding of GF(859^1) into GF(859^2). -/
noncomputable def embed_859_1_2 :
    Hex.GFq 859 1 Hex.Conway.supportedEntry_859_1 →+*
      Hex.GFq 859 2 Hex.Conway.supportedEntry_859_2 :=
  conwayEmbed 859 1 2 _ _ Hex.Conway.compat_859_1_2

/-- The canonical embedding of GF(859^1) into GF(859^3). -/
noncomputable def embed_859_1_3 :
    Hex.GFq 859 1 Hex.Conway.supportedEntry_859_1 →+*
      Hex.GFq 859 3 Hex.Conway.supportedEntry_859_3 :=
  conwayEmbed 859 1 3 _ _ Hex.Conway.compat_859_1_3

/-- The canonical embedding of GF(863^1) into GF(863^2). -/
noncomputable def embed_863_1_2 :
    Hex.GFq 863 1 Hex.Conway.supportedEntry_863_1 →+*
      Hex.GFq 863 2 Hex.Conway.supportedEntry_863_2 :=
  conwayEmbed 863 1 2 _ _ Hex.Conway.compat_863_1_2

/-- The canonical embedding of GF(863^1) into GF(863^3). -/
noncomputable def embed_863_1_3 :
    Hex.GFq 863 1 Hex.Conway.supportedEntry_863_1 →+*
      Hex.GFq 863 3 Hex.Conway.supportedEntry_863_3 :=
  conwayEmbed 863 1 3 _ _ Hex.Conway.compat_863_1_3

/-- The canonical embedding of GF(877^1) into GF(877^2). -/
noncomputable def embed_877_1_2 :
    Hex.GFq 877 1 Hex.Conway.supportedEntry_877_1 →+*
      Hex.GFq 877 2 Hex.Conway.supportedEntry_877_2 :=
  conwayEmbed 877 1 2 _ _ Hex.Conway.compat_877_1_2

/-- The canonical embedding of GF(877^1) into GF(877^3). -/
noncomputable def embed_877_1_3 :
    Hex.GFq 877 1 Hex.Conway.supportedEntry_877_1 →+*
      Hex.GFq 877 3 Hex.Conway.supportedEntry_877_3 :=
  conwayEmbed 877 1 3 _ _ Hex.Conway.compat_877_1_3

/-- The canonical embedding of GF(881^1) into GF(881^2). -/
noncomputable def embed_881_1_2 :
    Hex.GFq 881 1 Hex.Conway.supportedEntry_881_1 →+*
      Hex.GFq 881 2 Hex.Conway.supportedEntry_881_2 :=
  conwayEmbed 881 1 2 _ _ Hex.Conway.compat_881_1_2

/-- The canonical embedding of GF(881^1) into GF(881^3). -/
noncomputable def embed_881_1_3 :
    Hex.GFq 881 1 Hex.Conway.supportedEntry_881_1 →+*
      Hex.GFq 881 3 Hex.Conway.supportedEntry_881_3 :=
  conwayEmbed 881 1 3 _ _ Hex.Conway.compat_881_1_3

/-- The canonical embedding of GF(883^1) into GF(883^2). -/
noncomputable def embed_883_1_2 :
    Hex.GFq 883 1 Hex.Conway.supportedEntry_883_1 →+*
      Hex.GFq 883 2 Hex.Conway.supportedEntry_883_2 :=
  conwayEmbed 883 1 2 _ _ Hex.Conway.compat_883_1_2

/-- The canonical embedding of GF(883^1) into GF(883^3). -/
noncomputable def embed_883_1_3 :
    Hex.GFq 883 1 Hex.Conway.supportedEntry_883_1 →+*
      Hex.GFq 883 3 Hex.Conway.supportedEntry_883_3 :=
  conwayEmbed 883 1 3 _ _ Hex.Conway.compat_883_1_3

/-- The canonical embedding of GF(887^1) into GF(887^2). -/
noncomputable def embed_887_1_2 :
    Hex.GFq 887 1 Hex.Conway.supportedEntry_887_1 →+*
      Hex.GFq 887 2 Hex.Conway.supportedEntry_887_2 :=
  conwayEmbed 887 1 2 _ _ Hex.Conway.compat_887_1_2

/-- The canonical embedding of GF(887^1) into GF(887^3). -/
noncomputable def embed_887_1_3 :
    Hex.GFq 887 1 Hex.Conway.supportedEntry_887_1 →+*
      Hex.GFq 887 3 Hex.Conway.supportedEntry_887_3 :=
  conwayEmbed 887 1 3 _ _ Hex.Conway.compat_887_1_3

/-- The canonical embedding of GF(907^1) into GF(907^2). -/
noncomputable def embed_907_1_2 :
    Hex.GFq 907 1 Hex.Conway.supportedEntry_907_1 →+*
      Hex.GFq 907 2 Hex.Conway.supportedEntry_907_2 :=
  conwayEmbed 907 1 2 _ _ Hex.Conway.compat_907_1_2

/-- The canonical embedding of GF(907^1) into GF(907^3). -/
noncomputable def embed_907_1_3 :
    Hex.GFq 907 1 Hex.Conway.supportedEntry_907_1 →+*
      Hex.GFq 907 3 Hex.Conway.supportedEntry_907_3 :=
  conwayEmbed 907 1 3 _ _ Hex.Conway.compat_907_1_3

/-- The canonical embedding of GF(911^1) into GF(911^2). -/
noncomputable def embed_911_1_2 :
    Hex.GFq 911 1 Hex.Conway.supportedEntry_911_1 →+*
      Hex.GFq 911 2 Hex.Conway.supportedEntry_911_2 :=
  conwayEmbed 911 1 2 _ _ Hex.Conway.compat_911_1_2

/-- The canonical embedding of GF(911^1) into GF(911^3). -/
noncomputable def embed_911_1_3 :
    Hex.GFq 911 1 Hex.Conway.supportedEntry_911_1 →+*
      Hex.GFq 911 3 Hex.Conway.supportedEntry_911_3 :=
  conwayEmbed 911 1 3 _ _ Hex.Conway.compat_911_1_3

/-- The canonical embedding of GF(919^1) into GF(919^2). -/
noncomputable def embed_919_1_2 :
    Hex.GFq 919 1 Hex.Conway.supportedEntry_919_1 →+*
      Hex.GFq 919 2 Hex.Conway.supportedEntry_919_2 :=
  conwayEmbed 919 1 2 _ _ Hex.Conway.compat_919_1_2

/-- The canonical embedding of GF(919^1) into GF(919^3). -/
noncomputable def embed_919_1_3 :
    Hex.GFq 919 1 Hex.Conway.supportedEntry_919_1 →+*
      Hex.GFq 919 3 Hex.Conway.supportedEntry_919_3 :=
  conwayEmbed 919 1 3 _ _ Hex.Conway.compat_919_1_3

/-- The canonical embedding of GF(929^1) into GF(929^2). -/
noncomputable def embed_929_1_2 :
    Hex.GFq 929 1 Hex.Conway.supportedEntry_929_1 →+*
      Hex.GFq 929 2 Hex.Conway.supportedEntry_929_2 :=
  conwayEmbed 929 1 2 _ _ Hex.Conway.compat_929_1_2

/-- The canonical embedding of GF(929^1) into GF(929^3). -/
noncomputable def embed_929_1_3 :
    Hex.GFq 929 1 Hex.Conway.supportedEntry_929_1 →+*
      Hex.GFq 929 3 Hex.Conway.supportedEntry_929_3 :=
  conwayEmbed 929 1 3 _ _ Hex.Conway.compat_929_1_3

/-- The canonical embedding of GF(937^1) into GF(937^2). -/
noncomputable def embed_937_1_2 :
    Hex.GFq 937 1 Hex.Conway.supportedEntry_937_1 →+*
      Hex.GFq 937 2 Hex.Conway.supportedEntry_937_2 :=
  conwayEmbed 937 1 2 _ _ Hex.Conway.compat_937_1_2

/-- The canonical embedding of GF(937^1) into GF(937^3). -/
noncomputable def embed_937_1_3 :
    Hex.GFq 937 1 Hex.Conway.supportedEntry_937_1 →+*
      Hex.GFq 937 3 Hex.Conway.supportedEntry_937_3 :=
  conwayEmbed 937 1 3 _ _ Hex.Conway.compat_937_1_3

/-- The canonical embedding of GF(941^1) into GF(941^2). -/
noncomputable def embed_941_1_2 :
    Hex.GFq 941 1 Hex.Conway.supportedEntry_941_1 →+*
      Hex.GFq 941 2 Hex.Conway.supportedEntry_941_2 :=
  conwayEmbed 941 1 2 _ _ Hex.Conway.compat_941_1_2

/-- The canonical embedding of GF(941^1) into GF(941^3). -/
noncomputable def embed_941_1_3 :
    Hex.GFq 941 1 Hex.Conway.supportedEntry_941_1 →+*
      Hex.GFq 941 3 Hex.Conway.supportedEntry_941_3 :=
  conwayEmbed 941 1 3 _ _ Hex.Conway.compat_941_1_3

/-- The canonical embedding of GF(947^1) into GF(947^2). -/
noncomputable def embed_947_1_2 :
    Hex.GFq 947 1 Hex.Conway.supportedEntry_947_1 →+*
      Hex.GFq 947 2 Hex.Conway.supportedEntry_947_2 :=
  conwayEmbed 947 1 2 _ _ Hex.Conway.compat_947_1_2

/-- The canonical embedding of GF(947^1) into GF(947^3). -/
noncomputable def embed_947_1_3 :
    Hex.GFq 947 1 Hex.Conway.supportedEntry_947_1 →+*
      Hex.GFq 947 3 Hex.Conway.supportedEntry_947_3 :=
  conwayEmbed 947 1 3 _ _ Hex.Conway.compat_947_1_3

/-- The canonical embedding of GF(953^1) into GF(953^2). -/
noncomputable def embed_953_1_2 :
    Hex.GFq 953 1 Hex.Conway.supportedEntry_953_1 →+*
      Hex.GFq 953 2 Hex.Conway.supportedEntry_953_2 :=
  conwayEmbed 953 1 2 _ _ Hex.Conway.compat_953_1_2

/-- The canonical embedding of GF(953^1) into GF(953^3). -/
noncomputable def embed_953_1_3 :
    Hex.GFq 953 1 Hex.Conway.supportedEntry_953_1 →+*
      Hex.GFq 953 3 Hex.Conway.supportedEntry_953_3 :=
  conwayEmbed 953 1 3 _ _ Hex.Conway.compat_953_1_3

/-- The canonical embedding of GF(967^1) into GF(967^2). -/
noncomputable def embed_967_1_2 :
    Hex.GFq 967 1 Hex.Conway.supportedEntry_967_1 →+*
      Hex.GFq 967 2 Hex.Conway.supportedEntry_967_2 :=
  conwayEmbed 967 1 2 _ _ Hex.Conway.compat_967_1_2

/-- The canonical embedding of GF(967^1) into GF(967^3). -/
noncomputable def embed_967_1_3 :
    Hex.GFq 967 1 Hex.Conway.supportedEntry_967_1 →+*
      Hex.GFq 967 3 Hex.Conway.supportedEntry_967_3 :=
  conwayEmbed 967 1 3 _ _ Hex.Conway.compat_967_1_3

/-- The canonical embedding of GF(971^1) into GF(971^2). -/
noncomputable def embed_971_1_2 :
    Hex.GFq 971 1 Hex.Conway.supportedEntry_971_1 →+*
      Hex.GFq 971 2 Hex.Conway.supportedEntry_971_2 :=
  conwayEmbed 971 1 2 _ _ Hex.Conway.compat_971_1_2

/-- The canonical embedding of GF(971^1) into GF(971^3). -/
noncomputable def embed_971_1_3 :
    Hex.GFq 971 1 Hex.Conway.supportedEntry_971_1 →+*
      Hex.GFq 971 3 Hex.Conway.supportedEntry_971_3 :=
  conwayEmbed 971 1 3 _ _ Hex.Conway.compat_971_1_3

/-- The canonical embedding of GF(977^1) into GF(977^2). -/
noncomputable def embed_977_1_2 :
    Hex.GFq 977 1 Hex.Conway.supportedEntry_977_1 →+*
      Hex.GFq 977 2 Hex.Conway.supportedEntry_977_2 :=
  conwayEmbed 977 1 2 _ _ Hex.Conway.compat_977_1_2

/-- The canonical embedding of GF(977^1) into GF(977^3). -/
noncomputable def embed_977_1_3 :
    Hex.GFq 977 1 Hex.Conway.supportedEntry_977_1 →+*
      Hex.GFq 977 3 Hex.Conway.supportedEntry_977_3 :=
  conwayEmbed 977 1 3 _ _ Hex.Conway.compat_977_1_3

/-- The canonical embedding of GF(983^1) into GF(983^2). -/
noncomputable def embed_983_1_2 :
    Hex.GFq 983 1 Hex.Conway.supportedEntry_983_1 →+*
      Hex.GFq 983 2 Hex.Conway.supportedEntry_983_2 :=
  conwayEmbed 983 1 2 _ _ Hex.Conway.compat_983_1_2

/-- The canonical embedding of GF(983^1) into GF(983^3). -/
noncomputable def embed_983_1_3 :
    Hex.GFq 983 1 Hex.Conway.supportedEntry_983_1 →+*
      Hex.GFq 983 3 Hex.Conway.supportedEntry_983_3 :=
  conwayEmbed 983 1 3 _ _ Hex.Conway.compat_983_1_3

/-- The canonical embedding of GF(991^1) into GF(991^2). -/
noncomputable def embed_991_1_2 :
    Hex.GFq 991 1 Hex.Conway.supportedEntry_991_1 →+*
      Hex.GFq 991 2 Hex.Conway.supportedEntry_991_2 :=
  conwayEmbed 991 1 2 _ _ Hex.Conway.compat_991_1_2

/-- The canonical embedding of GF(991^1) into GF(991^3). -/
noncomputable def embed_991_1_3 :
    Hex.GFq 991 1 Hex.Conway.supportedEntry_991_1 →+*
      Hex.GFq 991 3 Hex.Conway.supportedEntry_991_3 :=
  conwayEmbed 991 1 3 _ _ Hex.Conway.compat_991_1_3

/-- The canonical embedding of GF(997^1) into GF(997^2). -/
noncomputable def embed_997_1_2 :
    Hex.GFq 997 1 Hex.Conway.supportedEntry_997_1 →+*
      Hex.GFq 997 2 Hex.Conway.supportedEntry_997_2 :=
  conwayEmbed 997 1 2 _ _ Hex.Conway.compat_997_1_2

/-- The canonical embedding of GF(997^1) into GF(997^3). -/
noncomputable def embed_997_1_3 :
    Hex.GFq 997 1 Hex.Conway.supportedEntry_997_1 →+*
      Hex.GFq 997 3 Hex.Conway.supportedEntry_997_3 :=
  conwayEmbed 997 1 3 _ _ Hex.Conway.compat_997_1_3

end HexGFqMathlib.Conway
