/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(59^1) into GF(59^4). -/
noncomputable def embed_59_1_4 :
    Hex.GFq 59 1 Hex.Conway.supportedEntry_59_1 →+*
      Hex.GFq 59 4 Hex.Conway.supportedEntry_59_4 :=
  conwayEmbed 59 1 4 _ _ Hex.Conway.compat_59_1_4

/-- The canonical embedding of GF(59^2) into GF(59^4). -/
noncomputable def embed_59_2_4 :
    Hex.GFq 59 2 Hex.Conway.supportedEntry_59_2 →+*
      Hex.GFq 59 4 Hex.Conway.supportedEntry_59_4 :=
  conwayEmbed 59 2 4 _ _ Hex.Conway.compat_59_2_4

/-- The canonical embedding of GF(61^1) into GF(61^2). -/
noncomputable def embed_61_1_2 :
    Hex.GFq 61 1 Hex.Conway.supportedEntry_61_1 →+*
      Hex.GFq 61 2 Hex.Conway.supportedEntry_61_2 :=
  conwayEmbed 61 1 2 _ _ Hex.Conway.compat_61_1_2

/-- The canonical embedding of GF(61^1) into GF(61^3). -/
noncomputable def embed_61_1_3 :
    Hex.GFq 61 1 Hex.Conway.supportedEntry_61_1 →+*
      Hex.GFq 61 3 Hex.Conway.supportedEntry_61_3 :=
  conwayEmbed 61 1 3 _ _ Hex.Conway.compat_61_1_3

/-- The canonical embedding of GF(61^1) into GF(61^4). -/
noncomputable def embed_61_1_4 :
    Hex.GFq 61 1 Hex.Conway.supportedEntry_61_1 →+*
      Hex.GFq 61 4 Hex.Conway.supportedEntry_61_4 :=
  conwayEmbed 61 1 4 _ _ Hex.Conway.compat_61_1_4

/-- The canonical embedding of GF(61^2) into GF(61^4). -/
noncomputable def embed_61_2_4 :
    Hex.GFq 61 2 Hex.Conway.supportedEntry_61_2 →+*
      Hex.GFq 61 4 Hex.Conway.supportedEntry_61_4 :=
  conwayEmbed 61 2 4 _ _ Hex.Conway.compat_61_2_4

/-- The canonical embedding of GF(67^1) into GF(67^2). -/
noncomputable def embed_67_1_2 :
    Hex.GFq 67 1 Hex.Conway.supportedEntry_67_1 →+*
      Hex.GFq 67 2 Hex.Conway.supportedEntry_67_2 :=
  conwayEmbed 67 1 2 _ _ Hex.Conway.compat_67_1_2

/-- The canonical embedding of GF(67^1) into GF(67^3). -/
noncomputable def embed_67_1_3 :
    Hex.GFq 67 1 Hex.Conway.supportedEntry_67_1 →+*
      Hex.GFq 67 3 Hex.Conway.supportedEntry_67_3 :=
  conwayEmbed 67 1 3 _ _ Hex.Conway.compat_67_1_3

/-- The canonical embedding of GF(67^1) into GF(67^4). -/
noncomputable def embed_67_1_4 :
    Hex.GFq 67 1 Hex.Conway.supportedEntry_67_1 →+*
      Hex.GFq 67 4 Hex.Conway.supportedEntry_67_4 :=
  conwayEmbed 67 1 4 _ _ Hex.Conway.compat_67_1_4

/-- The canonical embedding of GF(67^2) into GF(67^4). -/
noncomputable def embed_67_2_4 :
    Hex.GFq 67 2 Hex.Conway.supportedEntry_67_2 →+*
      Hex.GFq 67 4 Hex.Conway.supportedEntry_67_4 :=
  conwayEmbed 67 2 4 _ _ Hex.Conway.compat_67_2_4

/-- The canonical embedding of GF(71^1) into GF(71^2). -/
noncomputable def embed_71_1_2 :
    Hex.GFq 71 1 Hex.Conway.supportedEntry_71_1 →+*
      Hex.GFq 71 2 Hex.Conway.supportedEntry_71_2 :=
  conwayEmbed 71 1 2 _ _ Hex.Conway.compat_71_1_2

/-- The canonical embedding of GF(71^1) into GF(71^3). -/
noncomputable def embed_71_1_3 :
    Hex.GFq 71 1 Hex.Conway.supportedEntry_71_1 →+*
      Hex.GFq 71 3 Hex.Conway.supportedEntry_71_3 :=
  conwayEmbed 71 1 3 _ _ Hex.Conway.compat_71_1_3

/-- The canonical embedding of GF(71^1) into GF(71^4). -/
noncomputable def embed_71_1_4 :
    Hex.GFq 71 1 Hex.Conway.supportedEntry_71_1 →+*
      Hex.GFq 71 4 Hex.Conway.supportedEntry_71_4 :=
  conwayEmbed 71 1 4 _ _ Hex.Conway.compat_71_1_4

/-- The canonical embedding of GF(71^2) into GF(71^4). -/
noncomputable def embed_71_2_4 :
    Hex.GFq 71 2 Hex.Conway.supportedEntry_71_2 →+*
      Hex.GFq 71 4 Hex.Conway.supportedEntry_71_4 :=
  conwayEmbed 71 2 4 _ _ Hex.Conway.compat_71_2_4

/-- The canonical embedding of GF(73^1) into GF(73^2). -/
noncomputable def embed_73_1_2 :
    Hex.GFq 73 1 Hex.Conway.supportedEntry_73_1 →+*
      Hex.GFq 73 2 Hex.Conway.supportedEntry_73_2 :=
  conwayEmbed 73 1 2 _ _ Hex.Conway.compat_73_1_2

/-- The canonical embedding of GF(73^1) into GF(73^3). -/
noncomputable def embed_73_1_3 :
    Hex.GFq 73 1 Hex.Conway.supportedEntry_73_1 →+*
      Hex.GFq 73 3 Hex.Conway.supportedEntry_73_3 :=
  conwayEmbed 73 1 3 _ _ Hex.Conway.compat_73_1_3

/-- The canonical embedding of GF(73^1) into GF(73^4). -/
noncomputable def embed_73_1_4 :
    Hex.GFq 73 1 Hex.Conway.supportedEntry_73_1 →+*
      Hex.GFq 73 4 Hex.Conway.supportedEntry_73_4 :=
  conwayEmbed 73 1 4 _ _ Hex.Conway.compat_73_1_4

/-- The canonical embedding of GF(73^2) into GF(73^4). -/
noncomputable def embed_73_2_4 :
    Hex.GFq 73 2 Hex.Conway.supportedEntry_73_2 →+*
      Hex.GFq 73 4 Hex.Conway.supportedEntry_73_4 :=
  conwayEmbed 73 2 4 _ _ Hex.Conway.compat_73_2_4

/-- The canonical embedding of GF(79^1) into GF(79^2). -/
noncomputable def embed_79_1_2 :
    Hex.GFq 79 1 Hex.Conway.supportedEntry_79_1 →+*
      Hex.GFq 79 2 Hex.Conway.supportedEntry_79_2 :=
  conwayEmbed 79 1 2 _ _ Hex.Conway.compat_79_1_2

/-- The canonical embedding of GF(79^1) into GF(79^3). -/
noncomputable def embed_79_1_3 :
    Hex.GFq 79 1 Hex.Conway.supportedEntry_79_1 →+*
      Hex.GFq 79 3 Hex.Conway.supportedEntry_79_3 :=
  conwayEmbed 79 1 3 _ _ Hex.Conway.compat_79_1_3

/-- The canonical embedding of GF(79^1) into GF(79^4). -/
noncomputable def embed_79_1_4 :
    Hex.GFq 79 1 Hex.Conway.supportedEntry_79_1 →+*
      Hex.GFq 79 4 Hex.Conway.supportedEntry_79_4 :=
  conwayEmbed 79 1 4 _ _ Hex.Conway.compat_79_1_4

/-- The canonical embedding of GF(79^2) into GF(79^4). -/
noncomputable def embed_79_2_4 :
    Hex.GFq 79 2 Hex.Conway.supportedEntry_79_2 →+*
      Hex.GFq 79 4 Hex.Conway.supportedEntry_79_4 :=
  conwayEmbed 79 2 4 _ _ Hex.Conway.compat_79_2_4

/-- The canonical embedding of GF(83^1) into GF(83^2). -/
noncomputable def embed_83_1_2 :
    Hex.GFq 83 1 Hex.Conway.supportedEntry_83_1 →+*
      Hex.GFq 83 2 Hex.Conway.supportedEntry_83_2 :=
  conwayEmbed 83 1 2 _ _ Hex.Conway.compat_83_1_2

/-- The canonical embedding of GF(83^1) into GF(83^3). -/
noncomputable def embed_83_1_3 :
    Hex.GFq 83 1 Hex.Conway.supportedEntry_83_1 →+*
      Hex.GFq 83 3 Hex.Conway.supportedEntry_83_3 :=
  conwayEmbed 83 1 3 _ _ Hex.Conway.compat_83_1_3

/-- The canonical embedding of GF(83^1) into GF(83^4). -/
noncomputable def embed_83_1_4 :
    Hex.GFq 83 1 Hex.Conway.supportedEntry_83_1 →+*
      Hex.GFq 83 4 Hex.Conway.supportedEntry_83_4 :=
  conwayEmbed 83 1 4 _ _ Hex.Conway.compat_83_1_4

/-- The canonical embedding of GF(83^2) into GF(83^4). -/
noncomputable def embed_83_2_4 :
    Hex.GFq 83 2 Hex.Conway.supportedEntry_83_2 →+*
      Hex.GFq 83 4 Hex.Conway.supportedEntry_83_4 :=
  conwayEmbed 83 2 4 _ _ Hex.Conway.compat_83_2_4

/-- The canonical embedding of GF(89^1) into GF(89^2). -/
noncomputable def embed_89_1_2 :
    Hex.GFq 89 1 Hex.Conway.supportedEntry_89_1 →+*
      Hex.GFq 89 2 Hex.Conway.supportedEntry_89_2 :=
  conwayEmbed 89 1 2 _ _ Hex.Conway.compat_89_1_2

/-- The canonical embedding of GF(89^1) into GF(89^3). -/
noncomputable def embed_89_1_3 :
    Hex.GFq 89 1 Hex.Conway.supportedEntry_89_1 →+*
      Hex.GFq 89 3 Hex.Conway.supportedEntry_89_3 :=
  conwayEmbed 89 1 3 _ _ Hex.Conway.compat_89_1_3

/-- The canonical embedding of GF(89^1) into GF(89^4). -/
noncomputable def embed_89_1_4 :
    Hex.GFq 89 1 Hex.Conway.supportedEntry_89_1 →+*
      Hex.GFq 89 4 Hex.Conway.supportedEntry_89_4 :=
  conwayEmbed 89 1 4 _ _ Hex.Conway.compat_89_1_4

/-- The canonical embedding of GF(89^2) into GF(89^4). -/
noncomputable def embed_89_2_4 :
    Hex.GFq 89 2 Hex.Conway.supportedEntry_89_2 →+*
      Hex.GFq 89 4 Hex.Conway.supportedEntry_89_4 :=
  conwayEmbed 89 2 4 _ _ Hex.Conway.compat_89_2_4

/-- The canonical embedding of GF(97^1) into GF(97^2). -/
noncomputable def embed_97_1_2 :
    Hex.GFq 97 1 Hex.Conway.supportedEntry_97_1 →+*
      Hex.GFq 97 2 Hex.Conway.supportedEntry_97_2 :=
  conwayEmbed 97 1 2 _ _ Hex.Conway.compat_97_1_2

/-- The canonical embedding of GF(97^1) into GF(97^3). -/
noncomputable def embed_97_1_3 :
    Hex.GFq 97 1 Hex.Conway.supportedEntry_97_1 →+*
      Hex.GFq 97 3 Hex.Conway.supportedEntry_97_3 :=
  conwayEmbed 97 1 3 _ _ Hex.Conway.compat_97_1_3

/-- The canonical embedding of GF(97^1) into GF(97^4). -/
noncomputable def embed_97_1_4 :
    Hex.GFq 97 1 Hex.Conway.supportedEntry_97_1 →+*
      Hex.GFq 97 4 Hex.Conway.supportedEntry_97_4 :=
  conwayEmbed 97 1 4 _ _ Hex.Conway.compat_97_1_4

/-- The canonical embedding of GF(97^2) into GF(97^4). -/
noncomputable def embed_97_2_4 :
    Hex.GFq 97 2 Hex.Conway.supportedEntry_97_2 →+*
      Hex.GFq 97 4 Hex.Conway.supportedEntry_97_4 :=
  conwayEmbed 97 2 4 _ _ Hex.Conway.compat_97_2_4

/-- The canonical embedding of GF(101^1) into GF(101^2). -/
noncomputable def embed_101_1_2 :
    Hex.GFq 101 1 Hex.Conway.supportedEntry_101_1 →+*
      Hex.GFq 101 2 Hex.Conway.supportedEntry_101_2 :=
  conwayEmbed 101 1 2 _ _ Hex.Conway.compat_101_1_2

/-- The canonical embedding of GF(101^1) into GF(101^3). -/
noncomputable def embed_101_1_3 :
    Hex.GFq 101 1 Hex.Conway.supportedEntry_101_1 →+*
      Hex.GFq 101 3 Hex.Conway.supportedEntry_101_3 :=
  conwayEmbed 101 1 3 _ _ Hex.Conway.compat_101_1_3

/-- The canonical embedding of GF(101^1) into GF(101^4). -/
noncomputable def embed_101_1_4 :
    Hex.GFq 101 1 Hex.Conway.supportedEntry_101_1 →+*
      Hex.GFq 101 4 Hex.Conway.supportedEntry_101_4 :=
  conwayEmbed 101 1 4 _ _ Hex.Conway.compat_101_1_4

/-- The canonical embedding of GF(101^2) into GF(101^4). -/
noncomputable def embed_101_2_4 :
    Hex.GFq 101 2 Hex.Conway.supportedEntry_101_2 →+*
      Hex.GFq 101 4 Hex.Conway.supportedEntry_101_4 :=
  conwayEmbed 101 2 4 _ _ Hex.Conway.compat_101_2_4

/-- The canonical embedding of GF(103^1) into GF(103^2). -/
noncomputable def embed_103_1_2 :
    Hex.GFq 103 1 Hex.Conway.supportedEntry_103_1 →+*
      Hex.GFq 103 2 Hex.Conway.supportedEntry_103_2 :=
  conwayEmbed 103 1 2 _ _ Hex.Conway.compat_103_1_2

/-- The canonical embedding of GF(103^1) into GF(103^3). -/
noncomputable def embed_103_1_3 :
    Hex.GFq 103 1 Hex.Conway.supportedEntry_103_1 →+*
      Hex.GFq 103 3 Hex.Conway.supportedEntry_103_3 :=
  conwayEmbed 103 1 3 _ _ Hex.Conway.compat_103_1_3

/-- The canonical embedding of GF(103^1) into GF(103^4). -/
noncomputable def embed_103_1_4 :
    Hex.GFq 103 1 Hex.Conway.supportedEntry_103_1 →+*
      Hex.GFq 103 4 Hex.Conway.supportedEntry_103_4 :=
  conwayEmbed 103 1 4 _ _ Hex.Conway.compat_103_1_4

/-- The canonical embedding of GF(103^2) into GF(103^4). -/
noncomputable def embed_103_2_4 :
    Hex.GFq 103 2 Hex.Conway.supportedEntry_103_2 →+*
      Hex.GFq 103 4 Hex.Conway.supportedEntry_103_4 :=
  conwayEmbed 103 2 4 _ _ Hex.Conway.compat_103_2_4

/-- The canonical embedding of GF(107^1) into GF(107^2). -/
noncomputable def embed_107_1_2 :
    Hex.GFq 107 1 Hex.Conway.supportedEntry_107_1 →+*
      Hex.GFq 107 2 Hex.Conway.supportedEntry_107_2 :=
  conwayEmbed 107 1 2 _ _ Hex.Conway.compat_107_1_2

/-- The canonical embedding of GF(107^1) into GF(107^3). -/
noncomputable def embed_107_1_3 :
    Hex.GFq 107 1 Hex.Conway.supportedEntry_107_1 →+*
      Hex.GFq 107 3 Hex.Conway.supportedEntry_107_3 :=
  conwayEmbed 107 1 3 _ _ Hex.Conway.compat_107_1_3

/-- The canonical embedding of GF(107^1) into GF(107^4). -/
noncomputable def embed_107_1_4 :
    Hex.GFq 107 1 Hex.Conway.supportedEntry_107_1 →+*
      Hex.GFq 107 4 Hex.Conway.supportedEntry_107_4 :=
  conwayEmbed 107 1 4 _ _ Hex.Conway.compat_107_1_4

/-- The canonical embedding of GF(107^2) into GF(107^4). -/
noncomputable def embed_107_2_4 :
    Hex.GFq 107 2 Hex.Conway.supportedEntry_107_2 →+*
      Hex.GFq 107 4 Hex.Conway.supportedEntry_107_4 :=
  conwayEmbed 107 2 4 _ _ Hex.Conway.compat_107_2_4

/-- The canonical embedding of GF(109^1) into GF(109^2). -/
noncomputable def embed_109_1_2 :
    Hex.GFq 109 1 Hex.Conway.supportedEntry_109_1 →+*
      Hex.GFq 109 2 Hex.Conway.supportedEntry_109_2 :=
  conwayEmbed 109 1 2 _ _ Hex.Conway.compat_109_1_2

/-- The canonical embedding of GF(109^1) into GF(109^3). -/
noncomputable def embed_109_1_3 :
    Hex.GFq 109 1 Hex.Conway.supportedEntry_109_1 →+*
      Hex.GFq 109 3 Hex.Conway.supportedEntry_109_3 :=
  conwayEmbed 109 1 3 _ _ Hex.Conway.compat_109_1_3

/-- The canonical embedding of GF(109^1) into GF(109^4). -/
noncomputable def embed_109_1_4 :
    Hex.GFq 109 1 Hex.Conway.supportedEntry_109_1 →+*
      Hex.GFq 109 4 Hex.Conway.supportedEntry_109_4 :=
  conwayEmbed 109 1 4 _ _ Hex.Conway.compat_109_1_4

/-- The canonical embedding of GF(109^2) into GF(109^4). -/
noncomputable def embed_109_2_4 :
    Hex.GFq 109 2 Hex.Conway.supportedEntry_109_2 →+*
      Hex.GFq 109 4 Hex.Conway.supportedEntry_109_4 :=
  conwayEmbed 109 2 4 _ _ Hex.Conway.compat_109_2_4

/-- The canonical embedding of GF(113^1) into GF(113^2). -/
noncomputable def embed_113_1_2 :
    Hex.GFq 113 1 Hex.Conway.supportedEntry_113_1 →+*
      Hex.GFq 113 2 Hex.Conway.supportedEntry_113_2 :=
  conwayEmbed 113 1 2 _ _ Hex.Conway.compat_113_1_2

/-- The canonical embedding of GF(113^1) into GF(113^3). -/
noncomputable def embed_113_1_3 :
    Hex.GFq 113 1 Hex.Conway.supportedEntry_113_1 →+*
      Hex.GFq 113 3 Hex.Conway.supportedEntry_113_3 :=
  conwayEmbed 113 1 3 _ _ Hex.Conway.compat_113_1_3

/-- The canonical embedding of GF(113^1) into GF(113^4). -/
noncomputable def embed_113_1_4 :
    Hex.GFq 113 1 Hex.Conway.supportedEntry_113_1 →+*
      Hex.GFq 113 4 Hex.Conway.supportedEntry_113_4 :=
  conwayEmbed 113 1 4 _ _ Hex.Conway.compat_113_1_4

/-- The canonical embedding of GF(113^2) into GF(113^4). -/
noncomputable def embed_113_2_4 :
    Hex.GFq 113 2 Hex.Conway.supportedEntry_113_2 →+*
      Hex.GFq 113 4 Hex.Conway.supportedEntry_113_4 :=
  conwayEmbed 113 2 4 _ _ Hex.Conway.compat_113_2_4

/-- The canonical embedding of GF(127^1) into GF(127^2). -/
noncomputable def embed_127_1_2 :
    Hex.GFq 127 1 Hex.Conway.supportedEntry_127_1 →+*
      Hex.GFq 127 2 Hex.Conway.supportedEntry_127_2 :=
  conwayEmbed 127 1 2 _ _ Hex.Conway.compat_127_1_2

/-- The canonical embedding of GF(127^1) into GF(127^3). -/
noncomputable def embed_127_1_3 :
    Hex.GFq 127 1 Hex.Conway.supportedEntry_127_1 →+*
      Hex.GFq 127 3 Hex.Conway.supportedEntry_127_3 :=
  conwayEmbed 127 1 3 _ _ Hex.Conway.compat_127_1_3

/-- The canonical embedding of GF(127^1) into GF(127^4). -/
noncomputable def embed_127_1_4 :
    Hex.GFq 127 1 Hex.Conway.supportedEntry_127_1 →+*
      Hex.GFq 127 4 Hex.Conway.supportedEntry_127_4 :=
  conwayEmbed 127 1 4 _ _ Hex.Conway.compat_127_1_4

/-- The canonical embedding of GF(127^2) into GF(127^4). -/
noncomputable def embed_127_2_4 :
    Hex.GFq 127 2 Hex.Conway.supportedEntry_127_2 →+*
      Hex.GFq 127 4 Hex.Conway.supportedEntry_127_4 :=
  conwayEmbed 127 2 4 _ _ Hex.Conway.compat_127_2_4

/-- The canonical embedding of GF(131^1) into GF(131^2). -/
noncomputable def embed_131_1_2 :
    Hex.GFq 131 1 Hex.Conway.supportedEntry_131_1 →+*
      Hex.GFq 131 2 Hex.Conway.supportedEntry_131_2 :=
  conwayEmbed 131 1 2 _ _ Hex.Conway.compat_131_1_2

/-- The canonical embedding of GF(131^1) into GF(131^3). -/
noncomputable def embed_131_1_3 :
    Hex.GFq 131 1 Hex.Conway.supportedEntry_131_1 →+*
      Hex.GFq 131 3 Hex.Conway.supportedEntry_131_3 :=
  conwayEmbed 131 1 3 _ _ Hex.Conway.compat_131_1_3

/-- The canonical embedding of GF(131^1) into GF(131^4). -/
noncomputable def embed_131_1_4 :
    Hex.GFq 131 1 Hex.Conway.supportedEntry_131_1 →+*
      Hex.GFq 131 4 Hex.Conway.supportedEntry_131_4 :=
  conwayEmbed 131 1 4 _ _ Hex.Conway.compat_131_1_4

/-- The canonical embedding of GF(131^2) into GF(131^4). -/
noncomputable def embed_131_2_4 :
    Hex.GFq 131 2 Hex.Conway.supportedEntry_131_2 →+*
      Hex.GFq 131 4 Hex.Conway.supportedEntry_131_4 :=
  conwayEmbed 131 2 4 _ _ Hex.Conway.compat_131_2_4

/-- The canonical embedding of GF(137^1) into GF(137^2). -/
noncomputable def embed_137_1_2 :
    Hex.GFq 137 1 Hex.Conway.supportedEntry_137_1 →+*
      Hex.GFq 137 2 Hex.Conway.supportedEntry_137_2 :=
  conwayEmbed 137 1 2 _ _ Hex.Conway.compat_137_1_2

/-- The canonical embedding of GF(137^1) into GF(137^3). -/
noncomputable def embed_137_1_3 :
    Hex.GFq 137 1 Hex.Conway.supportedEntry_137_1 →+*
      Hex.GFq 137 3 Hex.Conway.supportedEntry_137_3 :=
  conwayEmbed 137 1 3 _ _ Hex.Conway.compat_137_1_3

/-- The canonical embedding of GF(137^1) into GF(137^4). -/
noncomputable def embed_137_1_4 :
    Hex.GFq 137 1 Hex.Conway.supportedEntry_137_1 →+*
      Hex.GFq 137 4 Hex.Conway.supportedEntry_137_4 :=
  conwayEmbed 137 1 4 _ _ Hex.Conway.compat_137_1_4

/-- The canonical embedding of GF(137^2) into GF(137^4). -/
noncomputable def embed_137_2_4 :
    Hex.GFq 137 2 Hex.Conway.supportedEntry_137_2 →+*
      Hex.GFq 137 4 Hex.Conway.supportedEntry_137_4 :=
  conwayEmbed 137 2 4 _ _ Hex.Conway.compat_137_2_4

/-- The canonical embedding of GF(139^1) into GF(139^2). -/
noncomputable def embed_139_1_2 :
    Hex.GFq 139 1 Hex.Conway.supportedEntry_139_1 →+*
      Hex.GFq 139 2 Hex.Conway.supportedEntry_139_2 :=
  conwayEmbed 139 1 2 _ _ Hex.Conway.compat_139_1_2

/-- The canonical embedding of GF(139^1) into GF(139^3). -/
noncomputable def embed_139_1_3 :
    Hex.GFq 139 1 Hex.Conway.supportedEntry_139_1 →+*
      Hex.GFq 139 3 Hex.Conway.supportedEntry_139_3 :=
  conwayEmbed 139 1 3 _ _ Hex.Conway.compat_139_1_3

/-- The canonical embedding of GF(139^1) into GF(139^4). -/
noncomputable def embed_139_1_4 :
    Hex.GFq 139 1 Hex.Conway.supportedEntry_139_1 →+*
      Hex.GFq 139 4 Hex.Conway.supportedEntry_139_4 :=
  conwayEmbed 139 1 4 _ _ Hex.Conway.compat_139_1_4

/-- The canonical embedding of GF(139^2) into GF(139^4). -/
noncomputable def embed_139_2_4 :
    Hex.GFq 139 2 Hex.Conway.supportedEntry_139_2 →+*
      Hex.GFq 139 4 Hex.Conway.supportedEntry_139_4 :=
  conwayEmbed 139 2 4 _ _ Hex.Conway.compat_139_2_4

/-- The canonical embedding of GF(149^1) into GF(149^2). -/
noncomputable def embed_149_1_2 :
    Hex.GFq 149 1 Hex.Conway.supportedEntry_149_1 →+*
      Hex.GFq 149 2 Hex.Conway.supportedEntry_149_2 :=
  conwayEmbed 149 1 2 _ _ Hex.Conway.compat_149_1_2

/-- The canonical embedding of GF(149^1) into GF(149^3). -/
noncomputable def embed_149_1_3 :
    Hex.GFq 149 1 Hex.Conway.supportedEntry_149_1 →+*
      Hex.GFq 149 3 Hex.Conway.supportedEntry_149_3 :=
  conwayEmbed 149 1 3 _ _ Hex.Conway.compat_149_1_3

/-- The canonical embedding of GF(149^1) into GF(149^4). -/
noncomputable def embed_149_1_4 :
    Hex.GFq 149 1 Hex.Conway.supportedEntry_149_1 →+*
      Hex.GFq 149 4 Hex.Conway.supportedEntry_149_4 :=
  conwayEmbed 149 1 4 _ _ Hex.Conway.compat_149_1_4

/-- The canonical embedding of GF(149^2) into GF(149^4). -/
noncomputable def embed_149_2_4 :
    Hex.GFq 149 2 Hex.Conway.supportedEntry_149_2 →+*
      Hex.GFq 149 4 Hex.Conway.supportedEntry_149_4 :=
  conwayEmbed 149 2 4 _ _ Hex.Conway.compat_149_2_4

/-- The canonical embedding of GF(151^1) into GF(151^2). -/
noncomputable def embed_151_1_2 :
    Hex.GFq 151 1 Hex.Conway.supportedEntry_151_1 →+*
      Hex.GFq 151 2 Hex.Conway.supportedEntry_151_2 :=
  conwayEmbed 151 1 2 _ _ Hex.Conway.compat_151_1_2

/-- The canonical embedding of GF(151^1) into GF(151^3). -/
noncomputable def embed_151_1_3 :
    Hex.GFq 151 1 Hex.Conway.supportedEntry_151_1 →+*
      Hex.GFq 151 3 Hex.Conway.supportedEntry_151_3 :=
  conwayEmbed 151 1 3 _ _ Hex.Conway.compat_151_1_3

/-- The canonical embedding of GF(151^1) into GF(151^4). -/
noncomputable def embed_151_1_4 :
    Hex.GFq 151 1 Hex.Conway.supportedEntry_151_1 →+*
      Hex.GFq 151 4 Hex.Conway.supportedEntry_151_4 :=
  conwayEmbed 151 1 4 _ _ Hex.Conway.compat_151_1_4

/-- The canonical embedding of GF(151^2) into GF(151^4). -/
noncomputable def embed_151_2_4 :
    Hex.GFq 151 2 Hex.Conway.supportedEntry_151_2 →+*
      Hex.GFq 151 4 Hex.Conway.supportedEntry_151_4 :=
  conwayEmbed 151 2 4 _ _ Hex.Conway.compat_151_2_4

/-- The canonical embedding of GF(157^1) into GF(157^2). -/
noncomputable def embed_157_1_2 :
    Hex.GFq 157 1 Hex.Conway.supportedEntry_157_1 →+*
      Hex.GFq 157 2 Hex.Conway.supportedEntry_157_2 :=
  conwayEmbed 157 1 2 _ _ Hex.Conway.compat_157_1_2

/-- The canonical embedding of GF(157^1) into GF(157^3). -/
noncomputable def embed_157_1_3 :
    Hex.GFq 157 1 Hex.Conway.supportedEntry_157_1 →+*
      Hex.GFq 157 3 Hex.Conway.supportedEntry_157_3 :=
  conwayEmbed 157 1 3 _ _ Hex.Conway.compat_157_1_3

/-- The canonical embedding of GF(157^1) into GF(157^4). -/
noncomputable def embed_157_1_4 :
    Hex.GFq 157 1 Hex.Conway.supportedEntry_157_1 →+*
      Hex.GFq 157 4 Hex.Conway.supportedEntry_157_4 :=
  conwayEmbed 157 1 4 _ _ Hex.Conway.compat_157_1_4

/-- The canonical embedding of GF(157^2) into GF(157^4). -/
noncomputable def embed_157_2_4 :
    Hex.GFq 157 2 Hex.Conway.supportedEntry_157_2 →+*
      Hex.GFq 157 4 Hex.Conway.supportedEntry_157_4 :=
  conwayEmbed 157 2 4 _ _ Hex.Conway.compat_157_2_4

/-- The canonical embedding of GF(163^1) into GF(163^2). -/
noncomputable def embed_163_1_2 :
    Hex.GFq 163 1 Hex.Conway.supportedEntry_163_1 →+*
      Hex.GFq 163 2 Hex.Conway.supportedEntry_163_2 :=
  conwayEmbed 163 1 2 _ _ Hex.Conway.compat_163_1_2

/-- The canonical embedding of GF(163^1) into GF(163^3). -/
noncomputable def embed_163_1_3 :
    Hex.GFq 163 1 Hex.Conway.supportedEntry_163_1 →+*
      Hex.GFq 163 3 Hex.Conway.supportedEntry_163_3 :=
  conwayEmbed 163 1 3 _ _ Hex.Conway.compat_163_1_3

/-- The canonical embedding of GF(163^1) into GF(163^4). -/
noncomputable def embed_163_1_4 :
    Hex.GFq 163 1 Hex.Conway.supportedEntry_163_1 →+*
      Hex.GFq 163 4 Hex.Conway.supportedEntry_163_4 :=
  conwayEmbed 163 1 4 _ _ Hex.Conway.compat_163_1_4

/-- The canonical embedding of GF(163^2) into GF(163^4). -/
noncomputable def embed_163_2_4 :
    Hex.GFq 163 2 Hex.Conway.supportedEntry_163_2 →+*
      Hex.GFq 163 4 Hex.Conway.supportedEntry_163_4 :=
  conwayEmbed 163 2 4 _ _ Hex.Conway.compat_163_2_4

/-- The canonical embedding of GF(167^1) into GF(167^2). -/
noncomputable def embed_167_1_2 :
    Hex.GFq 167 1 Hex.Conway.supportedEntry_167_1 →+*
      Hex.GFq 167 2 Hex.Conway.supportedEntry_167_2 :=
  conwayEmbed 167 1 2 _ _ Hex.Conway.compat_167_1_2

/-- The canonical embedding of GF(167^1) into GF(167^3). -/
noncomputable def embed_167_1_3 :
    Hex.GFq 167 1 Hex.Conway.supportedEntry_167_1 →+*
      Hex.GFq 167 3 Hex.Conway.supportedEntry_167_3 :=
  conwayEmbed 167 1 3 _ _ Hex.Conway.compat_167_1_3

/-- The canonical embedding of GF(167^1) into GF(167^4). -/
noncomputable def embed_167_1_4 :
    Hex.GFq 167 1 Hex.Conway.supportedEntry_167_1 →+*
      Hex.GFq 167 4 Hex.Conway.supportedEntry_167_4 :=
  conwayEmbed 167 1 4 _ _ Hex.Conway.compat_167_1_4

/-- The canonical embedding of GF(167^2) into GF(167^4). -/
noncomputable def embed_167_2_4 :
    Hex.GFq 167 2 Hex.Conway.supportedEntry_167_2 →+*
      Hex.GFq 167 4 Hex.Conway.supportedEntry_167_4 :=
  conwayEmbed 167 2 4 _ _ Hex.Conway.compat_167_2_4

/-- The canonical embedding of GF(173^1) into GF(173^2). -/
noncomputable def embed_173_1_2 :
    Hex.GFq 173 1 Hex.Conway.supportedEntry_173_1 →+*
      Hex.GFq 173 2 Hex.Conway.supportedEntry_173_2 :=
  conwayEmbed 173 1 2 _ _ Hex.Conway.compat_173_1_2

/-- The canonical embedding of GF(173^1) into GF(173^3). -/
noncomputable def embed_173_1_3 :
    Hex.GFq 173 1 Hex.Conway.supportedEntry_173_1 →+*
      Hex.GFq 173 3 Hex.Conway.supportedEntry_173_3 :=
  conwayEmbed 173 1 3 _ _ Hex.Conway.compat_173_1_3

/-- The canonical embedding of GF(173^1) into GF(173^4). -/
noncomputable def embed_173_1_4 :
    Hex.GFq 173 1 Hex.Conway.supportedEntry_173_1 →+*
      Hex.GFq 173 4 Hex.Conway.supportedEntry_173_4 :=
  conwayEmbed 173 1 4 _ _ Hex.Conway.compat_173_1_4

/-- The canonical embedding of GF(173^2) into GF(173^4). -/
noncomputable def embed_173_2_4 :
    Hex.GFq 173 2 Hex.Conway.supportedEntry_173_2 →+*
      Hex.GFq 173 4 Hex.Conway.supportedEntry_173_4 :=
  conwayEmbed 173 2 4 _ _ Hex.Conway.compat_173_2_4

/-- The canonical embedding of GF(179^1) into GF(179^2). -/
noncomputable def embed_179_1_2 :
    Hex.GFq 179 1 Hex.Conway.supportedEntry_179_1 →+*
      Hex.GFq 179 2 Hex.Conway.supportedEntry_179_2 :=
  conwayEmbed 179 1 2 _ _ Hex.Conway.compat_179_1_2

/-- The canonical embedding of GF(179^1) into GF(179^3). -/
noncomputable def embed_179_1_3 :
    Hex.GFq 179 1 Hex.Conway.supportedEntry_179_1 →+*
      Hex.GFq 179 3 Hex.Conway.supportedEntry_179_3 :=
  conwayEmbed 179 1 3 _ _ Hex.Conway.compat_179_1_3

/-- The canonical embedding of GF(179^1) into GF(179^4). -/
noncomputable def embed_179_1_4 :
    Hex.GFq 179 1 Hex.Conway.supportedEntry_179_1 →+*
      Hex.GFq 179 4 Hex.Conway.supportedEntry_179_4 :=
  conwayEmbed 179 1 4 _ _ Hex.Conway.compat_179_1_4

/-- The canonical embedding of GF(179^2) into GF(179^4). -/
noncomputable def embed_179_2_4 :
    Hex.GFq 179 2 Hex.Conway.supportedEntry_179_2 →+*
      Hex.GFq 179 4 Hex.Conway.supportedEntry_179_4 :=
  conwayEmbed 179 2 4 _ _ Hex.Conway.compat_179_2_4

/-- The canonical embedding of GF(181^1) into GF(181^2). -/
noncomputable def embed_181_1_2 :
    Hex.GFq 181 1 Hex.Conway.supportedEntry_181_1 →+*
      Hex.GFq 181 2 Hex.Conway.supportedEntry_181_2 :=
  conwayEmbed 181 1 2 _ _ Hex.Conway.compat_181_1_2

/-- The canonical embedding of GF(181^1) into GF(181^3). -/
noncomputable def embed_181_1_3 :
    Hex.GFq 181 1 Hex.Conway.supportedEntry_181_1 →+*
      Hex.GFq 181 3 Hex.Conway.supportedEntry_181_3 :=
  conwayEmbed 181 1 3 _ _ Hex.Conway.compat_181_1_3

/-- The canonical embedding of GF(181^1) into GF(181^4). -/
noncomputable def embed_181_1_4 :
    Hex.GFq 181 1 Hex.Conway.supportedEntry_181_1 →+*
      Hex.GFq 181 4 Hex.Conway.supportedEntry_181_4 :=
  conwayEmbed 181 1 4 _ _ Hex.Conway.compat_181_1_4

/-- The canonical embedding of GF(181^2) into GF(181^4). -/
noncomputable def embed_181_2_4 :
    Hex.GFq 181 2 Hex.Conway.supportedEntry_181_2 →+*
      Hex.GFq 181 4 Hex.Conway.supportedEntry_181_4 :=
  conwayEmbed 181 2 4 _ _ Hex.Conway.compat_181_2_4

/-- The canonical embedding of GF(191^1) into GF(191^2). -/
noncomputable def embed_191_1_2 :
    Hex.GFq 191 1 Hex.Conway.supportedEntry_191_1 →+*
      Hex.GFq 191 2 Hex.Conway.supportedEntry_191_2 :=
  conwayEmbed 191 1 2 _ _ Hex.Conway.compat_191_1_2

/-- The canonical embedding of GF(191^1) into GF(191^3). -/
noncomputable def embed_191_1_3 :
    Hex.GFq 191 1 Hex.Conway.supportedEntry_191_1 →+*
      Hex.GFq 191 3 Hex.Conway.supportedEntry_191_3 :=
  conwayEmbed 191 1 3 _ _ Hex.Conway.compat_191_1_3

/-- The canonical embedding of GF(191^1) into GF(191^4). -/
noncomputable def embed_191_1_4 :
    Hex.GFq 191 1 Hex.Conway.supportedEntry_191_1 →+*
      Hex.GFq 191 4 Hex.Conway.supportedEntry_191_4 :=
  conwayEmbed 191 1 4 _ _ Hex.Conway.compat_191_1_4

/-- The canonical embedding of GF(191^2) into GF(191^4). -/
noncomputable def embed_191_2_4 :
    Hex.GFq 191 2 Hex.Conway.supportedEntry_191_2 →+*
      Hex.GFq 191 4 Hex.Conway.supportedEntry_191_4 :=
  conwayEmbed 191 2 4 _ _ Hex.Conway.compat_191_2_4

/-- The canonical embedding of GF(193^1) into GF(193^2). -/
noncomputable def embed_193_1_2 :
    Hex.GFq 193 1 Hex.Conway.supportedEntry_193_1 →+*
      Hex.GFq 193 2 Hex.Conway.supportedEntry_193_2 :=
  conwayEmbed 193 1 2 _ _ Hex.Conway.compat_193_1_2

/-- The canonical embedding of GF(193^1) into GF(193^3). -/
noncomputable def embed_193_1_3 :
    Hex.GFq 193 1 Hex.Conway.supportedEntry_193_1 →+*
      Hex.GFq 193 3 Hex.Conway.supportedEntry_193_3 :=
  conwayEmbed 193 1 3 _ _ Hex.Conway.compat_193_1_3

/-- The canonical embedding of GF(193^1) into GF(193^4). -/
noncomputable def embed_193_1_4 :
    Hex.GFq 193 1 Hex.Conway.supportedEntry_193_1 →+*
      Hex.GFq 193 4 Hex.Conway.supportedEntry_193_4 :=
  conwayEmbed 193 1 4 _ _ Hex.Conway.compat_193_1_4

/-- The canonical embedding of GF(193^2) into GF(193^4). -/
noncomputable def embed_193_2_4 :
    Hex.GFq 193 2 Hex.Conway.supportedEntry_193_2 →+*
      Hex.GFq 193 4 Hex.Conway.supportedEntry_193_4 :=
  conwayEmbed 193 2 4 _ _ Hex.Conway.compat_193_2_4

/-- The canonical embedding of GF(197^1) into GF(197^2). -/
noncomputable def embed_197_1_2 :
    Hex.GFq 197 1 Hex.Conway.supportedEntry_197_1 →+*
      Hex.GFq 197 2 Hex.Conway.supportedEntry_197_2 :=
  conwayEmbed 197 1 2 _ _ Hex.Conway.compat_197_1_2

/-- The canonical embedding of GF(197^1) into GF(197^3). -/
noncomputable def embed_197_1_3 :
    Hex.GFq 197 1 Hex.Conway.supportedEntry_197_1 →+*
      Hex.GFq 197 3 Hex.Conway.supportedEntry_197_3 :=
  conwayEmbed 197 1 3 _ _ Hex.Conway.compat_197_1_3

/-- The canonical embedding of GF(197^1) into GF(197^4). -/
noncomputable def embed_197_1_4 :
    Hex.GFq 197 1 Hex.Conway.supportedEntry_197_1 →+*
      Hex.GFq 197 4 Hex.Conway.supportedEntry_197_4 :=
  conwayEmbed 197 1 4 _ _ Hex.Conway.compat_197_1_4

/-- The canonical embedding of GF(197^2) into GF(197^4). -/
noncomputable def embed_197_2_4 :
    Hex.GFq 197 2 Hex.Conway.supportedEntry_197_2 →+*
      Hex.GFq 197 4 Hex.Conway.supportedEntry_197_4 :=
  conwayEmbed 197 2 4 _ _ Hex.Conway.compat_197_2_4

/-- The canonical embedding of GF(199^1) into GF(199^2). -/
noncomputable def embed_199_1_2 :
    Hex.GFq 199 1 Hex.Conway.supportedEntry_199_1 →+*
      Hex.GFq 199 2 Hex.Conway.supportedEntry_199_2 :=
  conwayEmbed 199 1 2 _ _ Hex.Conway.compat_199_1_2

/-- The canonical embedding of GF(199^1) into GF(199^3). -/
noncomputable def embed_199_1_3 :
    Hex.GFq 199 1 Hex.Conway.supportedEntry_199_1 →+*
      Hex.GFq 199 3 Hex.Conway.supportedEntry_199_3 :=
  conwayEmbed 199 1 3 _ _ Hex.Conway.compat_199_1_3

/-- The canonical embedding of GF(199^1) into GF(199^4). -/
noncomputable def embed_199_1_4 :
    Hex.GFq 199 1 Hex.Conway.supportedEntry_199_1 →+*
      Hex.GFq 199 4 Hex.Conway.supportedEntry_199_4 :=
  conwayEmbed 199 1 4 _ _ Hex.Conway.compat_199_1_4

/-- The canonical embedding of GF(199^2) into GF(199^4). -/
noncomputable def embed_199_2_4 :
    Hex.GFq 199 2 Hex.Conway.supportedEntry_199_2 →+*
      Hex.GFq 199 4 Hex.Conway.supportedEntry_199_4 :=
  conwayEmbed 199 2 4 _ _ Hex.Conway.compat_199_2_4

/-- The canonical embedding of GF(211^1) into GF(211^2). -/
noncomputable def embed_211_1_2 :
    Hex.GFq 211 1 Hex.Conway.supportedEntry_211_1 →+*
      Hex.GFq 211 2 Hex.Conway.supportedEntry_211_2 :=
  conwayEmbed 211 1 2 _ _ Hex.Conway.compat_211_1_2

/-- The canonical embedding of GF(211^1) into GF(211^3). -/
noncomputable def embed_211_1_3 :
    Hex.GFq 211 1 Hex.Conway.supportedEntry_211_1 →+*
      Hex.GFq 211 3 Hex.Conway.supportedEntry_211_3 :=
  conwayEmbed 211 1 3 _ _ Hex.Conway.compat_211_1_3

/-- The canonical embedding of GF(211^1) into GF(211^4). -/
noncomputable def embed_211_1_4 :
    Hex.GFq 211 1 Hex.Conway.supportedEntry_211_1 →+*
      Hex.GFq 211 4 Hex.Conway.supportedEntry_211_4 :=
  conwayEmbed 211 1 4 _ _ Hex.Conway.compat_211_1_4

/-- The canonical embedding of GF(211^2) into GF(211^4). -/
noncomputable def embed_211_2_4 :
    Hex.GFq 211 2 Hex.Conway.supportedEntry_211_2 →+*
      Hex.GFq 211 4 Hex.Conway.supportedEntry_211_4 :=
  conwayEmbed 211 2 4 _ _ Hex.Conway.compat_211_2_4

/-- The canonical embedding of GF(223^1) into GF(223^2). -/
noncomputable def embed_223_1_2 :
    Hex.GFq 223 1 Hex.Conway.supportedEntry_223_1 →+*
      Hex.GFq 223 2 Hex.Conway.supportedEntry_223_2 :=
  conwayEmbed 223 1 2 _ _ Hex.Conway.compat_223_1_2

/-- The canonical embedding of GF(223^1) into GF(223^3). -/
noncomputable def embed_223_1_3 :
    Hex.GFq 223 1 Hex.Conway.supportedEntry_223_1 →+*
      Hex.GFq 223 3 Hex.Conway.supportedEntry_223_3 :=
  conwayEmbed 223 1 3 _ _ Hex.Conway.compat_223_1_3

/-- The canonical embedding of GF(223^1) into GF(223^4). -/
noncomputable def embed_223_1_4 :
    Hex.GFq 223 1 Hex.Conway.supportedEntry_223_1 →+*
      Hex.GFq 223 4 Hex.Conway.supportedEntry_223_4 :=
  conwayEmbed 223 1 4 _ _ Hex.Conway.compat_223_1_4

/-- The canonical embedding of GF(223^2) into GF(223^4). -/
noncomputable def embed_223_2_4 :
    Hex.GFq 223 2 Hex.Conway.supportedEntry_223_2 →+*
      Hex.GFq 223 4 Hex.Conway.supportedEntry_223_4 :=
  conwayEmbed 223 2 4 _ _ Hex.Conway.compat_223_2_4

/-- The canonical embedding of GF(227^1) into GF(227^2). -/
noncomputable def embed_227_1_2 :
    Hex.GFq 227 1 Hex.Conway.supportedEntry_227_1 →+*
      Hex.GFq 227 2 Hex.Conway.supportedEntry_227_2 :=
  conwayEmbed 227 1 2 _ _ Hex.Conway.compat_227_1_2

/-- The canonical embedding of GF(227^1) into GF(227^3). -/
noncomputable def embed_227_1_3 :
    Hex.GFq 227 1 Hex.Conway.supportedEntry_227_1 →+*
      Hex.GFq 227 3 Hex.Conway.supportedEntry_227_3 :=
  conwayEmbed 227 1 3 _ _ Hex.Conway.compat_227_1_3

end HexGFqMathlib.Conway
