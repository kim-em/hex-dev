/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

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
