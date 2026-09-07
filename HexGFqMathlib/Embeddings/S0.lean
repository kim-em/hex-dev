/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(2^1) into GF(2^2). -/
noncomputable def embed_2_1_2 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 :=
  conwayEmbed 2 1 2 _ _ Hex.Conway.compat_2_1_2

/-- The canonical embedding of GF(2^1) into GF(2^3). -/
noncomputable def embed_2_1_3 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 :=
  conwayEmbed 2 1 3 _ _ Hex.Conway.compat_2_1_3

/-- The canonical embedding of GF(2^1) into GF(2^4). -/
noncomputable def embed_2_1_4 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 :=
  conwayEmbed 2 1 4 _ _ Hex.Conway.compat_2_1_4

/-- The canonical embedding of GF(2^2) into GF(2^4). -/
noncomputable def embed_2_2_4 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 :=
  conwayEmbed 2 2 4 _ _ Hex.Conway.compat_2_2_4

/-- The canonical embedding of GF(2^1) into GF(2^5). -/
noncomputable def embed_2_1_5 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 5 Hex.Conway.supportedEntry_2_5 :=
  conwayEmbed 2 1 5 _ _ Hex.Conway.compat_2_1_5

/-- The canonical embedding of GF(2^1) into GF(2^6). -/
noncomputable def embed_2_1_6 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 :=
  conwayEmbed 2 1 6 _ _ Hex.Conway.compat_2_1_6

/-- The canonical embedding of GF(2^2) into GF(2^6). -/
noncomputable def embed_2_2_6 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 :=
  conwayEmbed 2 2 6 _ _ Hex.Conway.compat_2_2_6

/-- The canonical embedding of GF(2^3) into GF(2^6). -/
noncomputable def embed_2_3_6 :
    Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 →+*
      Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 :=
  conwayEmbed 2 3 6 _ _ Hex.Conway.compat_2_3_6

/-- The canonical embedding of GF(2^1) into GF(2^7). -/
noncomputable def embed_2_1_7 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 7 Hex.Conway.supportedEntry_2_7 :=
  conwayEmbed 2 1 7 _ _ Hex.Conway.compat_2_1_7

/-- The canonical embedding of GF(2^1) into GF(2^8). -/
noncomputable def embed_2_1_8 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 8 Hex.Conway.supportedEntry_2_8 :=
  conwayEmbed 2 1 8 _ _ Hex.Conway.compat_2_1_8

/-- The canonical embedding of GF(2^2) into GF(2^8). -/
noncomputable def embed_2_2_8 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 8 Hex.Conway.supportedEntry_2_8 :=
  conwayEmbed 2 2 8 _ _ Hex.Conway.compat_2_2_8

/-- The canonical embedding of GF(2^4) into GF(2^8). -/
noncomputable def embed_2_4_8 :
    Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 →+*
      Hex.GFq 2 8 Hex.Conway.supportedEntry_2_8 :=
  conwayEmbed 2 4 8 _ _ Hex.Conway.compat_2_4_8

/-- The canonical embedding of GF(2^1) into GF(2^9). -/
noncomputable def embed_2_1_9 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 9 Hex.Conway.supportedEntry_2_9 :=
  conwayEmbed 2 1 9 _ _ Hex.Conway.compat_2_1_9

/-- The canonical embedding of GF(2^3) into GF(2^9). -/
noncomputable def embed_2_3_9 :
    Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 →+*
      Hex.GFq 2 9 Hex.Conway.supportedEntry_2_9 :=
  conwayEmbed 2 3 9 _ _ Hex.Conway.compat_2_3_9

/-- The canonical embedding of GF(2^1) into GF(2^10). -/
noncomputable def embed_2_1_10 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 10 Hex.Conway.supportedEntry_2_10 :=
  conwayEmbed 2 1 10 _ _ Hex.Conway.compat_2_1_10

/-- The canonical embedding of GF(2^2) into GF(2^10). -/
noncomputable def embed_2_2_10 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 10 Hex.Conway.supportedEntry_2_10 :=
  conwayEmbed 2 2 10 _ _ Hex.Conway.compat_2_2_10

/-- The canonical embedding of GF(2^5) into GF(2^10). -/
noncomputable def embed_2_5_10 :
    Hex.GFq 2 5 Hex.Conway.supportedEntry_2_5 →+*
      Hex.GFq 2 10 Hex.Conway.supportedEntry_2_10 :=
  conwayEmbed 2 5 10 _ _ Hex.Conway.compat_2_5_10

/-- The canonical embedding of GF(2^1) into GF(2^11). -/
noncomputable def embed_2_1_11 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 11 Hex.Conway.supportedEntry_2_11 :=
  conwayEmbed 2 1 11 _ _ Hex.Conway.compat_2_1_11

/-- The canonical embedding of GF(2^1) into GF(2^12). -/
noncomputable def embed_2_1_12 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 12 Hex.Conway.supportedEntry_2_12 :=
  conwayEmbed 2 1 12 _ _ Hex.Conway.compat_2_1_12

/-- The canonical embedding of GF(2^2) into GF(2^12). -/
noncomputable def embed_2_2_12 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 12 Hex.Conway.supportedEntry_2_12 :=
  conwayEmbed 2 2 12 _ _ Hex.Conway.compat_2_2_12

/-- The canonical embedding of GF(2^3) into GF(2^12). -/
noncomputable def embed_2_3_12 :
    Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 →+*
      Hex.GFq 2 12 Hex.Conway.supportedEntry_2_12 :=
  conwayEmbed 2 3 12 _ _ Hex.Conway.compat_2_3_12

/-- The canonical embedding of GF(2^4) into GF(2^12). -/
noncomputable def embed_2_4_12 :
    Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 →+*
      Hex.GFq 2 12 Hex.Conway.supportedEntry_2_12 :=
  conwayEmbed 2 4 12 _ _ Hex.Conway.compat_2_4_12

/-- The canonical embedding of GF(2^6) into GF(2^12). -/
noncomputable def embed_2_6_12 :
    Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 →+*
      Hex.GFq 2 12 Hex.Conway.supportedEntry_2_12 :=
  conwayEmbed 2 6 12 _ _ Hex.Conway.compat_2_6_12

/-- The canonical embedding of GF(2^1) into GF(2^13). -/
noncomputable def embed_2_1_13 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 13 Hex.Conway.supportedEntry_2_13 :=
  conwayEmbed 2 1 13 _ _ Hex.Conway.compat_2_1_13

/-- The canonical embedding of GF(2^1) into GF(2^14). -/
noncomputable def embed_2_1_14 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 14 Hex.Conway.supportedEntry_2_14 :=
  conwayEmbed 2 1 14 _ _ Hex.Conway.compat_2_1_14

/-- The canonical embedding of GF(2^2) into GF(2^14). -/
noncomputable def embed_2_2_14 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 14 Hex.Conway.supportedEntry_2_14 :=
  conwayEmbed 2 2 14 _ _ Hex.Conway.compat_2_2_14

/-- The canonical embedding of GF(2^7) into GF(2^14). -/
noncomputable def embed_2_7_14 :
    Hex.GFq 2 7 Hex.Conway.supportedEntry_2_7 →+*
      Hex.GFq 2 14 Hex.Conway.supportedEntry_2_14 :=
  conwayEmbed 2 7 14 _ _ Hex.Conway.compat_2_7_14

/-- The canonical embedding of GF(2^1) into GF(2^15). -/
noncomputable def embed_2_1_15 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 15 Hex.Conway.supportedEntry_2_15 :=
  conwayEmbed 2 1 15 _ _ Hex.Conway.compat_2_1_15

/-- The canonical embedding of GF(2^3) into GF(2^15). -/
noncomputable def embed_2_3_15 :
    Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 →+*
      Hex.GFq 2 15 Hex.Conway.supportedEntry_2_15 :=
  conwayEmbed 2 3 15 _ _ Hex.Conway.compat_2_3_15

/-- The canonical embedding of GF(2^5) into GF(2^15). -/
noncomputable def embed_2_5_15 :
    Hex.GFq 2 5 Hex.Conway.supportedEntry_2_5 →+*
      Hex.GFq 2 15 Hex.Conway.supportedEntry_2_15 :=
  conwayEmbed 2 5 15 _ _ Hex.Conway.compat_2_5_15

/-- The canonical embedding of GF(2^1) into GF(2^16). -/
noncomputable def embed_2_1_16 :
    Hex.GFq 2 1 Hex.Conway.supportedEntry_2_1 →+*
      Hex.GFq 2 16 Hex.Conway.supportedEntry_2_16 :=
  conwayEmbed 2 1 16 _ _ Hex.Conway.compat_2_1_16

/-- The canonical embedding of GF(2^2) into GF(2^16). -/
noncomputable def embed_2_2_16 :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 16 Hex.Conway.supportedEntry_2_16 :=
  conwayEmbed 2 2 16 _ _ Hex.Conway.compat_2_2_16

/-- The canonical embedding of GF(2^4) into GF(2^16). -/
noncomputable def embed_2_4_16 :
    Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 →+*
      Hex.GFq 2 16 Hex.Conway.supportedEntry_2_16 :=
  conwayEmbed 2 4 16 _ _ Hex.Conway.compat_2_4_16

/-- The canonical embedding of GF(2^8) into GF(2^16). -/
noncomputable def embed_2_8_16 :
    Hex.GFq 2 8 Hex.Conway.supportedEntry_2_8 →+*
      Hex.GFq 2 16 Hex.Conway.supportedEntry_2_16 :=
  conwayEmbed 2 8 16 _ _ Hex.Conway.compat_2_8_16

/-- The canonical embedding of GF(3^1) into GF(3^2). -/
noncomputable def embed_3_1_2 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 2 Hex.Conway.supportedEntry_3_2 :=
  conwayEmbed 3 1 2 _ _ Hex.Conway.compat_3_1_2

/-- The canonical embedding of GF(3^1) into GF(3^3). -/
noncomputable def embed_3_1_3 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 3 Hex.Conway.supportedEntry_3_3 :=
  conwayEmbed 3 1 3 _ _ Hex.Conway.compat_3_1_3

/-- The canonical embedding of GF(3^1) into GF(3^4). -/
noncomputable def embed_3_1_4 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 4 Hex.Conway.supportedEntry_3_4 :=
  conwayEmbed 3 1 4 _ _ Hex.Conway.compat_3_1_4

/-- The canonical embedding of GF(3^2) into GF(3^4). -/
noncomputable def embed_3_2_4 :
    Hex.GFq 3 2 Hex.Conway.supportedEntry_3_2 →+*
      Hex.GFq 3 4 Hex.Conway.supportedEntry_3_4 :=
  conwayEmbed 3 2 4 _ _ Hex.Conway.compat_3_2_4

/-- The canonical embedding of GF(3^1) into GF(3^5). -/
noncomputable def embed_3_1_5 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 5 Hex.Conway.supportedEntry_3_5 :=
  conwayEmbed 3 1 5 _ _ Hex.Conway.compat_3_1_5

/-- The canonical embedding of GF(3^1) into GF(3^6). -/
noncomputable def embed_3_1_6 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 6 Hex.Conway.supportedEntry_3_6 :=
  conwayEmbed 3 1 6 _ _ Hex.Conway.compat_3_1_6

/-- The canonical embedding of GF(3^2) into GF(3^6). -/
noncomputable def embed_3_2_6 :
    Hex.GFq 3 2 Hex.Conway.supportedEntry_3_2 →+*
      Hex.GFq 3 6 Hex.Conway.supportedEntry_3_6 :=
  conwayEmbed 3 2 6 _ _ Hex.Conway.compat_3_2_6

/-- The canonical embedding of GF(3^3) into GF(3^6). -/
noncomputable def embed_3_3_6 :
    Hex.GFq 3 3 Hex.Conway.supportedEntry_3_3 →+*
      Hex.GFq 3 6 Hex.Conway.supportedEntry_3_6 :=
  conwayEmbed 3 3 6 _ _ Hex.Conway.compat_3_3_6

/-- The canonical embedding of GF(3^1) into GF(3^7). -/
noncomputable def embed_3_1_7 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 7 Hex.Conway.supportedEntry_3_7 :=
  conwayEmbed 3 1 7 _ _ Hex.Conway.compat_3_1_7

/-- The canonical embedding of GF(3^1) into GF(3^8). -/
noncomputable def embed_3_1_8 :
    Hex.GFq 3 1 Hex.Conway.supportedEntry_3_1 →+*
      Hex.GFq 3 8 Hex.Conway.supportedEntry_3_8 :=
  conwayEmbed 3 1 8 _ _ Hex.Conway.compat_3_1_8

/-- The canonical embedding of GF(3^2) into GF(3^8). -/
noncomputable def embed_3_2_8 :
    Hex.GFq 3 2 Hex.Conway.supportedEntry_3_2 →+*
      Hex.GFq 3 8 Hex.Conway.supportedEntry_3_8 :=
  conwayEmbed 3 2 8 _ _ Hex.Conway.compat_3_2_8

/-- The canonical embedding of GF(3^4) into GF(3^8). -/
noncomputable def embed_3_4_8 :
    Hex.GFq 3 4 Hex.Conway.supportedEntry_3_4 →+*
      Hex.GFq 3 8 Hex.Conway.supportedEntry_3_8 :=
  conwayEmbed 3 4 8 _ _ Hex.Conway.compat_3_4_8

/-- The canonical embedding of GF(5^1) into GF(5^2). -/
noncomputable def embed_5_1_2 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 2 Hex.Conway.supportedEntry_5_2 :=
  conwayEmbed 5 1 2 _ _ Hex.Conway.compat_5_1_2

/-- The canonical embedding of GF(5^1) into GF(5^3). -/
noncomputable def embed_5_1_3 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 3 Hex.Conway.supportedEntry_5_3 :=
  conwayEmbed 5 1 3 _ _ Hex.Conway.compat_5_1_3

/-- The canonical embedding of GF(5^1) into GF(5^4). -/
noncomputable def embed_5_1_4 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 4 Hex.Conway.supportedEntry_5_4 :=
  conwayEmbed 5 1 4 _ _ Hex.Conway.compat_5_1_4

/-- The canonical embedding of GF(5^2) into GF(5^4). -/
noncomputable def embed_5_2_4 :
    Hex.GFq 5 2 Hex.Conway.supportedEntry_5_2 →+*
      Hex.GFq 5 4 Hex.Conway.supportedEntry_5_4 :=
  conwayEmbed 5 2 4 _ _ Hex.Conway.compat_5_2_4

/-- The canonical embedding of GF(5^1) into GF(5^5). -/
noncomputable def embed_5_1_5 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 5 Hex.Conway.supportedEntry_5_5 :=
  conwayEmbed 5 1 5 _ _ Hex.Conway.compat_5_1_5

/-- The canonical embedding of GF(5^1) into GF(5^6). -/
noncomputable def embed_5_1_6 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 6 Hex.Conway.supportedEntry_5_6 :=
  conwayEmbed 5 1 6 _ _ Hex.Conway.compat_5_1_6

/-- The canonical embedding of GF(5^2) into GF(5^6). -/
noncomputable def embed_5_2_6 :
    Hex.GFq 5 2 Hex.Conway.supportedEntry_5_2 →+*
      Hex.GFq 5 6 Hex.Conway.supportedEntry_5_6 :=
  conwayEmbed 5 2 6 _ _ Hex.Conway.compat_5_2_6

/-- The canonical embedding of GF(5^3) into GF(5^6). -/
noncomputable def embed_5_3_6 :
    Hex.GFq 5 3 Hex.Conway.supportedEntry_5_3 →+*
      Hex.GFq 5 6 Hex.Conway.supportedEntry_5_6 :=
  conwayEmbed 5 3 6 _ _ Hex.Conway.compat_5_3_6

/-- The canonical embedding of GF(5^1) into GF(5^7). -/
noncomputable def embed_5_1_7 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 7 Hex.Conway.supportedEntry_5_7 :=
  conwayEmbed 5 1 7 _ _ Hex.Conway.compat_5_1_7

/-- The canonical embedding of GF(5^1) into GF(5^8). -/
noncomputable def embed_5_1_8 :
    Hex.GFq 5 1 Hex.Conway.supportedEntry_5_1 →+*
      Hex.GFq 5 8 Hex.Conway.supportedEntry_5_8 :=
  conwayEmbed 5 1 8 _ _ Hex.Conway.compat_5_1_8

/-- The canonical embedding of GF(5^2) into GF(5^8). -/
noncomputable def embed_5_2_8 :
    Hex.GFq 5 2 Hex.Conway.supportedEntry_5_2 →+*
      Hex.GFq 5 8 Hex.Conway.supportedEntry_5_8 :=
  conwayEmbed 5 2 8 _ _ Hex.Conway.compat_5_2_8

/-- The canonical embedding of GF(5^4) into GF(5^8). -/
noncomputable def embed_5_4_8 :
    Hex.GFq 5 4 Hex.Conway.supportedEntry_5_4 →+*
      Hex.GFq 5 8 Hex.Conway.supportedEntry_5_8 :=
  conwayEmbed 5 4 8 _ _ Hex.Conway.compat_5_4_8

/-- The canonical embedding of GF(7^1) into GF(7^2). -/
noncomputable def embed_7_1_2 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 2 Hex.Conway.supportedEntry_7_2 :=
  conwayEmbed 7 1 2 _ _ Hex.Conway.compat_7_1_2

/-- The canonical embedding of GF(7^1) into GF(7^3). -/
noncomputable def embed_7_1_3 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 3 Hex.Conway.supportedEntry_7_3 :=
  conwayEmbed 7 1 3 _ _ Hex.Conway.compat_7_1_3

/-- The canonical embedding of GF(7^1) into GF(7^4). -/
noncomputable def embed_7_1_4 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 4 Hex.Conway.supportedEntry_7_4 :=
  conwayEmbed 7 1 4 _ _ Hex.Conway.compat_7_1_4

/-- The canonical embedding of GF(7^2) into GF(7^4). -/
noncomputable def embed_7_2_4 :
    Hex.GFq 7 2 Hex.Conway.supportedEntry_7_2 →+*
      Hex.GFq 7 4 Hex.Conway.supportedEntry_7_4 :=
  conwayEmbed 7 2 4 _ _ Hex.Conway.compat_7_2_4

/-- The canonical embedding of GF(7^1) into GF(7^5). -/
noncomputable def embed_7_1_5 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 5 Hex.Conway.supportedEntry_7_5 :=
  conwayEmbed 7 1 5 _ _ Hex.Conway.compat_7_1_5

/-- The canonical embedding of GF(7^1) into GF(7^6). -/
noncomputable def embed_7_1_6 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 6 Hex.Conway.supportedEntry_7_6 :=
  conwayEmbed 7 1 6 _ _ Hex.Conway.compat_7_1_6

/-- The canonical embedding of GF(7^2) into GF(7^6). -/
noncomputable def embed_7_2_6 :
    Hex.GFq 7 2 Hex.Conway.supportedEntry_7_2 →+*
      Hex.GFq 7 6 Hex.Conway.supportedEntry_7_6 :=
  conwayEmbed 7 2 6 _ _ Hex.Conway.compat_7_2_6

/-- The canonical embedding of GF(7^3) into GF(7^6). -/
noncomputable def embed_7_3_6 :
    Hex.GFq 7 3 Hex.Conway.supportedEntry_7_3 →+*
      Hex.GFq 7 6 Hex.Conway.supportedEntry_7_6 :=
  conwayEmbed 7 3 6 _ _ Hex.Conway.compat_7_3_6

/-- The canonical embedding of GF(7^1) into GF(7^7). -/
noncomputable def embed_7_1_7 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 7 Hex.Conway.supportedEntry_7_7 :=
  conwayEmbed 7 1 7 _ _ Hex.Conway.compat_7_1_7

/-- The canonical embedding of GF(7^1) into GF(7^8). -/
noncomputable def embed_7_1_8 :
    Hex.GFq 7 1 Hex.Conway.supportedEntry_7_1 →+*
      Hex.GFq 7 8 Hex.Conway.supportedEntry_7_8 :=
  conwayEmbed 7 1 8 _ _ Hex.Conway.compat_7_1_8

/-- The canonical embedding of GF(7^2) into GF(7^8). -/
noncomputable def embed_7_2_8 :
    Hex.GFq 7 2 Hex.Conway.supportedEntry_7_2 →+*
      Hex.GFq 7 8 Hex.Conway.supportedEntry_7_8 :=
  conwayEmbed 7 2 8 _ _ Hex.Conway.compat_7_2_8

/-- The canonical embedding of GF(7^4) into GF(7^8). -/
noncomputable def embed_7_4_8 :
    Hex.GFq 7 4 Hex.Conway.supportedEntry_7_4 →+*
      Hex.GFq 7 8 Hex.Conway.supportedEntry_7_8 :=
  conwayEmbed 7 4 8 _ _ Hex.Conway.compat_7_4_8

/-- The canonical embedding of GF(11^1) into GF(11^2). -/
noncomputable def embed_11_1_2 :
    Hex.GFq 11 1 Hex.Conway.supportedEntry_11_1 →+*
      Hex.GFq 11 2 Hex.Conway.supportedEntry_11_2 :=
  conwayEmbed 11 1 2 _ _ Hex.Conway.compat_11_1_2

/-- The canonical embedding of GF(11^1) into GF(11^3). -/
noncomputable def embed_11_1_3 :
    Hex.GFq 11 1 Hex.Conway.supportedEntry_11_1 →+*
      Hex.GFq 11 3 Hex.Conway.supportedEntry_11_3 :=
  conwayEmbed 11 1 3 _ _ Hex.Conway.compat_11_1_3

/-- The canonical embedding of GF(11^1) into GF(11^4). -/
noncomputable def embed_11_1_4 :
    Hex.GFq 11 1 Hex.Conway.supportedEntry_11_1 →+*
      Hex.GFq 11 4 Hex.Conway.supportedEntry_11_4 :=
  conwayEmbed 11 1 4 _ _ Hex.Conway.compat_11_1_4

/-- The canonical embedding of GF(11^2) into GF(11^4). -/
noncomputable def embed_11_2_4 :
    Hex.GFq 11 2 Hex.Conway.supportedEntry_11_2 →+*
      Hex.GFq 11 4 Hex.Conway.supportedEntry_11_4 :=
  conwayEmbed 11 2 4 _ _ Hex.Conway.compat_11_2_4

/-- The canonical embedding of GF(11^1) into GF(11^5). -/
noncomputable def embed_11_1_5 :
    Hex.GFq 11 1 Hex.Conway.supportedEntry_11_1 →+*
      Hex.GFq 11 5 Hex.Conway.supportedEntry_11_5 :=
  conwayEmbed 11 1 5 _ _ Hex.Conway.compat_11_1_5

/-- The canonical embedding of GF(11^1) into GF(11^6). -/
noncomputable def embed_11_1_6 :
    Hex.GFq 11 1 Hex.Conway.supportedEntry_11_1 →+*
      Hex.GFq 11 6 Hex.Conway.supportedEntry_11_6 :=
  conwayEmbed 11 1 6 _ _ Hex.Conway.compat_11_1_6

/-- The canonical embedding of GF(11^2) into GF(11^6). -/
noncomputable def embed_11_2_6 :
    Hex.GFq 11 2 Hex.Conway.supportedEntry_11_2 →+*
      Hex.GFq 11 6 Hex.Conway.supportedEntry_11_6 :=
  conwayEmbed 11 2 6 _ _ Hex.Conway.compat_11_2_6

/-- The canonical embedding of GF(11^3) into GF(11^6). -/
noncomputable def embed_11_3_6 :
    Hex.GFq 11 3 Hex.Conway.supportedEntry_11_3 →+*
      Hex.GFq 11 6 Hex.Conway.supportedEntry_11_6 :=
  conwayEmbed 11 3 6 _ _ Hex.Conway.compat_11_3_6

/-- The canonical embedding of GF(13^1) into GF(13^2). -/
noncomputable def embed_13_1_2 :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 2 Hex.Conway.supportedEntry_13_2 :=
  conwayEmbed 13 1 2 _ _ Hex.Conway.compat_13_1_2

/-- The canonical embedding of GF(13^1) into GF(13^3). -/
noncomputable def embed_13_1_3 :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 3 Hex.Conway.supportedEntry_13_3 :=
  conwayEmbed 13 1 3 _ _ Hex.Conway.compat_13_1_3

/-- The canonical embedding of GF(13^1) into GF(13^4). -/
noncomputable def embed_13_1_4 :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 4 Hex.Conway.supportedEntry_13_4 :=
  conwayEmbed 13 1 4 _ _ Hex.Conway.compat_13_1_4

/-- The canonical embedding of GF(13^2) into GF(13^4). -/
noncomputable def embed_13_2_4 :
    Hex.GFq 13 2 Hex.Conway.supportedEntry_13_2 →+*
      Hex.GFq 13 4 Hex.Conway.supportedEntry_13_4 :=
  conwayEmbed 13 2 4 _ _ Hex.Conway.compat_13_2_4

/-- The canonical embedding of GF(13^1) into GF(13^5). -/
noncomputable def embed_13_1_5 :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 5 Hex.Conway.supportedEntry_13_5 :=
  conwayEmbed 13 1 5 _ _ Hex.Conway.compat_13_1_5

/-- The canonical embedding of GF(13^1) into GF(13^6). -/
noncomputable def embed_13_1_6 :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 6 Hex.Conway.supportedEntry_13_6 :=
  conwayEmbed 13 1 6 _ _ Hex.Conway.compat_13_1_6

/-- The canonical embedding of GF(13^2) into GF(13^6). -/
noncomputable def embed_13_2_6 :
    Hex.GFq 13 2 Hex.Conway.supportedEntry_13_2 →+*
      Hex.GFq 13 6 Hex.Conway.supportedEntry_13_6 :=
  conwayEmbed 13 2 6 _ _ Hex.Conway.compat_13_2_6

/-- The canonical embedding of GF(13^3) into GF(13^6). -/
noncomputable def embed_13_3_6 :
    Hex.GFq 13 3 Hex.Conway.supportedEntry_13_3 →+*
      Hex.GFq 13 6 Hex.Conway.supportedEntry_13_6 :=
  conwayEmbed 13 3 6 _ _ Hex.Conway.compat_13_3_6

/-- The canonical embedding of GF(17^1) into GF(17^2). -/
noncomputable def embed_17_1_2 :
    Hex.GFq 17 1 Hex.Conway.supportedEntry_17_1 →+*
      Hex.GFq 17 2 Hex.Conway.supportedEntry_17_2 :=
  conwayEmbed 17 1 2 _ _ Hex.Conway.compat_17_1_2

/-- The canonical embedding of GF(17^1) into GF(17^3). -/
noncomputable def embed_17_1_3 :
    Hex.GFq 17 1 Hex.Conway.supportedEntry_17_1 →+*
      Hex.GFq 17 3 Hex.Conway.supportedEntry_17_3 :=
  conwayEmbed 17 1 3 _ _ Hex.Conway.compat_17_1_3

/-- The canonical embedding of GF(17^1) into GF(17^4). -/
noncomputable def embed_17_1_4 :
    Hex.GFq 17 1 Hex.Conway.supportedEntry_17_1 →+*
      Hex.GFq 17 4 Hex.Conway.supportedEntry_17_4 :=
  conwayEmbed 17 1 4 _ _ Hex.Conway.compat_17_1_4

/-- The canonical embedding of GF(17^2) into GF(17^4). -/
noncomputable def embed_17_2_4 :
    Hex.GFq 17 2 Hex.Conway.supportedEntry_17_2 →+*
      Hex.GFq 17 4 Hex.Conway.supportedEntry_17_4 :=
  conwayEmbed 17 2 4 _ _ Hex.Conway.compat_17_2_4

/-- The canonical embedding of GF(19^1) into GF(19^2). -/
noncomputable def embed_19_1_2 :
    Hex.GFq 19 1 Hex.Conway.supportedEntry_19_1 →+*
      Hex.GFq 19 2 Hex.Conway.supportedEntry_19_2 :=
  conwayEmbed 19 1 2 _ _ Hex.Conway.compat_19_1_2

/-- The canonical embedding of GF(19^1) into GF(19^3). -/
noncomputable def embed_19_1_3 :
    Hex.GFq 19 1 Hex.Conway.supportedEntry_19_1 →+*
      Hex.GFq 19 3 Hex.Conway.supportedEntry_19_3 :=
  conwayEmbed 19 1 3 _ _ Hex.Conway.compat_19_1_3

/-- The canonical embedding of GF(19^1) into GF(19^4). -/
noncomputable def embed_19_1_4 :
    Hex.GFq 19 1 Hex.Conway.supportedEntry_19_1 →+*
      Hex.GFq 19 4 Hex.Conway.supportedEntry_19_4 :=
  conwayEmbed 19 1 4 _ _ Hex.Conway.compat_19_1_4

/-- The canonical embedding of GF(19^2) into GF(19^4). -/
noncomputable def embed_19_2_4 :
    Hex.GFq 19 2 Hex.Conway.supportedEntry_19_2 →+*
      Hex.GFq 19 4 Hex.Conway.supportedEntry_19_4 :=
  conwayEmbed 19 2 4 _ _ Hex.Conway.compat_19_2_4

/-- The canonical embedding of GF(23^1) into GF(23^2). -/
noncomputable def embed_23_1_2 :
    Hex.GFq 23 1 Hex.Conway.supportedEntry_23_1 →+*
      Hex.GFq 23 2 Hex.Conway.supportedEntry_23_2 :=
  conwayEmbed 23 1 2 _ _ Hex.Conway.compat_23_1_2

/-- The canonical embedding of GF(23^1) into GF(23^3). -/
noncomputable def embed_23_1_3 :
    Hex.GFq 23 1 Hex.Conway.supportedEntry_23_1 →+*
      Hex.GFq 23 3 Hex.Conway.supportedEntry_23_3 :=
  conwayEmbed 23 1 3 _ _ Hex.Conway.compat_23_1_3

/-- The canonical embedding of GF(23^1) into GF(23^4). -/
noncomputable def embed_23_1_4 :
    Hex.GFq 23 1 Hex.Conway.supportedEntry_23_1 →+*
      Hex.GFq 23 4 Hex.Conway.supportedEntry_23_4 :=
  conwayEmbed 23 1 4 _ _ Hex.Conway.compat_23_1_4

/-- The canonical embedding of GF(23^2) into GF(23^4). -/
noncomputable def embed_23_2_4 :
    Hex.GFq 23 2 Hex.Conway.supportedEntry_23_2 →+*
      Hex.GFq 23 4 Hex.Conway.supportedEntry_23_4 :=
  conwayEmbed 23 2 4 _ _ Hex.Conway.compat_23_2_4

/-- The canonical embedding of GF(29^1) into GF(29^2). -/
noncomputable def embed_29_1_2 :
    Hex.GFq 29 1 Hex.Conway.supportedEntry_29_1 →+*
      Hex.GFq 29 2 Hex.Conway.supportedEntry_29_2 :=
  conwayEmbed 29 1 2 _ _ Hex.Conway.compat_29_1_2

/-- The canonical embedding of GF(29^1) into GF(29^3). -/
noncomputable def embed_29_1_3 :
    Hex.GFq 29 1 Hex.Conway.supportedEntry_29_1 →+*
      Hex.GFq 29 3 Hex.Conway.supportedEntry_29_3 :=
  conwayEmbed 29 1 3 _ _ Hex.Conway.compat_29_1_3

/-- The canonical embedding of GF(29^1) into GF(29^4). -/
noncomputable def embed_29_1_4 :
    Hex.GFq 29 1 Hex.Conway.supportedEntry_29_1 →+*
      Hex.GFq 29 4 Hex.Conway.supportedEntry_29_4 :=
  conwayEmbed 29 1 4 _ _ Hex.Conway.compat_29_1_4

/-- The canonical embedding of GF(29^2) into GF(29^4). -/
noncomputable def embed_29_2_4 :
    Hex.GFq 29 2 Hex.Conway.supportedEntry_29_2 →+*
      Hex.GFq 29 4 Hex.Conway.supportedEntry_29_4 :=
  conwayEmbed 29 2 4 _ _ Hex.Conway.compat_29_2_4

/-- The canonical embedding of GF(31^1) into GF(31^2). -/
noncomputable def embed_31_1_2 :
    Hex.GFq 31 1 Hex.Conway.supportedEntry_31_1 →+*
      Hex.GFq 31 2 Hex.Conway.supportedEntry_31_2 :=
  conwayEmbed 31 1 2 _ _ Hex.Conway.compat_31_1_2

/-- The canonical embedding of GF(31^1) into GF(31^3). -/
noncomputable def embed_31_1_3 :
    Hex.GFq 31 1 Hex.Conway.supportedEntry_31_1 →+*
      Hex.GFq 31 3 Hex.Conway.supportedEntry_31_3 :=
  conwayEmbed 31 1 3 _ _ Hex.Conway.compat_31_1_3

/-- The canonical embedding of GF(31^1) into GF(31^4). -/
noncomputable def embed_31_1_4 :
    Hex.GFq 31 1 Hex.Conway.supportedEntry_31_1 →+*
      Hex.GFq 31 4 Hex.Conway.supportedEntry_31_4 :=
  conwayEmbed 31 1 4 _ _ Hex.Conway.compat_31_1_4

/-- The canonical embedding of GF(31^2) into GF(31^4). -/
noncomputable def embed_31_2_4 :
    Hex.GFq 31 2 Hex.Conway.supportedEntry_31_2 →+*
      Hex.GFq 31 4 Hex.Conway.supportedEntry_31_4 :=
  conwayEmbed 31 2 4 _ _ Hex.Conway.compat_31_2_4

/-- The canonical embedding of GF(37^1) into GF(37^2). -/
noncomputable def embed_37_1_2 :
    Hex.GFq 37 1 Hex.Conway.supportedEntry_37_1 →+*
      Hex.GFq 37 2 Hex.Conway.supportedEntry_37_2 :=
  conwayEmbed 37 1 2 _ _ Hex.Conway.compat_37_1_2

/-- The canonical embedding of GF(37^1) into GF(37^3). -/
noncomputable def embed_37_1_3 :
    Hex.GFq 37 1 Hex.Conway.supportedEntry_37_1 →+*
      Hex.GFq 37 3 Hex.Conway.supportedEntry_37_3 :=
  conwayEmbed 37 1 3 _ _ Hex.Conway.compat_37_1_3

/-- The canonical embedding of GF(37^1) into GF(37^4). -/
noncomputable def embed_37_1_4 :
    Hex.GFq 37 1 Hex.Conway.supportedEntry_37_1 →+*
      Hex.GFq 37 4 Hex.Conway.supportedEntry_37_4 :=
  conwayEmbed 37 1 4 _ _ Hex.Conway.compat_37_1_4

/-- The canonical embedding of GF(37^2) into GF(37^4). -/
noncomputable def embed_37_2_4 :
    Hex.GFq 37 2 Hex.Conway.supportedEntry_37_2 →+*
      Hex.GFq 37 4 Hex.Conway.supportedEntry_37_4 :=
  conwayEmbed 37 2 4 _ _ Hex.Conway.compat_37_2_4

/-- The canonical embedding of GF(41^1) into GF(41^2). -/
noncomputable def embed_41_1_2 :
    Hex.GFq 41 1 Hex.Conway.supportedEntry_41_1 →+*
      Hex.GFq 41 2 Hex.Conway.supportedEntry_41_2 :=
  conwayEmbed 41 1 2 _ _ Hex.Conway.compat_41_1_2

/-- The canonical embedding of GF(41^1) into GF(41^3). -/
noncomputable def embed_41_1_3 :
    Hex.GFq 41 1 Hex.Conway.supportedEntry_41_1 →+*
      Hex.GFq 41 3 Hex.Conway.supportedEntry_41_3 :=
  conwayEmbed 41 1 3 _ _ Hex.Conway.compat_41_1_3

/-- The canonical embedding of GF(41^1) into GF(41^4). -/
noncomputable def embed_41_1_4 :
    Hex.GFq 41 1 Hex.Conway.supportedEntry_41_1 →+*
      Hex.GFq 41 4 Hex.Conway.supportedEntry_41_4 :=
  conwayEmbed 41 1 4 _ _ Hex.Conway.compat_41_1_4

/-- The canonical embedding of GF(41^2) into GF(41^4). -/
noncomputable def embed_41_2_4 :
    Hex.GFq 41 2 Hex.Conway.supportedEntry_41_2 →+*
      Hex.GFq 41 4 Hex.Conway.supportedEntry_41_4 :=
  conwayEmbed 41 2 4 _ _ Hex.Conway.compat_41_2_4

/-- The canonical embedding of GF(43^1) into GF(43^2). -/
noncomputable def embed_43_1_2 :
    Hex.GFq 43 1 Hex.Conway.supportedEntry_43_1 →+*
      Hex.GFq 43 2 Hex.Conway.supportedEntry_43_2 :=
  conwayEmbed 43 1 2 _ _ Hex.Conway.compat_43_1_2

/-- The canonical embedding of GF(43^1) into GF(43^3). -/
noncomputable def embed_43_1_3 :
    Hex.GFq 43 1 Hex.Conway.supportedEntry_43_1 →+*
      Hex.GFq 43 3 Hex.Conway.supportedEntry_43_3 :=
  conwayEmbed 43 1 3 _ _ Hex.Conway.compat_43_1_3

/-- The canonical embedding of GF(43^1) into GF(43^4). -/
noncomputable def embed_43_1_4 :
    Hex.GFq 43 1 Hex.Conway.supportedEntry_43_1 →+*
      Hex.GFq 43 4 Hex.Conway.supportedEntry_43_4 :=
  conwayEmbed 43 1 4 _ _ Hex.Conway.compat_43_1_4

/-- The canonical embedding of GF(43^2) into GF(43^4). -/
noncomputable def embed_43_2_4 :
    Hex.GFq 43 2 Hex.Conway.supportedEntry_43_2 →+*
      Hex.GFq 43 4 Hex.Conway.supportedEntry_43_4 :=
  conwayEmbed 43 2 4 _ _ Hex.Conway.compat_43_2_4

/-- The canonical embedding of GF(47^1) into GF(47^2). -/
noncomputable def embed_47_1_2 :
    Hex.GFq 47 1 Hex.Conway.supportedEntry_47_1 →+*
      Hex.GFq 47 2 Hex.Conway.supportedEntry_47_2 :=
  conwayEmbed 47 1 2 _ _ Hex.Conway.compat_47_1_2

/-- The canonical embedding of GF(47^1) into GF(47^3). -/
noncomputable def embed_47_1_3 :
    Hex.GFq 47 1 Hex.Conway.supportedEntry_47_1 →+*
      Hex.GFq 47 3 Hex.Conway.supportedEntry_47_3 :=
  conwayEmbed 47 1 3 _ _ Hex.Conway.compat_47_1_3

/-- The canonical embedding of GF(47^1) into GF(47^4). -/
noncomputable def embed_47_1_4 :
    Hex.GFq 47 1 Hex.Conway.supportedEntry_47_1 →+*
      Hex.GFq 47 4 Hex.Conway.supportedEntry_47_4 :=
  conwayEmbed 47 1 4 _ _ Hex.Conway.compat_47_1_4

/-- The canonical embedding of GF(47^2) into GF(47^4). -/
noncomputable def embed_47_2_4 :
    Hex.GFq 47 2 Hex.Conway.supportedEntry_47_2 →+*
      Hex.GFq 47 4 Hex.Conway.supportedEntry_47_4 :=
  conwayEmbed 47 2 4 _ _ Hex.Conway.compat_47_2_4

/-- The canonical embedding of GF(53^1) into GF(53^2). -/
noncomputable def embed_53_1_2 :
    Hex.GFq 53 1 Hex.Conway.supportedEntry_53_1 →+*
      Hex.GFq 53 2 Hex.Conway.supportedEntry_53_2 :=
  conwayEmbed 53 1 2 _ _ Hex.Conway.compat_53_1_2

/-- The canonical embedding of GF(53^1) into GF(53^3). -/
noncomputable def embed_53_1_3 :
    Hex.GFq 53 1 Hex.Conway.supportedEntry_53_1 →+*
      Hex.GFq 53 3 Hex.Conway.supportedEntry_53_3 :=
  conwayEmbed 53 1 3 _ _ Hex.Conway.compat_53_1_3

/-- The canonical embedding of GF(53^1) into GF(53^4). -/
noncomputable def embed_53_1_4 :
    Hex.GFq 53 1 Hex.Conway.supportedEntry_53_1 →+*
      Hex.GFq 53 4 Hex.Conway.supportedEntry_53_4 :=
  conwayEmbed 53 1 4 _ _ Hex.Conway.compat_53_1_4

/-- The canonical embedding of GF(53^2) into GF(53^4). -/
noncomputable def embed_53_2_4 :
    Hex.GFq 53 2 Hex.Conway.supportedEntry_53_2 →+*
      Hex.GFq 53 4 Hex.Conway.supportedEntry_53_4 :=
  conwayEmbed 53 2 4 _ _ Hex.Conway.compat_53_2_4

/-- The canonical embedding of GF(59^1) into GF(59^2). -/
noncomputable def embed_59_1_2 :
    Hex.GFq 59 1 Hex.Conway.supportedEntry_59_1 →+*
      Hex.GFq 59 2 Hex.Conway.supportedEntry_59_2 :=
  conwayEmbed 59 1 2 _ _ Hex.Conway.compat_59_1_2

/-- The canonical embedding of GF(59^1) into GF(59^3). -/
noncomputable def embed_59_1_3 :
    Hex.GFq 59 1 Hex.Conway.supportedEntry_59_1 →+*
      Hex.GFq 59 3 Hex.Conway.supportedEntry_59_3 :=
  conwayEmbed 59 1 3 _ _ Hex.Conway.compat_59_1_3

end HexGFqMathlib.Conway
