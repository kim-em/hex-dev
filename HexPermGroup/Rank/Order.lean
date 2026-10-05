/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Rank
public import HexPermGroup.Order

public section

namespace Hex.PermGroup

/-- The checked group's existing rank and unrank maps witness its order. -/
theorem Group.hasOrder (G : Group n) : HasOrder G.generators G.order :=
  ⟨⟨G.rank, G.unrank, G.unrank_rank, G.rank_unrank⟩⟩


end Hex.PermGroup
