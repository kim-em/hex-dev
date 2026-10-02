/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReturnCodes
import all HexGraphIso.Nauty.Sparse.ReturnCodes

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A sparse subtree key is bounded by an installed native incumbent. -/
def Covers (bound : Key n) (best : Option (Key n)) : Prop :=
  ∃ b, best = some b ∧ Key.Le bound b

namespace Covers

theorem grow {bound : Key n} {before after : Option (Key n)}
    (h : Covers bound before) (hg : Grows before after) : Covers bound after := by
  obtain ⟨b, hb, hbound⟩ := h
  obtain ⟨a, ha, hba⟩ := hg b hb
  exact ⟨a, ha, Key.le_trans hbound hba⟩

theorem mono {a b : Key n} {best : Option (Key n)}
    (h : Covers b best) (hab : Key.Le a b) : Covers a best := by
  obtain ⟨c, hc, hbc⟩ := h
  exact ⟨c, hc, Key.le_trans hab hbc⟩

theorem max {a b : Key n} {best : Option (Key n)}
    (ha : Covers a best) (hb : Covers b best) : Covers (Key.max a b) best := by
  rcases Key.max_mem a b with he | he
  · rwa [he]
  · rwa [he]

end Covers

end Hex.GraphIso.Nauty.Sparse
