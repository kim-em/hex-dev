/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Every accumulated generator stabilizes each saved first ancestor
whose sweep survives the return. Ancestors unwound past need no carrier. -/
def Keeps (parents : Parents n) (exit : Exit) (st : Search n) : Prop :=
  ∀ t p, parents t = some p → p.loop.first = true →
    (match exit with | .unwind target _ => t ≤ target | _ => True) →
    ∀ γ ∈ st.genTrace, CellStab p.state.ptn t p.state.lab γ

/-- The incoming scope already stabilizes every saved first frame. -/
theorem Scope.keeps {G : Colored n k} {ctx : Ctx n} {tcLevel level : Nat}
    {cs bs : List Nat} {st : Search n} {parents : Parents n}
    (h : Scope G ctx tcLevel level cs bs st parents) (exit : Exit) : Keeps parents exit st :=
  fun t p hp hf _ γ hγ => h.generators t p hp hf γ hγ

/-- Cleanup and recovery preserve the accumulated carriers when they
retain the generator trace. -/
theorem Keeps.congr {parents : Parents n} {exit : Exit} {st out : Search n}
    (h : Keeps parents exit st) (he : out.genTrace = st.genTrace) : Keeps parents exit out := by
  intro t p hp hf ht γ hγ
  rw [he] at hγ
  exact h t p hp hf ht γ hγ

end Hex.GraphIso.Nauty.Max
