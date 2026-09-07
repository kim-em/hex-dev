/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A valid workspace exposes the newly inserted pair to the short filter,
including the overwrite at capacity. -/
theorem RunInv.push_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (pair : VSet n × VSet n) :
    (pushAuto st pair).autos.back? = some pair := by
  change (pushAuto st pair).view.autos.back? = some pair
  rw [view_pushAuto]
  exact Nauty.pushAuto_back h.workspace.1

/-- The short filter following an explicit admission reads that admission's pair. -/
theorem RunInv.auto_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) {leaf : Leaf} (level : Nat)
    (ha : leaf = .autoFirst ∨ leaf = .autoCanon) :
    (leafExit leaf level st).2.autos.back? = some (fmperm st.workperm n) := by
  rcases ha with rfl | rfl
  all_goals rw [leafExit_autos, admit_autos]
  all_goals exact h.push_back _

/-- The cheap prune tail exposes its frozen implicit pair to the short filter. -/
theorem RunInv.cheap_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) {leaf : Leaf} {level : Nat}
    (ha : leaf = .bad ∨ ∃ sr, leaf = .better sr) (hne : level ≠ st.noncheaplevel) :
    (leafExit leaf level st).2.autos.back? = some (fmptn st.lab st.ptn st.noncheaplevel n) := by
  rcases ha with rfl | ⟨sr, rfl⟩
  all_goals rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
  all_goals exact h.push_back _

/-- The actual sweep's fix-passing pairs carry each vertex of the full
target cell to a surviving representative under a checked automorphism
stabilizing this partition and fixing its individualized path. -/
theorem SweepPre.longprune {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc tv1 len : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st)
    (hn0 : 0 < n) (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n) :
    ∀ v, v < n → (windowSet n st.lab tc len).mem v = true →
      ∃ γ, checkAutom ctx.g γ = true ∧
        (∀ u, u < n → st.fixedpts.mem u = true → γ[u]! = u) ∧
        CellStab st.ptn level st.lab γ ∧
        (windowSet n st.lab tc len).mem γ[v]! = true ∧
        (Nauty.longprune (windowSet n st.lab tc len) st.fixedpts st.autos).mem γ[v]! = true :=
  Nauty.longprune_carried (labOk_of_reach h.partition.labSize h.partition.reach)
    h.partition.labSize h.partition.ptnSize (searchOk_end hn0 h.partition h.positive)
    hc hr h.local_pairs

end Hex.GraphIso.Nauty.Engine
