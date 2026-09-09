/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPush
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.ShortPair
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.CanonRef
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- An exhausted cursor leaves every vertex of the original target
window covered, and hence covers its entire frozen maximum. -/
theorem SweepInput.done_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 none cell index
      st l bs fs parents) : Generic.Covers (l.bound ctx tcLevel) (st.key ctx bs) := by
  let p := l.prepare ctx tcLevel
  have hcov := h.coverage.finish (by
    intro v hv
    obtain ⟨_, tv, ht, _⟩ := hv
    cases ht)
  have hlen : 2 ≤ p.2.2.2.1 := h.len
  have hrange : p.2.1.toNat + p.2.2.2.1 ≤ n := by
    rw [← h.tc_eq]
    exact h.range
  have hsize : p.2.2.2.2.lab.size = n := h.base.labSize
  have hgo : ∀ o, o < p.2.2.2.1 →
      Generic.Covers (l.key ctx tcLevel p.2.2.2.2.lab[p.2.1.toNat + o]!) (st.key ctx bs) := by
    intro o ho
    have hw : (windowSet n p.2.2.2.2.lab p.2.1.toNat p.2.2.2.1).mem
        p.2.2.2.2.lab[p.2.1.toNat + o]! = true := by
      apply mem_windowSet.mpr
      exact ⟨(labOk_of_reach h.base.labSize h.base.reach) _ (by change p.2.1.toNat + o < p.2.2.2.2.lab.size; rw [hsize]; omega),
        mem_segN_iff.mpr ⟨o, ho, rfl⟩⟩
    have hh := hcov _ (by simpa only [h.tc_eq] using hw)
    rw [h.level_eq, h.numcells_eq, h.tc_eq] at hh
    exact hh
  unfold Loop.bound
  apply Generic.Covers.keysMax
  · simpa only [Nat.add_zero] using hgo 0 (by omega)
  · intro key hk
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp ho
    change i < p.2.2.2.1 - 1 at hi
    exact hgo o (by omega)

/-- An exhausted sweep reads the settled incumbent and closes the
coverage contract without changing any search state. -/
theorem finish (G : Colored n k) (tcLevel : Nat) :
    ∀ fuel cfuel first level numcells tc tv1 cell index st,
      (keyContract G tcLevel).sweepPost fuel cfuel first level numcells tc tv1 none cell index st
        (.done, index, st) := by
  intro fuel cfuel first level numcells tc tv1 cell index st l bs fs parents h
  have hc := h.done_cover
  have hread : st.best { g := rowsOf G } = st.key { g := rowsOf G } bs := by
    rcases h.phase with ⟨_, hbs, _, _, _, _, _⟩ | ⟨_, hm, hn⟩
    · rw [hbs] at hc
      obtain ⟨_, hh, _⟩ := hc
      change (none : Option (Key n)) = some _ at hh
      cases hh
    · apply best_eq_key hm.canonical
      rcases hn with hn | ⟨_, hn⟩
      · omega
      · cases hn
  rw [hread]
  exact ⟨Generic.Bounded.refl _ _, hc⟩

end Hex.GraphIso.Nauty.Max
