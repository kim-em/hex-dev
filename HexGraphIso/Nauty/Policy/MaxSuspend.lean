/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxChoice
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Save the parent being suspended by the next child call. -/
def Parents.push (parents : Parents n) (p : Parent n) : Parents n :=
  fun level => if level = p.loop.node.level then some p else parents level

/-- The saved child has the chosen vertex's key in the frozen sweep. -/
theorem Parent.key {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G ctx tcLevel) :
    (p.child ctx tcLevel).key ctx tcLevel = p.loop.key ctx tcLevel p.chosen := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hv := h.chosen
  have hw := h.effect.window_eq h.cell

  rw [← hw] at hv
  have he := h.effect.vertex_key (ctx := ctx) (tcLevel := tcLevel)
    (p.loop.prepare_ok h.node) h.partition hn0 h.node.positive h.cell h.len h.range hv
    (fuel := n - p.loop.node.level) (by have := h.node.depth; omega)

  rw [Loop.key, he]
  unfold Frame.key Parent.child
  simp only [show n + 1 - (p.loop.node.level + 1) = n - p.loop.node.level by omega]
  cases hf : p.loop.first <;> rfl

/-- Every original target vertex is bounded by the frozen full sweep. -/
theorem Loop.key_le {ctx : Ctx n} {tcLevel v : Nat} {l : Loop n}
    (hv : (windowSet n (l.prepare ctx tcLevel).2.2.2.2.lab (l.prepare ctx tcLevel).2.1.toNat
      (l.prepare ctx tcLevel).2.2.2.1).mem v = true) :
    keyLe (l.key ctx tcLevel v) (l.bound ctx tcLevel) := by
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  rw [← he]
  apply keyLe_iff.mpr
  apply keysMax_ge
  by_cases hz : o = 0
  · left
    simp only [hz, Nat.add_zero]
  · right
    apply List.mem_map.mpr
    refine ⟨o, ?_, rfl⟩
    simp only [List.mem_range']
    exact ⟨o - 1, by omega, by omega⟩

/-- An actual saved child stays below the complete chosen-cell maximum. -/
theorem Parent.key_le {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat} {p : Parent n}
    (h : p.Valid G ctx tcLevel) :
    keyLe ((p.child ctx tcLevel).key ctx tcLevel) (p.loop.bound ctx tcLevel) := by
  rw [p.key h]
  apply Loop.key_le
  have he := h.effect.window_eq h.cell

  rw [he]
  exact h.chosen

/-- Every selected child records the reference, shape, and target
justifications already established at its actual sweep entry. -/
theorem SweepInput.suspend {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n} {st : Search n}
    {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents) : (⟨l, st, tv, bs, fs⟩ : Parent n).Valid G ctx tcLevel := by
  rcases h.level_eq with rfl
  rcases h.numcells_eq with rfl
  rcases h.tc_eq with rfl
  refine ⟨h.node, h.partition, h.effect, h.equitable, h.window, h.len, h.range,
    ?_, h.path, h.choice, h.canonical, h.first_ref, h.small, ?_⟩
  · have hv := h.subset tv (h.cursor_mem tv rfl)
    have he := h.effect.window_eq h.window

    rwa [he] at hv
  · intro v hv hlt
    rcases h.coverage v hv with hd | ⟨w, hw, _, hrank⟩
    · exact hd
    · obtain ⟨_, u, hu, hle⟩ := hw
      cases hu
      change w ≤ v at hrank
      change v < tv at hlt
      omega

/-- Below the child's receiving level, saving a parent preserves exactly
the sweep's ancestor table, including the root frame at target zero. -/
theorem Parents.push_frames {ctx : Ctx n} {tcLevel target : Nat}
    {parents : Parents n} {p : Parent n} (hl : 1 ≤ p.loop.node.level)
    (ht : target < p.loop.node.level)
    (hparent : 1 < p.loop.node.level → ∃ prev,
      parents (p.loop.node.level - 1) = some prev ∧ prev.child ctx tcLevel = p.loop.node) :
    (parents.push p).frames ctx tcLevel target =
      ((parents.frames ctx tcLevel).insert p.loop.node) target := by
  by_cases he : target = p.loop.node.level - 1
  · subst target
    simp only [Frames.insert, ↓reduceIte]
    by_cases hroot : p.loop.node.level = 1
    · simp only [Parents.frames, hroot, Nat.sub_self, ↓reduceIte, Parents.push,
        Option.map_some]
    · obtain ⟨prev, hp, hc⟩ := hparent (by omega)
      simp only [Parents.frames, show p.loop.node.level - 1 ≠ 0 by omega, ↓reduceIte,
        Parents.push, show p.loop.node.level - 1 ≠ p.loop.node.level by omega, hp,
        Option.map_some, hc]
  · simp only [Frames.insert, he, ↓reduceIte, Parents.frames, Parents.push]
    by_cases hz : target = 0
    · simp only [hz, ↓reduceIte, show 1 ≠ p.loop.node.level by omega]
    · simp only [hz, ↓reduceIte, show target ≠ p.loop.node.level by omega]

end Hex.GraphIso.Nauty.Max
