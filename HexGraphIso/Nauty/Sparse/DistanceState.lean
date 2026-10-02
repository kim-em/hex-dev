/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefinePrefix
public import HexGraphIso.Nauty.Sparse.RefineState

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual distance-cell scan preserves unprocessed cells while making
every completed cell constant in the captured distance array. -/
structure DistanceState (level : Nat) (before s : RefineSt n) (first : Nat) : Prop where
  valid : RefineSt.Valid level s
  step : RefineSt.Step level before s
  bound : first ≤ n
  suffix : RefinePrefix level first before.ptn s.ptn
  constant : ConstantPrefix n level first (fun v => before.hits[v]!) s.lab s.ptn
  hits : s.hits = before.hits
  active : Activation n level before.ptn s.ptn before.active s.active

namespace DistanceState

variable {n level first : Nat} {before s : RefineSt n}

theorem initial (h : RefineSt.Valid level s) : DistanceState level s s 0 :=
  ⟨h, .refl _ _, Nat.zero_le _, .initial _ _, .initial _ _ _ _ _, rfl, .refl _ _ _⟩

theorem cell (h : DistanceState level before s first) (hf : first < n) :
    IsCell s.ptn level first (s.cellend[first]! + 1 - first) ∧
      first ≤ s.cellend[first]! ∧ s.cellend[first]! < n := by
  apply h.valid.cell hf
  rcases h.suffix.start with he | hs
  · exact Or.inl he
  · exact Or.inr (by rw [h.step.cuts.closed _ hs]; exact hs)

theorem singleton (h : DistanceState level before s first) (hf : first < n)
    (he : s.cellend[first]! = first) : DistanceState level before s (first + 1) := by
  have hc : IsCell s.ptn level first 1 := by simpa only [he, Nat.add_sub_cancel_left] using (h.cell hf).1
  exact ⟨h.valid, h.step, by omega, h.suffix.advance hc, h.constant.singleton hc, h.hits, h.active⟩

theorem counts (h : DistanceState level before s first) (hbefore : RefineSt.Valid level before)
    (hv : ∀ v, v < n → before.hits[v]! ≤ n) (hf : first < n) :
    DistanceState level before (splitCounts level first true s) (s.cellend[first]! + 1) := by
  have hc := h.cell hf
  have hl : s.lab.size = n := by simpa using h.valid.lab.length_eq
  have hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2 := by
    intro q hq hq'
    rw [h.hits]
    have := hv s.lab[q]! (perm_bound h.valid.lab (by omega))
    omega
  have ht := h.valid.counts first true hc.1 hc.2.2 hk
  exact ⟨ht.1, h.step.trans ht.2 hbefore h.valid ht.1, by omega,
    h.suffix.counts hc.1 hl h.valid.size hc.2.2 hk true,
    h.constant.counts hc.1 hl h.valid.size hc.2.2 hk (by intro v _; rw [h.hits]) true,
    (splitCounts_frame level first true s).hits.trans h.hits,
    h.active.counts level first true s (h.suffix.cell hc.1) hc.1 hl h.valid.size hc.2.2 hk⟩

end DistanceState
end Hex.GraphIso.Nauty.Sparse
