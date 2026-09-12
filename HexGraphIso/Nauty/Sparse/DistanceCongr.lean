/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineCongr
public import HexGraphIso.Nauty.Sparse.RefineDistance
import all HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse.Refinement

/-- The full distance-cell scan preserves literal label agreement when
the captured native distance arrays agree. Valid scratch indices may differ. -/
theorem distance_lab (level : Nat) (s t : RefineSt n)
    (hs : s.Valid level) (ht : t.Valid level)
    (he : RefineSt.Equiv (renamingOf (Perm.id n)) level s t) (hl : t.lab = s.lab)
    (hk : t.hits = s.hits) (hv : ∀ v, v < n → s.hits[v]! ≤ n) :
    (distance level s).lab = (distance level t).lab := by
  let σ := renamingOf (Perm.id n)
  have hid : σ.toFun = id := by funext v; simp [σ, renamingOf]
  have hw : ∀ v, v < n → t.hits[v]! ≤ n := by rw [hk]; exact hv
  have hkeys : ∀ v, v < n → t.hits[σ v]! = s.hits[v]! := by
    intro v hv
    change t.hits[σ.toFun v]! = s.hits[v]!
    rw [hid, hk]
    rfl
  let R (a b : RefineSt n × Nat) := DistanceState.Rel σ level s t a b ∧ b.1.lab = a.1.lab
  let step (_ : Nat) (x : RefineSt n × Nat) : Id (ForInStep (RefineSt n × Nat)) :=
    if x.2 ≥ n then .done x else
      let last := x.1.cellend[x.2]!
      if x.2 < last then .yield (splitCounts level x.2 true x.1, last + 1)
      else .yield (x.1, last + 1)
  have hr := Loop.range_rel n step step R (by
    intro i a b h
    rcases a with ⟨a, first⟩
    rcases b with ⟨b, other⟩
    rcases h with ⟨⟨ha, hb, hpos, he⟩, hl⟩
    dsimp only at hpos
    subst other
    have hold := DistanceState.step_rel σ level first s t a b hs ht hv hw hkeys ha hb he
    dsimp only [step]
    by_cases hf : n ≤ first
    · simp only [ite_eq_left hf] at hold ⊢
      cases hold with
      | done hpost => exact .done ⟨hpost, hl⟩
    · simp only [ite_eq_right hf] at hold ⊢
      have hc : IsCell a.ptn level first (a.cellend[first]! + 1 - first) ∧
          first ≤ a.cellend[first]! ∧ a.cellend[first]! < n := ha.cell (by omega)
      have hi := hb.valid.index
      rw [he.ptn] at hi
      have hend := ha.valid.index.ends_congr hi hc.1 (by omega)
      rw [← hend] at hold ⊢
      by_cases hcut : first < a.cellend[first]!
      · simp only [ite_eq_left hcut] at hold ⊢
        cases hold with
        | yield hpost =>
          apply Loop.Rel.yield
          refine ⟨hpost, ?_⟩
          have hsize : a.lab.size = n := by simpa using ha.valid.lab.length_eq
          exact (splitCounts_lab level first true a b hl hend.symm (by omega) (by omega)
            (fun q _ _ => by rw [ha.hits, hb.hits, hk])).symm
      · simp only [ite_eq_right hcut] at hold ⊢
        cases hold with
        | yield hpost => exact .yield ⟨hpost, hl⟩)
    (show R (s, 0) (t, 0) from ⟨⟨.initial hs, .initial ht, rfl, he⟩, hl⟩)
  simpa only [distance, step, Id.run, bind, pure, apply_ite ForInStep.yield] using hr.2.symm

/-- Native BFS starts at the same literal queued vertex for equal input
labels. Its distances therefore agree before the complete shallow scan. -/
theorem shallow_lab (G : Hex.SparseGraph n) (level : Nat) (s t : RefineSt n)
    (hs : s.Valid level) (ht : t.Valid level)
    (he : RefineSt.Equiv (renamingOf (Perm.id n)) level s t) (hl : t.lab = s.lab)
    (hq : s.queue.size = 1) :
    (distance level (distanceStart (.ofGraph G) s)).lab =
      (distance level (distanceStart (.ofGraph G) t)).lab := by
  have ha := hs.distance_start G hq
  have hb := ht.distance_start G (he.queue ▸ hq)
  have hstart : RefineSt.Equiv (renamingOf (Perm.id n)) level
      (distanceStart (.ofGraph G) s) (distanceStart (.ofGraph G) t) := by
    refine ⟨he.ptn, he.cells, ?_, he.count⟩
    simp only [distanceStart, CountTrace.control, he.active, he.queue, he.code]
  have hh : (distanceStart (.ofGraph G) t).hits = (distanceStart (.ofGraph G) s).hits := by
    simp only [distanceStart, hl, ← he.queue]
  apply distance_lab level _ _ ha hb hstart hl hh
  intro v hv
  have hc := hs.queue_cell (show 0 < s.queue.size by omega)
  have hroot := perm_bound hs.lab hc.1
  exact (distvals_correct G ⟨s.lab[s.queue[0]!]!, hroot⟩).bound ⟨v, hv⟩

end Hex.GraphIso.Nauty.Sparse.Refinement
