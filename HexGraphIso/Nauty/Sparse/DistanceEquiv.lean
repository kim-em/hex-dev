/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineEquiv
public import HexGraphIso.Nauty.Sparse.DistanceState
public import HexGraphIso.Nauty.Sparse.LoopRel

public section

namespace Hex.GraphIso.Nauty.Sparse.DistanceState

/-- The two executed distance scans have valid states, the same cursor,
and corresponding refinement observations. -/
@[expose] def Rel (σ : Renaming n) (level : Nat) (s t : RefineSt n)
    (a b : RefineSt n × Nat) : Prop :=
  DistanceState level s a.1 a.2 ∧ DistanceState level t b.1 b.2 ∧
    a.2 = b.2 ∧ RefineSt.Equiv σ level a.1 b.1

/-- One literal distance-loop callback transports its state and its
stop/continue choice, including skipped singleton cells. -/
theorem step_rel (σ : Renaming n) (level first : Nat) (s t a b : RefineSt n)
    (hs : RefineSt.Valid level s) (ht : RefineSt.Valid level t)
    (hv : ∀ v, v < n → s.hits[v]! ≤ n) (hw : ∀ v, v < n → t.hits[v]! ≤ n)
    (hkeys : ∀ v, v < n → t.hits[σ v]! = s.hits[v]!)
    (ha : DistanceState level s a first) (hb : DistanceState level t b first)
    (he : RefineSt.Equiv σ level a b) :
    Loop.Rel (Rel σ level s t)
      (if first ≥ n then ForInStep.done (a, first) else
        let last := a.cellend[first]!
        if first < last then .yield (splitCounts level first true a, last + 1)
        else .yield (a, last + 1))
      (if first ≥ n then ForInStep.done (b, first) else
        let last := b.cellend[first]!
        if first < last then .yield (splitCounts level first true b, last + 1)
        else .yield (b, last + 1)) := by
  by_cases hf : n ≤ first
  · simp only [ite_eq_left hf]
    exact .done ⟨ha, hb, rfl, he⟩
  · simp only [ite_eq_right hf]
    have hfa : first < n := by omega
    have hc := ha.cell hfa
    have hd := hb.cell hfa
    have hi := hb.valid.index
    rw [he.ptn] at hi
    have hend := ha.valid.index.ends_congr hi hc.1 (by omega)
    have hka : ∀ q, first ≤ q → q ≤ a.cellend[first]! → a.hits[a.lab[q]!]! < n + 2 := by
      intro q hq hu
      rw [ha.hits]
      have := hv a.lab[q]! (perm_bound ha.valid.lab (i := q) (by omega))
      omega
    have hkb : ∀ q, first ≤ q → q ≤ b.cellend[first]! → b.hits[b.lab[q]!]! < n + 2 := by
      intro q hq hu
      rw [hb.hits]
      have := hw b.lab[q]! (perm_bound hb.valid.lab (i := q) (by omega))
      omega
    rw [← hend]
    by_cases hcut : first < a.cellend[first]!
    · simp only [ite_eq_left hcut]
      apply Loop.Rel.yield
      refine ⟨ha.counts hs hv hfa, ?_, rfl, ?_⟩
      · simpa only [hend] using hb.counts ht hw hfa
      · apply he.counts first true ha.valid hb.valid hc.1 hc.2.2 hka hkb
        intro v hm
        rw [ha.hits, hb.hits]
        obtain ⟨i, hi, rfl⟩ := mem_segN_iff.mp hm
        exact hkeys _ (perm_bound ha.valid.lab (by omega))
    · simp only [ite_eq_right hcut]
      have haend : a.cellend[first]! = first := by omega
      have hbend : b.cellend[first]! = first := by omega
      rw [haend]
      exact .yield ⟨ha.singleton hfa haend, hb.singleton hfa hbend, rfl, he⟩

end Hex.GraphIso.Nauty.Sparse.DistanceState
