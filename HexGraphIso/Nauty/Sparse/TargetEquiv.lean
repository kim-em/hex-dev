/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ContextMap
public import HexGraphIso.Nauty.Sparse.TargetInvariant

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A graph isomorphism preserves native target-row counts after transporting
the labelling and its valid cell index. -/
theorem Target.count_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n (lab.map (renamingOf p).toFun) ptn level t.cellstart t.cellend)
    (ha : a ∈ Target.nontrivial (cells ptn level n)) (hf : first < n) :
    (row (.ofGraph H) (lab.map (renamingOf p).toFun) t first).count a =
      (row (.ofGraph G) lab s first).count a := by
  have hl : lab.size = n := by simpa using hp.length_eq
  have hctx := Graph.context_map G H p hiso
  obtain ⟨b, hcell, hab⟩ := Target.mem_iff.mp ha
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hc := cells_isCell (Nat.le_of_eq hs.symm) hend' (a, b) hcell
  have hb := cells_end_lt_of_end (Nat.le_of_eq hs.symm) hend' hend (a, b) hcell
  have hs' : s.cellend[a]! = b := by
    have hh := hi.ends_eq a (b + 1 - a) hc (by omega) (by omega)
    omega
  have ht' : t.cellend[a]! = b := by
    have hh := hj.ends_eq a (b + 1 - a) hc (by omega) (by omega)
    omega
  have hlabel : LabOk lab n := fun i hi => perm_bound hp (by omega)
  rw [count_workset H _ ptn level t (perm_map hp p) hs hend hj ha hf,
    count_workset G lab ptn level s hp hs hend hi ha hf, hs', ht',
    worksetOf_map (renamingOf p) hlabel (by omega),
    getElem!_map_of_lt (renamingOf p).toFun lab (by omega),
    hctx.2.2 lab[first]! (perm_bound hp hf),
    VSet.cardInter_eq, VSet.cardInter_eq, ← VSet.image_inter, VSet.card_image]

/-- Partial-join scores commute with relabelling, independently of native
neighbour order and admissible scratch contents. -/
theorem Target.score_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n (lab.map (renamingOf p).toFun) ptn level t.cellstart t.cellend)
    (hf : first ∈ Target.nontrivial (cells ptn level n)) :
    score (.ofGraph H) (lab.map (renamingOf p).toFun) t (nontrivial (cells ptn level n)) first =
      score (.ofGraph G) lab s (nontrivial (cells ptn level n)) first := by
  have hfirst := bound hs hend hf
  unfold score
  apply List.countP_congr
  intro a ha
  have he := count_map G H p hiso lab ptn level s t hp hs hend hi hj ha hfirst
  have hb := bound hs hend ha
  have hstart := (Target.open_of_mem hs hend ha).2
  have hend' : t.cellend[a]! = s.cellend[a]! :=
    (hj.end_eq hs hend hb hstart).trans (hi.end_eq hs hend hb hstart).symm
  simp only [Join.qualifies, he, hend']

/-- Sparse best-cell selection commutes with the transported graph and
labelling, retaining its native first-maximum tie rule. -/
theorem bestcell_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level : Nat) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n (lab.map (renamingOf p).toFun) ptn level t.cellstart t.cellend) :
    bestcell (.ofGraph H) (lab.map (renamingOf p).toFun) ptn level = bestcell (.ofGraph G) lab ptn level := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  obtain ⟨m, hm⟩ := Label.ofArray?_exists (perm_map hp p)
  rw [bestcell_spec H _ ptn level t m hm hs hend hj,
    bestcell_spec G lab ptn level s l hl hs hend hi]
  exact Target.best_congr _ _ _ _ (fun a ha => Target.score_map G H p hiso lab ptn level s t
    hp hs hend hi hj ha)

/-- All sparse target-dispatch arms commute with relabelling. -/
theorem targetcell_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hj : Index.Valid n (lab.map (renamingOf p).toFun) ptn level t.cellstart t.cellend) :
    targetcell (.ofGraph H) (lab.map (renamingOf p).toFun) ptn level tcLevel hint =
      targetcell (.ofGraph G) lab ptn level tcLevel hint := by
  unfold targetcell
  split
  · rfl
  · split
    · exact bestcell_map G H p hiso lab ptn level s t hp hs hend hi hj
    · rfl

end Hex.GraphIso.Nauty.Sparse
