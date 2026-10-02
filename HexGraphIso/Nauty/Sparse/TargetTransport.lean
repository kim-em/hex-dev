/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetEquiv
public import HexGraphIso.Nauty.Sparse.IndexWitness

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The full fresh target transports its vertex set and retains its position
and size under graph relabelling. Valid index witnesses are constructed. -/
theorem maketargetcell_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : bcount ptn level n < n) :
    let a := maketargetcell (.ofGraph G) lab ptn level tcLevel hint
    maketargetcell (.ofGraph H) (lab.map (renamingOf p).toFun) ptn level tcLevel hint =
      (a.1, a.2.1.image (renamingOf p), a.2.2) := by
  obtain ⟨s, hi⟩ := Index.exists_valid hp hs hend
  obtain ⟨t, hj⟩ := Index.exists_valid (perm_map hp p) hs hend
  have he := targetcell_map G H p hiso lab ptn level tcLevel hint s t hp hs hend hi hj
  have hm := targetcell_nontrivial G lab ptn level tcLevel hint hp hs hend hc
  have hb := Target.bound hs hend hm
  have hl : lab.size = n := by simpa using hp.length_eq
  have hlast := cellEnd_lt (ptn := ptn) (level := level)
    (i := targetcell (.ofGraph G) lab ptn level tcLevel hint)
    (by omega) (by simpa only [hs] using hend)
  have hlabel : LabOk lab n := fun i hi => perm_bound hp (by omega)
  have hw := worksetOf_map (renamingOf p) hlabel
    (lo := targetcell (.ofGraph G) lab ptn level tcLevel hint)
    (hi := cellEnd ptn level (targetcell (.ofGraph G) lab ptn level tcLevel hint)) (by omega)
  simp only [maketargetcell, he, hw]

/-- Admissible caches agree on all observable target fields after relabelling,
including invalid-cache fallback, valid hints, and the depth cutoff. -/
theorem maketargetCached_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Scratch.Valid n lab ptn level s)
    (hj : Scratch.Valid n (lab.map (renamingOf p).toFun) ptn level t)
    (hc : bcount ptn level n < n) :
    let a := maketargetCached (.ofGraph G) lab ptn level tcLevel hint s
    let b := maketargetCached (.ofGraph H) (lab.map (renamingOf p).toFun) ptn level tcLevel hint t
    (b.1, b.2.1, b.2.2.1) = (a.1, a.2.1.image (renamingOf p), a.2.2.1) := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  obtain ⟨m, hm⟩ := Label.ofArray?_exists (perm_map hp p)
  have hn := Target.nonempty hs hend hc
  have ha := maketargetCached_eq G lab ptn level tcLevel hint s l hl hs hend hi hn
  have hb := maketargetCached_eq H _ ptn level tcLevel hint t m hm hs hend hj hn
  have ht := maketargetcell_map G H p hiso lab ptn level tcLevel hint hp hs hend hc
  rw [← ha] at ht
  exact hb.trans ht

/-- Cached targets are independent of the ordering within equitable cells;
the cache's flag and scratch contents may differ between the two calls. -/
theorem maketargetCached_perm (G : Hex.SparseGraph n) (lab out ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (s t : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hi : Scratch.Valid n lab ptn level s) (hj : Scratch.Valid n out ptn level t)
    (heq : Equitable (Graph.context G) level lab ptn) (hperm : cellsPerm ptn level lab out)
    (hc : bcount ptn level n < n) :
    let a := maketargetCached (.ofGraph G) lab ptn level tcLevel hint s
    let b := maketargetCached (.ofGraph G) out ptn level tcLevel hint t
    (a.1, a.2.1, a.2.2.1) = (b.1, b.2.1, b.2.2.1) := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  obtain ⟨m, hm⟩ := Label.ofArray?_exists hq
  obtain ⟨s', hs'⟩ := Index.exists_valid hp hs hend
  obtain ⟨t', ht'⟩ := Index.exists_valid hq hs hend
  have hn := Target.nonempty hs hend hc
  have ha := maketargetCached_eq G lab ptn level tcLevel hint s l hl hs hend hi hn
  have hb := maketargetCached_eq G out ptn level tcLevel hint t m hm hs hend hj hn
  exact ha.trans ((maketargetcell_perm G lab out ptn level tcLevel hint s' t' hp hq hs hend
    hs' ht' heq hperm hc).trans hb.symm)

end Hex.GraphIso.Nauty.Sparse
