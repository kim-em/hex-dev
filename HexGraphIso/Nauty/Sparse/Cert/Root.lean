/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Complete
public import HexGraphIso.Nauty.Sparse.SpecNode

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Produce proof records from the same stable colour buckets as the
native sparse search. The claimed key is supplied by that search. -/
@[expose] def produceRoot (G : GraphIso.Sparse.Colored n k) (B : Key n) : CertNode :=
  if n = 0 then .leaf else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    produceNode G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length B

theorem canonSpecKey_zero {G : GraphIso.Sparse.Colored n k} (hn : n = 0) :
    canonSpecKey G = ⟨[codeSentinel], G.graph⟩ := by
  simp only [canonSpecKey, specBest, rootLeaves, hn, ite_true,
    List.head_cons, List.tail_cons, SpecLeaf.best, List.foldl_nil,
    SpecLeaf.key, Label.id, Hex.SparseGraph.relabel_id]

/-- With no logical limit, a root certificate always replays against the
actual declarative maximum, including order zero. -/
theorem produceRoot_replays (G : GraphIso.Sparse.Colored n k) :
    checkKey G (produceRoot G (canonSpecKey G)) (canonSpecKey G) = true := by
  by_cases hn : n = 0
  · have he : (⟨[codeSentinel], Label.id n⟩ : SpecLeaf n).key G.graph = canonSpecKey G := by
      rw [canonSpecKey_zero hn]
      simp only [SpecLeaf.key, Label.id, Hex.SparseGraph.relabel_id]
    simp only [checkKey, produceRoot, hn, ite_true, Replay.leaf, Key.cmp_eq.mpr he]
    rfl
  · let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    have hv := SpecNode.initial G (by omega : 0 < n)
    dsimp only at hv
    have hb : ∀ l ∈ specLeaves G.graph 100 (n + 2) 1 p.1
        (initPtn n (n + 2) p.2) (initActive n p.2) p.2.length,
        Key.Le (l.key G.graph) (canonSpecKey G) := by
      intro l hl
      apply canonSpecKey_bound G
      simpa only [rootLeaves, hn, ite_false] using hl
    obtain ⟨a, ha⟩ := produceNode_replays hv.label hv.node hv.count hv.depth (by omega) hb
    have hs := checkNode_valid ha
    have ha' : a = true := hs.attains.mpr ⟨specBest G, by
      simpa only [rootLeaves, hn, ite_false] using specBest_mem G, rfl⟩
    subst a
    simpa only [checkKey, produceRoot, hn, ite_false, beq_iff_eq] using ha

end Hex.GraphIso.Nauty.Sparse
