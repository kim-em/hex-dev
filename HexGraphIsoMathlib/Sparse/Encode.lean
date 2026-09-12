/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIsoMathlib.Encode
public import HexGraphIso.Sparse.Iso

public section

namespace Hex.GraphIso.Mathlib.Sparse

universe u v

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] {n k : Nat}

/-- Encode a Mathlib graph directly into sorted sparse rows. A general
adjacency oracle requires testing vertex pairs, but no dense matrix is
allocated. Each ordered colour is retained without renumbering. -/
@[expose] def encode (e : V ≃ Fin n) (G : Mathlib.Colored V k)
    [DecidableRel G.graph.Adj] : GraphIso.Sparse.Colored n k where
  graph := SparseGraph.ofRows
    (Hex.Vector.ofFn' fun i => (List.finRange n).filter fun j =>
      decide (G.graph.Adj (e.symm i) (e.symm j)))
    (fun i => by
      simp only [Hex.Vector.ofFn'_eq_ofFn, Fin.getElem_fin, Vector.getElem_ofFn]
      exact List.Pairwise.filter _ (List.pairwise_lt_finRange n))
    (fun i j => by simp [SimpleGraph.adj_comm])
    (fun i => by simp)
  coloring := {
    cells := Hex.Vector.ofFn' fun i => G.color (e.symm i)
    onto := fun c => by
      obtain ⟨v, hv⟩ := G.onto c
      refine ⟨e v, ?_⟩
      simpa [Hex.Vector.get_eq_getElem] using hv }

theorem encode_adj (e : V ≃ Fin n) (G : Mathlib.Colored V k)
    [DecidableRel G.graph.Adj] (i j : Fin n) :
    (encode e G).graph.adj i j = true ↔ G.graph.Adj (e.symm i) (e.symm j) := by
  rw [← SparseGraph.mem_nbrs, ← Array.mem_toList_iff, encode, SparseGraph.nbrs_ofRows]
  simp

theorem encode_color (e : V ≃ Fin n) (G : Mathlib.Colored V k)
    [DecidableRel G.graph.Adj] (i : Fin n) :
    (encode e G).coloring.cells[i] = G.color (e.symm i) := by
  simp [encode]

/-- The two encodings have identical adjacency and ordered colours.
This theorem is a proof bridge; sparse execution does not use `toDense`. -/
@[simp] theorem toDense_encode (e : V ≃ Fin n) (G : Mathlib.Colored V k)
    [DecidableRel G.graph.Adj] :
    (encode e G).toDense = Mathlib.encode e G := by
  apply GraphIso.Colored.ext
  · intro i j
    rw [GraphIso.Sparse.Colored.toDense, SparseGraph.adj_toDense, Bool.eq_iff_iff,
      encode_adj, Mathlib.encode_adj']
  · intro i
    change (encode e G).coloring.cells[i] = (Mathlib.encode e G).coloring.cells[i]
    rw [encode_color, Mathlib.encode_color']

variable {G : Mathlib.Colored V k} {H : Mathlib.Colored W k}
  [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]

/-- Decode a verified native sparse transporter as a Mathlib isomorphism. -/
def isoOfIsIso (eV : V ≃ Fin n) (eW : W ≃ Fin n) {p : Perm n}
    (h : GraphIso.Sparse.IsIso (encode eV G) (encode eW H) p) :
    Mathlib.Colored.Iso G H :=
  Mathlib.isoOfIsIso eV eW (by
    simpa only [toDense_encode] using (GraphIso.Sparse.isIso_toDense ..).mpr h)

theorem isIso_of_iso (eV : V ≃ Fin n) (eW : W ≃ Fin n) (h : Mathlib.Colored.Iso G H) :
    GraphIso.Sparse.IsIso (encode eV G) (encode eW H)
      (Perm.ofEquiv (eV.symm.trans (h.graphIso.toEquiv.trans eW))) := by
  apply (GraphIso.Sparse.isIso_toDense ..).mp
  simpa only [toDense_encode] using Mathlib.isIso_of_iso eV eW h

/-- Isomorphism is independent of the chosen finite enumerations. -/
theorem encode_iso_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔ GraphIso.Sparse.Isomorphic (encode eV G) (encode eW H) := by
  rw [← GraphIso.Sparse.isomorphic_toDense, toDense_encode, toDense_encode]
  exact Mathlib.encode_iso_iff eV eW

end Hex.GraphIso.Mathlib.Sparse
