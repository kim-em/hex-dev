/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompareKey

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Equal rows have equal cumulative offsets. Thus a partial raw store can
be reused for another graph with the same prefix and allocated edge count. -/
theorem Rows.Prefix.agreement {R : Rows n} {H A : Hex.SparseGraph n} {count : Nat}
    (h : R.Prefix H count) (hcap : H.neighbors.size = A.neighbors.size)
    (he : ∀ i : Fin n, i.val < count → (A.nbrs i).toList = (H.nbrs i).toList) :
    R.Prefix A count := by
  have hoff : ∀ i, i ≤ count → H.offsets[i]! = A.offsets[i]! := by
    intro i
    induction i with
    | zero => intro _; rw [H.offset_zero, A.offset_zero]
    | succ i ih =>
      intro hi
      have hb : i < n := by have := h.count_le; omega
      have hp := ih (by omega)
      have hd := congrArg List.length (he ⟨i, hb⟩ (show i < count from by omega))
      simp only [Array.length_toList, ← Hex.SparseGraph.degree_eq_size,
        Hex.SparseGraph.degree] at hd
      have ha := A.offset_mono (i := i) (j := i + 1) (by omega) (by omega)
      have hh := H.offset_mono (i := i) (j := i + 1) (by omega) (by omega)
      omega
  refine ⟨h.count_le, h.offsets_size, h.neighbors_size.trans hcap,
    fun i hi => (h.offsets_eq i hi).trans (hoff i hi), ?_⟩
  intro i hi
  rw [he i hi]
  exact h.rows_perm i hi

/-- The returned equal-row prefix is precisely a valid installation prefix
for the candidate, provided the canonical buffer has its edge capacity. -/
theorem testcanlab_prefix (G H : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n)
    (hcap : H.neighbors.size = G.neighbors.size) :
    R.Prefix (G.relabel l.perm) (testcanlab (.ofGraph G) R lab).2 := by
  have hcmp := testcanlab_result G H R lab l hl hR
  apply (hR.mono hcmp.bound).agreement (by simpa using hcap)
  intro i hi
  simpa only [Compare.row_fin] using hcmp.agrees i.val hi

/-- Comparing against an installed canonical label supplies the exact prefix
required by the executed canonical update, including for the empty graph. -/
theorem testcanlab_update (G : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l c : Label n) (hl : Label.ofArray? n lab = some l)
    (hR : R.Prefix (G.relabel c.perm) n) :
    (updatecan (.ofGraph G) R lab (testcanlab (.ofGraph G) R lab).2).Prefix
      (G.relabel l.perm) n := by
  apply updatecan_relabel G R lab l _ hl
  exact testcanlab_prefix G (G.relabel c.perm) R lab l hl hR (by simp)

end Hex.GraphIso.Nauty.Sparse
