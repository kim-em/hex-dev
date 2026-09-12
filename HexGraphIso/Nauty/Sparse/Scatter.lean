/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.WorkSize
public import HexGraphIso.Nauty.Sparse.Autom
public import HexGraphIso.LabelArray

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The reusable scatter stores the forward map from the reference leaf
to the current leaf. Every old workspace entry is overwritten. -/
theorem scatter_perm {ref : Array Nat} {st : State n} {c l : Label n}
    (hw : st.workperm.size = n) (hc : Label.ofArray? n ref = some c)
    (hl : Label.ofArray? n st.lab = some l) (v : Fin n) :
    (scatter ref st).workperm[v.val]! = ((l.perm.comp c.perm.inv).get v).val := by
  have hmap (i : Fin n) : (scatter ref st).workperm[(c.get i).val]! = (l.get i).val := by
    rw [Label.ofArray?_get hc, Label.ofArray?_get hl]
    apply scatter_get (i := i.val) ?_ ?_ i.isLt
    · intro a b ha hb he
      have hab : c.perm.get ⟨a, ha⟩ = c.perm.get ⟨b, hb⟩ := by
        apply Fin.ext
        change (c.get ⟨a, ha⟩).val = (c.get ⟨b, hb⟩).val
        rw [Label.ofArray?_get hc, Label.ofArray?_get hc]
        exact he
      exact congrArg Fin.val (c.perm.get_inj hab)
    · intro j hj
      rw [hw, ← Label.ofArray?_get hc j hj]
      exact (c.get ⟨j, hj⟩).isLt
  simpa only [Label.get, Perm.get_inv_get, Perm.get_comp] using hmap (c.perm.inv.get v)

/-- An explicit native scan on this workspace establishes adjacency
preservation by precisely the permutation emitted by the scatter. -/
theorem scatter_isautom (G : Hex.SparseGraph n) {ref : Array Nat} {st : State n} {c l : Label n}
    (hw : st.workperm.size = n) (hc : Label.ofArray? n ref = some c)
    (hl : Label.ofArray? n st.lab = some l)
    (ha : isautom (.ofGraph G) (scatter ref st).workperm = true) :
    ∀ i j, G.adj ((l.perm.comp c.perm.inv).get i) ((l.perm.comp c.perm.inv).get j) = G.adj i j :=
  (isautom_iff G _ _ (scatter_perm hw hc hl)).mp ha

end Hex.GraphIso.Nauty.Sparse
