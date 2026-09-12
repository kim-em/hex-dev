/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Uniform
public import HexGraphIso.Nauty.Sparse.RefinedSmall
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.LeafPath

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- Every selected descent below a native cheap-shaped node has the
same full key and targets. True cell-stabilizer transitivity transports
literal child calls with independent bounded scratch; no generated-group
completeness or dense execution is used. -/
theorem HasLeaf.small {G : Hex.SparseGraph n} {tcLevel level : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n} (h : HasLeaf G tcLevel level st targets key)
    (hr : RefineSt.Ready G level st) (hshape : NodeShape n level st.ptn) :
    Uniform G tcLevel level st targets key := by
  rcases h.cases with ⟨label, hd, hp, rfl, rfl⟩ |
    ⟨tc, len, o, scratch, rest, tail, hc, hb, hn, ho, hs, ht, hchild, rfl, rfl⟩
  · exact Uniform.leaf hr hd hp
  · have hguide := hchild.small (hr.child hc hb hn ho scratch hs)
      (hr.child_shape hc hb hn ho scratch hs hshape)
    apply Uniform.node hr hc hb hn ht
    intro j hj other hother
    obtain ⟨p, hiso, hcells, hmove⟩ : ∃ p : Perm n,
        (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ∧
        cellsPerm st.ptn level st.lab (st.lab.map (renamingOf p).toFun) ∧
        st.lab[tc + j]! = renamingOf p st.lab[tc + o]! := by
      by_cases he : o = j
      · subst j
        have hid : (renamingOf (Perm.id n)).toFun = id := by
          funext v
          simp [renamingOf]
        refine ⟨Perm.id n, by simp, ?_, ?_⟩
        · rw [hid, Array.map_id]
          exact cellsPerm_refl _ _ _
        · change st.lab[tc + o]! = (renamingOf (Perm.id n)).toFun st.lab[tc + o]!
          rw [hid, id_eq]
      · exact hr.automorphism hshape hc hb hn ho hj he
    have he := child_equiv G G p hiso hr hr rfl rfl hcells hc hb hn ho hj
      scratch other hs hother hmove
    exact hguide.map G G p hiso (hr.child hc hb hn ho scratch hs)
      (hr.child hc hb hn hj other hother) he
termination_by targets.length

end Hex.GraphIso.Nauty.Sparse.Generation
