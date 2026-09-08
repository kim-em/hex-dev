/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

/-! The cell stabilizer of a small-cell partition identifies its child
specification keys. These statements use only a refined partition and
its individualizations. -/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The finite array represented by a vertex renaming. -/
@[expose] def renamingArray (sigma : Renaming n) : Array Nat :=
  .ofFn fun i : Fin n => sigma i

theorem renamingArray_size (sigma : Renaming n) :
    (renamingArray sigma).size = n := by
  simp [renamingArray]

theorem renamingArray_get (sigma : Renaming n) {v : Nat} (hv : v < n) :
    (renamingArray sigma)[v]! = sigma v := by
  rw [getElem!_pos _ _ (by rw [renamingArray_size]; exact hv)]
  simp [renamingArray]

private theorem map_range_get (a : Array Nat) (hs : a.size = n) :
    (List.range n).map (fun i => a[i]!) = a.toList := by
  refine List.ext_getElem (by simp [hs]) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos a i (by simpa using h₂)]
  simp

/-- A row-preserving renaming passes the concrete automorphism checker. -/
theorem checkAutom_renaming {ctx : Ctx n} (sigma : Renaming n)
    (hrows : RowsMap sigma ctx.g ctx.g) :
    checkAutom ctx.g (renamingArray sigma) = true := by
  have hs := renamingArray_size sigma
  have hok : LabOk (renamingArray sigma) n := by
    intro i hi
    rw [hs] at hi
    rw [renamingArray_get sigma hi]
    exact (sigma.maps i).mp hi
  have hinj : LabInj (renamingArray sigma) n := by
    intro i j hi hj heq
    rw [renamingArray_get sigma hi, renamingArray_get sigma hj] at heq
    exact sigma.inj _ _ heq
  rw [checkAutom]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using hs, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun v hv => by
      have hvn := List.mem_range.mp hv
      simpa using hok v (by rw [hs]; exact hvn)
  · rw [List.isPerm_iff, map_range_get _ hs]
    exact labInj_perm_range hs hok hinj
  · refine List.all_eq_true.mpr fun v hv => ?_
    have hvn := List.mem_range.mp hv
    simp only [beq_iff_eq]
    rw [renamingArray_get sigma hvn, hrows.2.2 v hvn]
    exact image_congr _ fun w hw => (renamingArray_get sigma hw).symm

/-- At a small-cell node, every two members of a non-singleton cell have
equal semantic child subtrees.  This packages the geometric flip as the
concrete checked, cell-stabilizing array expected by `childKey_of_carried`.
-/
theorem SubtreeOk.child_key_eq {ctx : Ctx n} {st : RefineSt n}
    {tcLevel fuel level tc len numcells oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (hoU : oU < len) (hoV : oV < len)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oV =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oU := by
  rcases Decidable.em (oU = oV) with rfl | hUV
  · rfl
  have hmem : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    mem_cells_of_isCell (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
      hS.it.ok.ptnEnd
      hcell (by omega) (by rw [hS.it.ok.ptnSize]; exact hrange)
  have hdiff : tc + len - 1 - tc = len - 1 := by omega
  obtain ⟨sigma, hrows, hperm, hmap⟩ :=
    stabilizer_transitive (oU := oU) (oV := oV) hS hgsz hsymm hloop hmem
      (by omega) (by rw [hdiff]; omega) (by rw [hdiff]; omega) hUV
  let gamma := renamingArray sigma
  have hstab : CellStab st.ptn level st.lab gamma := by
    change cellsPerm st.ptn level st.lab
      (st.lab.map fun w => gamma[w]!)
    have hmapLab : st.lab.map (fun w => gamma[w]!) =
        st.lab.map sigma.toFun :=
      map_congr_of_labOk hS.it.ok.labOk fun w hw =>
        renamingArray_get sigma hw
    rw [hmapLab]
    exact hperm.cells
  apply childKey_of_carried hgsz (checkAutom_renaming sigma hrows)
    tcLevel fuel level hstab hS.it.ok.labSize hS.it.ok.labOk
    hS.it.ok.ptnSize hS.it.ok.ptnEnd (fun q => by
      rcases Decidable.em (q < n) with hq | hq
      · exact hS.it.vals q hq
      · left
        rw [getElem!_oob (by rw [hS.it.ok.ptnSize]; omega)]
        exact Nat.zero_le _)
    hcell hrange
    hoV hoU hfuel
  have hidxU : tc + oU < st.lab.size := by
    rw [hS.it.ok.labSize]
    omega
  rw [renamingArray_get sigma (hS.it.ok.labOk _ hidxU)]
  exact hmap.symm

/-- Below a small-cell node, the specification maximum is the subtree
of any member of its target cell, with the node's refinement code prefixed. -/
theorem SubtreeOk.node_key {ctx : Ctx n} {lab ptn : Array Nat} {active : VSet n}
    {tcLevel fuel level numcells o : Nat}
    (hS : SubtreeOk ctx level (refine ctx level lab ptn active numcells))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hdisc : discreteAt (refine ctx level lab ptn active numcells).ptn level n = false)
    (ho : o < (specMaketargetcell ctx (refine ctx level lab ptn active numcells).lab
      (refine ctx level lab ptn active numcells).ptn level tcLevel).2.2)
    (hfuel : level + 1 + fuel ≤ n + 1) (stem : List Nat) :
    let r := refine ctx level lab ptn active numcells
    let tc := (specMaketargetcell ctx r.lab r.ptn level tcLevel).1
    prefixKey stem (specNode ctx tcLevel (fuel + 1) level lab ptn active numcells) =
      prefixKey (stem ++ [r.longcode])
        (childKey ctx tcLevel fuel level r.lab r.ptn tc r.numcells o) := by
  let r := refine ctx level lab ptn active numcells
  obtain ⟨p, htc, hne, hpn, hcell, hend⟩ :=
    targetcell_facts (ctx := ctx) (tcLevel := tcLevel) r.lab
      hS.it.ok.ptnSize hS.it.ok.ptnEnd hdisc
  have ht : specMaketargetcell ctx r.lab r.ptn level tcLevel =
      (p.1, worksetOf n r.lab p.1 p.2, p.2 - p.1 + 1) := by
    change specTargetcell ctx r.lab r.ptn level tcLevel = p.1 at htc
    change cellEnd r.ptn level (p.1 + 1) = p.2 at hend
    simp only [specMaketargetcell, htc, hend]
  have hlen : (specMaketargetcell ctx r.lab r.ptn level tcLevel).2.2 =
      (p.2 - p.1) + 1 := by rw [ht]
  have ho' : o < p.2 - p.1 + 1 := by
    change o < (specMaketargetcell ctx r.lab r.ptn level tcLevel).2.2 at ho
    simpa only [ht] using ho
  let key := fun j => prefixKey (stem ++ [r.longcode])
    (childKey ctx tcLevel fuel level r.lab r.ptn p.1 r.numcells j)
  have hkey : ∀ j, j < p.2 - p.1 + 1 → key j = key o := by
    intro j hj
    apply congrArg (prefixKey (stem ++ [r.longcode]))
    exact hS.child_key_eq hgsz hsymm hloop hcell (by omega) (by omega)
      (by omega) (by omega) hfuel
  have hm : keysMax (key 0) ((List.range (p.2 - p.1)).map fun j => key (j + 1)) = key o := by
    apply keysMax_eq_of_le
    · rw [hkey 0 (by omega)]
      exact keyLe_refl _
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      rw [hkey (j + 1) (by have := List.mem_range.mp hj; omega)]
      exact keyLe_refl _
    · left
      exact (hkey 0 (by omega)).symm
  dsimp only
  rw [specNode_internal stem hdisc hlen]
  dsimp only [r] at ht
  simpa only [key, r, specChild, childKey, ht] using hm

end Hex.GraphIso.Nauty
