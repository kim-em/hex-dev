/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOrbit
public import HexGraphIso.Nauty.TranscriptionInv

public section

/-!
The stabilization invariant of the verified search refinement: the
generators the search admits fix the cells of their admitting nodes
setwise, and cell stabilization survives descent.

`childKey_of_orbPruned` consumes `CellStab` at the node performing an
orbit prune. This file supplies it from the run facts the simulation
induction carries, in three layers:

* **Reach transfer.** `cellsPerm` from an ancestor node's state is the
  node-relative generalization of `CellsReach`, and the two
  labelling-mutating operations preserve it (`refine_reachAt`,
  `breakout_reachAt`); the root-relative lemmas in
  `TranscriptionInv.lean` are the instance at the initial partition.
* **Scatter stabilization.** A generator is admitted as a scatter
  carrying one leaf labelling onto another. Both labellings are
  reachable from any common ancestor, and a scatter joining two
  reachable labellings stabilizes every cell of the ancestor's
  partition (`cellStab_of_scatter`).
* **Descent propagation.** A checked automorphism stabilizing a node's
  cells still stabilizes the cells after refinement
  (`cellStab_refine`): `refine` depends on the labelling only through
  cell contents (`refine_perm`) and commutes with the automorphism
  (`refine_map`), so the two transports compose.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Cell-contents equivalence is symmetric. -/
theorem cellsPerm_symm {ptn : Array Nat} {level : Nat}
    {lab1 lab2 : Array Nat} (h : cellsPerm ptn level lab1 lab2) :
    cellsPerm ptn level lab2 lab1 :=
  fun a len hc => (h a len hc).symm

/-- `refine` preserves reachability from an ancestor node's state: it
permutes labels within cells of its own finer partition, and the
ancestor's boundaries persist, so cell-content equivalence coarsens and
composes. The node-relative form of `refine_cellsReach`. -/
theorem refine_reachAt {ctx : Ctx} {ptnN labN : Array Nat} {levN : Nat}
    {lab ptn : Array Nat} {level active numcells : Nat}
    (hreach : cellsPerm ptnN levN labN lab)
    (hnn : ctx.n ≤ ptn.size) (hszN : ptnN.size = ptn.size)
    (hlsz : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hendN : ptnN[ptnN.size - 1]! ≤ levN)
    (hcoarse : ∀ q : Nat, ptnN[q]! ≤ levN → ptn[q]! ≤ level) :
    cellsPerm ptnN levN labN
      (refine ctx level lab ptn active numcells).lab := by
  have hRinv := refine_refInv (ctx := ctx) (active := active)
    (numcells := numcells) hnn hlsz hend
  refine cellsPerm_trans hreach ?_
  exact cellsPerm_coarsen hszN hlsz (by rw [hRinv.labSize, hlsz])
    hRinv.perm hend hendN hcoarse

/-- `breakout` preserves reachability from an ancestor node's state:
individualization permutes within one cell of the current partition,
which refines the ancestor's. The node-relative form of
`breakout_cellsReach`. -/
theorem breakout_reachAt {ptnN labN : Array Nat} {levN : Nat}
    {lab ptn : Array Nat} {level tc len o : Nat}
    (hreach : cellsPerm ptnN levN labN lab)
    (hcell : IsCell ptn level tc len) (hsize : tc + len ≤ ptn.size)
    (hszN : ptnN.size = ptn.size) (hlsz : lab.size = ptn.size)
    (ho : o < len)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hendN : ptnN[ptnN.size - 1]! ≤ levN)
    (hcoarse : ∀ q : Nat, ptnN[q]! ≤ levN → ptn[q]! ≤ level) :
    cellsPerm ptnN levN labN
      (breakout lab ptn (level + 1) tc lab[tc + o]!).1 := by
  have hstep := breakout_cellsPerm hcell hsize hlsz ho
  have hbsz : (breakout lab ptn (level + 1) tc
      lab[tc + o]!).1.size = ptn.size := by
    rw [breakout]
    rw [breakout_go_size, hlsz]
  exact cellsPerm_trans hreach
    (cellsPerm_coarsen hszN hlsz hbsz hstep hend hendN hcoarse)

/-- A scatter joining two labellings reachable from a node stabilizes
the node's cells: on every cell the scatter carries the first
labelling's contents to the second's, and both agree with the node's
own contents up to permutation, so the node labelling mapped through
the scatter is cell-wise a permutation of itself. This is how an
admitted generator (the scatter of a leaf labelling over `firstlab` or
`canonlab`) satisfies the `CellStab` hypothesis of
`childKey_of_orbPruned` at every node above both leaves. -/
theorem cellStab_of_scatter {ptnN labN lab₁ lab₂ γ : Array Nat}
    {levN : Nat} (hsp : ptnN.size = n) (hsN : labN.size = n)
    (hs1 : lab₁.size = n) (hendN : ptnN[ptnN.size - 1]! ≤ levN)
    (h1 : cellsPerm ptnN levN labN lab₁)
    (h2 : cellsPerm ptnN levN labN lab₂)
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!) :
    CellStab ptnN levN labN γ := by
  show cellsPerm ptnN levN labN (labN.map fun w => γ[w]!)
  refine cellsPerm_of_forall_cells hsp hsN
    (by rw [Array.size_map, hsN]) hendN ?_
  intro p hpm
  have hple := cells_le p hpm
  have hpb := cells_bound (Nat.le_of_eq hsp.symm) hendN p hpm
  have hic := cells_isCell (Nat.le_of_eq hsp.symm) hendN p hpm
  have hbnd : p.1 + (p.2 + 1 - p.1) ≤ n := by
    rw [hsp] at hpb
    omega
  have e1 : segN (labN.map fun w => γ[w]!) p.1 (p.2 + 1 - p.1) =
      (segN labN p.1 (p.2 + 1 - p.1)).map fun w => γ[w]! :=
    segN_map_of_le _ _ _ _ (by rw [hsN]; exact hbnd)
  have e2 : (segN lab₁ p.1 (p.2 + 1 - p.1)).map (fun w => γ[w]!) =
      segN (lab₁.map fun w => γ[w]!) p.1 (p.2 + 1 - p.1) :=
    (segN_map_of_le _ _ _ _ (by rw [hs1]; exact hbnd)).symm
  have e3 : segN (lab₁.map fun w => γ[w]!) p.1 (p.2 + 1 - p.1) =
      segN lab₂ p.1 (p.2 + 1 - p.1) :=
    segN_congr fun o ho => by
      rw [getElem!_map_of_lt _ _ (by rw [hs1]; omega)]
      exact hsc (p.1 + o) (by omega)
  refine List.Perm.symm ?_
  rw [e1]
  refine ((h1 p.1 _ hic).map _).trans ?_
  rw [e2, e3]
  exact (h2 p.1 _ hic).symm

/-- A checked automorphism stabilizing a node's cells still stabilizes
them after refinement: `refine` depends on the labelling only through
cell contents (`refine_perm`) and commutes with the automorphism's
renaming (`refine_map`), and the two transports meet at the refined
state. The descent-propagation clause of the stabilization
invariant. -/
theorem cellStab_refine {ctx : Ctx} (hn : ctx.n = n) {level : Nat}
    {lab ptn γ : Array Nat} {active numcells : Nat}
    (hstab : CellStab ptn level lab γ)
    (hgsz : ctx.g.size = n) (hca : checkAutom ctx.g γ n = true)
    (hsl : lab.size = n) (hlab : LabOk lab n) (hsp : ptn.size = n)
    (hact : active < 2 ^ n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, elem active v = true →
      v = 0 ∨ ptn[v - 1]! ≤ level) :
    CellStab (refine ctx level lab ptn active numcells).ptn level
      (refine ctx level lab ptn active numcells).lab γ := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hgsz hca
  have hmapeq : lab.map σ.toFun = lab.map fun w => γ[w]! :=
    map_congr_of_labOk hlab fun w hw => hσ w hw
  have hperm := refine_perm hn (lab' := lab.map fun w => γ[w]!)
    (active := active) (numcells := numcells) hstab
    (by rw [Array.size_map]) hsl hlab hsp hact hend hstarts
  have hmap := refine_map σ hn hn hrows level lab ptn active numcells
    hsl hlab hsp hact hend
  rw [hmapeq] at hmap
  rw [hmap] at hperm
  have hcells := hperm.cells
  have hout := refine_stOk hn (active := active)
    (numcells := numcells) hsl hlab hsp hact hend
  show cellsPerm (refine ctx level lab ptn active numcells).ptn level
    (refine ctx level lab ptn active numcells).lab
    ((refine ctx level lab ptn active numcells).lab.map fun w => γ[w]!)
  have hlabeq : (mapSt σ (refine ctx level lab ptn active
      numcells)).lab =
      (refine ctx level lab ptn active numcells).lab.map
        fun w => γ[w]! :=
    map_congr_of_labOk hout.labOk fun w hw => hσ w hw
  rw [← hlabeq]
  exact hcells

private theorem cellStab_breakout_go {ptn lab labB γ : Array Nat}
    {level tc len v : Nat} (hstab : CellStab ptn level lab γ)
    (hcell : IsCell ptn level tc len) (hsize : tc + len ≤ ptn.size)
    (hlsz : lab.size = ptn.size) (hlen2 : 2 ≤ len)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, ptn[q]! ≠ level + 1) (hfix : γ[v]! = v)
    (hBsz : labB.size = lab.size)
    (hseg : segN labB tc len = v :: (segN lab tc len).erase v)
    (houtL : ∀ q, q < tc → labB[q]! = lab[q]!)
    (houtR : ∀ q, tc + len ≤ q → labB[q]! = lab[q]!)
    (htvmem : v ∈ segN lab tc len) :
    cellsPerm (ptn.set! tc (level + 1)) (level + 1) labB
      (labB.map fun w => γ[w]!) := by
  have hsz : tc + len ≤ lab.size := by rw [hlsz]; exact hsize
  have hsegd : segN labB tc ((len - 1) + 1) =
      v :: (segN lab tc len).erase v := by
    rw [show (len - 1) + 1 = len from by omega]
    exact hseg
  rw [segN_cons] at hsegd
  have hhead : labB[tc]! = v := (List.cons.injEq _ _ _ _).mp hsegd |>.1
  have htail : segN labB (tc + 1) (len - 1) =
      (segN lab tc len).erase v :=
    (List.cons.injEq _ _ _ _).mp hsegd |>.2
  have hcellstab : (segN lab tc len).Perm
      ((segN lab tc len).map fun w => γ[w]!) := by
    have h := hstab tc len hcell
    rwa [segN_map_of_le _ _ _ _ hsz] at h
  refine cellsPerm_set! ((isCell_succ_iff hvals).mpr hcell) hsize
    (Nat.le_refl tc) (by omega) ?_ ?_ ?_
  · -- the individualized singleton, fixed by `γ`
    rw [show tc + 1 - tc = 1 from by omega,
      show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_cons,
      segN_zero, segN_zero, hhead,
      getElem!_map_of_lt _ _ (by rw [hBsz]; omega), hhead, hfix]
  · -- the remainder cell, by head cancellation in the target cell
    rw [show tc + len - (tc + 1) = len - 1 from by omega,
      segN_map_of_le _ _ _ _ (by rw [hBsz]; omega), htail]
    refine List.Perm.symm (List.Perm.cons_inv (a := v) ?_)
    have h1 : (v :: ((segN lab tc len).erase v).map fun w => γ[w]!) =
        ((v :: (segN lab tc len).erase v).map fun w => γ[w]!) := by
      rw [List.map_cons, hfix]
    rw [h1]
    refine ((List.perm_cons_erase htvmem).symm.map _).trans ?_
    exact hcellstab.symm.trans (List.perm_cons_erase htvmem)
  · -- untouched cells, stabilized already at the coarser level
    intro a len' hc' hdisj
    have hc := (isCell_succ_iff hvals).mp hc'
    rcases Nat.lt_or_ge a ptn.size with ha | ha
    · have hbound : a + len' ≤ ptn.size := by
        rcases Nat.lt_or_ge (a + len') (ptn.size + 1) with h1 | h1
        · omega
        · exfalso
          have hi := hc.2.2.1 (ptn.size - 1) (by omega) (by omega)
          omega
      have hB : segN labB a len' = segN lab a len' :=
        segN_congr fun o' ho' => by
          rcases hdisj with hd | hd
          · exact houtL _ (by omega)
          · exact houtR _ (by omega)
      rw [segN_map_of_le _ _ _ _ (by rw [hBsz, hlsz]; exact hbound),
        hB]
      have h := hstab a len' hc
      rwa [segN_map_of_le _ _ _ _ (by rw [hlsz]; exact hbound)] at h
    · have hlen0 := hc.1
      have hlen1 : len' = 1 := by
        rcases Nat.lt_or_ge len' 2 with h2 | h2
        · omega
        · exfalso
          have hi := hc.2.2.1 a (Nat.le_refl a) (by omega)
          rw [getElem!_neg _ _ (by omega)] at hi
          have hd : (default : Nat) = 0 := rfl
          omega
      subst hlen1
      rw [show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_cons,
        segN_zero, segN_zero, getElem!_neg labB _ (by omega),
        getElem!_neg (labB.map fun w => γ[w]!) _
          (by rw [Array.size_map]; omega)]

/-- A cell-stabilizing map fixing the individualized vertex still
stabilizes the cells after individualization: the singleton is fixed
outright, the remainder cell's stability follows from the target
cell's by head cancellation, and every other cell is untouched. The
individualization arm of descent propagation, paired with
`cellStab_refine`. -/
theorem cellStab_breakout {ptn lab γ : Array Nat}
    {level tc len o : Nat} (hstab : CellStab ptn level lab γ)
    (hcell : IsCell ptn level tc len) (hsize : tc + len ≤ ptn.size)
    (hlsz : lab.size = ptn.size) (ho : o < len) (hlen2 : 2 ≤ len)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, ptn[q]! ≠ level + 1)
    (hfix : γ[lab[tc + o]!]! = lab[tc + o]!) :
    CellStab (breakout lab ptn (level + 1) tc lab[tc + o]!).2.1
      (level + 1) (breakout lab ptn (level + 1) tc lab[tc + o]!).1
      γ := by
  have hsz : tc + len ≤ lab.size := by rw [hlsz]; exact hsize
  have hwit : ∃ kL, tc ≤ kL ∧ kL < tc + len ∧ kL < lab.size ∧
      lab[kL]! = lab[tc + o]! :=
    ⟨tc + o, by omega, by omega, by omega, rfl⟩
  show cellsPerm (ptn.set! tc (level + 1)) (level + 1)
    (breakout.go lab[tc + o]! (lab.size + 1) lab tc lab[tc + o]!)
    ((breakout.go lab[tc + o]! (lab.size + 1) lab tc
      lab[tc + o]!).map fun w => γ[w]!)
  refine cellStab_breakout_go hstab hcell hsize hlsz hlen2 hend hvals
    hfix (breakout_go_size _ _ _ _)
    (breakout_go_seg (lab.size + 1) len lab tc lab[tc + o]! hwit
      (by omega) hsz)
    (fun q hq => breakout_go_outside _ _ _ _ _ hq)
    (fun q hq => breakout_go_outside_right _ len _ _ _ hwit _ hq)
    (by
      rw [segN]
      exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩)

end Hex.GraphIso.Nauty
