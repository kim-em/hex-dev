/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeInduction
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.SmallCellTie

public section

/-!
Root-ledger preservation and leaf admission for the outcome-indexed search
induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Root-ledger entries -/

/-- A checked scatter between two reached labellings yields a valid
explicit autos-ledger entry at the initial coloured partition. -/
theorem pairOk_fmperm_of_reach {G : Colored n k} {ctx : Ctx}
    {lab₁ lab₂ γ : Array Nat}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hs₂ : lab₂.size = n) (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g γ ctx.n = true) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmperm γ ctx.n).1 (fmperm γ ctx.n).2 := by
  subst hn
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmperm hbg hroot.labOk hroot.labSize hroot.ptnSize
    hroot.ptnEnd hca
  exact cellStab_of_scatter hroot.ptnSize hroot.labSize hs₁
    hroot.ptnEnd hr₁ hr₂ hsc

/-- The finite array represented by a vertex renaming. -/
@[expose] def renamingArray (n : Nat) (sigma : Renaming n) : Array Nat :=
  .ofFn fun i : Fin n => sigma i

theorem renamingArray_size (sigma : Renaming n) :
    (renamingArray n sigma).size = n := by
  simp [renamingArray]

theorem renamingArray_get (sigma : Renaming n) {v : Nat} (hv : v < n) :
    (renamingArray n sigma)[v]! = sigma v := by
  rw [getElem!_pos _ _ (by rw [renamingArray_size]; exact hv)]
  simp [renamingArray]

private theorem map_range_get (a : Array Nat) (hs : a.size = n) :
    (List.range n).map (fun i => a[i]!) = a.toList := by
  refine List.ext_getElem (by simp [hs]) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos a i (by simpa using h₂)]
  simp

/-- A row-preserving renaming passes the concrete automorphism checker. -/
theorem checkAutom_renaming {ctx : Ctx} (sigma : Renaming ctx.n)
    (hrows : RowsMap sigma ctx.g ctx.g) :
    checkAutom ctx.g (renamingArray ctx.n sigma) ctx.n = true := by
  have hs := renamingArray_size sigma
  have hok : LabOk (renamingArray ctx.n sigma) ctx.n := by
    intro i hi
    rw [hs] at hi
    rw [renamingArray_get sigma hi]
    exact (sigma.maps i).mp hi
  have hinj : LabInj (renamingArray ctx.n sigma) ctx.n := by
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
theorem childKey_eq_of_subtree {ctx : Ctx} {st : RefineSt}
    {tcLevel fuel level tc len numcells oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n) (hoU : oU < len) (hoV : oV < len)
    (hfuel : level + 1 + fuel ≤ ctx.n + 1) :
    childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oV =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oU := by
  rcases Decidable.em (oU = oV) with rfl | hUV
  · rfl
  have hmem : (tc, tc + len - 1) ∈ cells st.ptn level ctx.n :=
    mem_cells_of_isCell (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
      hS.it.ok.ptnEnd
      hcell (by omega) (by rw [hS.it.ok.ptnSize]; exact hrange)
  have hdiff : tc + len - 1 - tc = len - 1 := by omega
  obtain ⟨sigma, hrows, hperm, hmap⟩ :=
    flipData_of_subtreeOk (oU := oU) (oV := oV) hS hgsz hgb hsymm hloop hmem
      (by omega) (by rw [hdiff]; omega) (by rw [hdiff]; omega) hUV
  let gamma := renamingArray ctx.n sigma
  have hstab : CellStab st.ptn level st.lab gamma := by
    change cellsPerm st.ptn level st.lab
      (st.lab.map fun w => gamma[w]!)
    have hmapLab : st.lab.map (fun w => gamma[w]!) =
        st.lab.map sigma.toFun :=
      map_congr_of_labOk hS.it.ok.labOk fun w hw =>
        renamingArray_get sigma hw
    rw [hmapLab]
    exact hperm.cells
  apply childKey_of_carried rfl hgsz (checkAutom_renaming sigma hrows)
    tcLevel fuel level hstab hS.it.ok.labSize hS.it.ok.labOk
    hS.it.ok.ptnSize hS.it.ok.ptnEnd (fun q => by
      rcases Decidable.em (q < ctx.n) with hq | hq
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

/-- If refinement exposes a small-cell node, its unpruned maximum is the
subtree below any chosen member of the specification target cell.  The
target is non-singleton, and the flip theorem makes every entry in its
finite maximum equal. -/
theorem nodeKey_eq_child_of_subtree {ctx : Ctx} {st : SearchSt}
    {tcLevel fuel level numcells tc len o : Nat} {codes : List Nat}
    (hS : SubtreeOk ctx level
      (refine ctx level st.lab st.ptn st.active numcells))
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hdisc : discreteAt
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level ctx.n = false)
    (hsize : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tcLevel).2.2 = len)
    (htc : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tcLevel).1 = tc)
    (hcell : IsCell
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen : 2 ≤ len) (hrange : tc + len ≤ ctx.n) (ho : o < len)
    (hfuel : level + 1 + fuel ≤ ctx.n + 1) :
    nodeKey ctx tcLevel (fuel + 1) level codes st numcells =
      sweepKey ctx tcLevel fuel level
        (codes ++ [(refine ctx level st.lab st.ptn st.active
          numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells o := by
  let r := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [r.longcode]
  let key := fun j => sweepKey ctx tcLevel fuel level full r.lab r.ptn tc
    r.numcells j
  have hkey : ∀ j, j < len → key j = key o := by
    intro j hj
    apply congrArg (prefixKey full)
    exact childKey_eq_of_subtree (tcLevel := tcLevel)
      (numcells := r.numcells) (oU := o) (oV := j) hS hgsz hgb
      hsymm hloop hcell hlen hrange ho hj hfuel
  have hchildren : nodeKey ctx tcLevel (fuel + 1) level codes st numcells =
      keysMax (key 0) ((List.range (len - 1)).map fun j => key (j + 1)) := by
    have hlen' : len = len - 1 + 1 := by omega
    have htarget : (specMaketargetcell ctx r.lab r.ptn level
        tcLevel).2.2 = len - 1 + 1 := by
      simpa only [r] using hsize.trans hlen'
    have hn := nodeKey_children (ctx := ctx) (tcLevel := tcLevel)
      (fuel := fuel) (level := level) (numcells := numcells)
      (cs := codes) (st := st) hdisc htarget
    simpa only [r, full, key, htc] using hn
  rw [hchildren]
  apply keysMax_eq_of_le
  · rw [hkey 0 (by omega)]
    exact keyLe_refl _
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have hj' := List.mem_range.mp hj
    rw [hkey (j + 1) (by omega)]
    exact keyLe_refl _
  · rcases Nat.eq_zero_or_pos o with rfl | hop
    · exact Or.inl rfl
    · right
      apply List.mem_map.mpr
      exact ⟨o - 1, List.mem_range.mpr (by omega),
        congrArg key (by omega)⟩

/-- The implicit pair recorded at a small-cell node is valid at the root
partition.  Its missing vertices are realized by the node's flip
automorphisms, while singleton cells supply the fixed set. -/
theorem pairOk_fmptn_of_subtree {ctx : Ctx} {G : Colored ctx.n k}
    {level : Nat} {r : RefineSt}
    (hn0 : 0 < ctx.n) (hlevel : 1 <= level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : forall v, v < ctx.n -> ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : forall u v, u < ctx.n -> v < ctx.n ->
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : forall v, v < ctx.n -> (ctx.g[v]!).testBit v = false)
    (hS : SubtreeOk ctx level r)
    (hreach : CellsReach G r.lab)
    (hinit : forall q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! <= 1 ->
        r.ptn[q]! <= 1) :
    PairOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmptn r.lab r.ptn level ctx.n).1
      (fmptn r.lab r.ptn level ctx.n).2 := by
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmptn
  · intro v hv
    obtain ⟨p, hp, hpv⟩ := labInj_surj
      (Nat.le_of_eq hS.it.ok.labSize.symm) hS.it.ok.labOk hS.it.inj v hv
    obtain ⟨c, hc, hp1, hp2⟩ := cells_cover p hp
    exact ⟨p, c.1, c.2, hc, hp1, hp2, hpv⟩
  · intro v c1 c2 hv hcell hp hq
    rcases hp with ⟨p, hp1, hp2, hpv⟩
    rcases hq with ⟨q, hq1, hq2, hqlt⟩
    have hoff : p - c1 ≠ q - c1 := by
      intro heq
      have : p = q := by omega
      subst q
      omega
    obtain ⟨sigma, hrows, hperm, hmap⟩ :=
      flipData_of_subtreeOk hS hgsz hgb hsymm hloop hcell
        (by omega) (by omega) (by omega) hoff
    let gamma := renamingArray ctx.n sigma
    refine ⟨gamma, checkAutom_renaming sigma hrows, ?_, ?_, ?_⟩
    · intro u hu hfix
      obtain ⟨c, hcellc, hcu⟩ := fmptn_fix hfix
      have hcb := cells_bound (Nat.le_of_eq hS.it.ok.ptnSize.symm)
        hS.it.ok.ptnEnd (c, c) hcellc
      have hc : c < r.lab.size := by
        rw [hS.it.ok.labSize, ← hS.it.ok.ptnSize]
        exact hcb
      have hic := cells_isCell
        (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
        hS.it.ok.ptnEnd (c, c) hcellc
      have heq := cellsPerm_singleton hperm.cells
        (show IsCell r.ptn level c 1 by simpa using hic)
      change r.lab[c]! = (r.lab.map sigma.toFun)[c]! at heq
      rw [getElem!_map_of_lt _ _ hc] at heq
      rw [renamingArray_get sigma hu]
      rw [← hcu]
      exact heq.symm
    · have hrootperm : cellsPerm
          (initPtn ctx.n (ctx.n + 2) (initialPartition G).2) 1
          r.lab (mapSt sigma r).lab := by
        apply cellsPerm_coarsen
            (ptnC := initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
            (ptnF := r.ptn) (levC := 1) (levF := level)
        · rw [size_initPtn, hS.it.ok.ptnSize]
        · rw [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · simp [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · exact hperm.cells
        · exact hS.it.ok.ptnEnd
        · exact hroot.ptnEnd
        · intro x hx
          exact Nat.le_trans (hinit x hx) hlevel
      apply cellStab_of_scatter hroot.ptnSize hroot.labSize
        hS.it.ok.labSize hroot.ptnEnd hreach
        (cellsPerm_trans hreach hrootperm)
      intro i hi
      have hil : i < r.lab.size := by rw [hS.it.ok.labSize]; exact hi
      have hv' := hS.it.ok.labOk i hil
      rw [renamingArray_get sigma hv']
      exact (getElem!_map_of_lt sigma.toFun r.lab hil).symm
    · have hσ := hmap
      simp only [Nat.add_sub_of_le hp1, Nat.add_sub_of_le hq1] at hσ
      rw [renamingArray_get sigma hv, ← hpv, ← hσ]
      rw [hpv]
      exact hqlt

/-- A guard-passing refined node supplies the pair needed to carry the
cheap-boundary invariant into its children. -/
theorem CheapOk.nextOfSubtree {ctx : Ctx} {G : Colored ctx.n k}
    {level : Nat} {st : SearchSt} {r : RefineSt}
    (h : CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2) level st)
    (hn0 : 0 < ctx.n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1)
    (hlab : st.lab = r.lab) (hptn : st.ptn = r.ptn) :
    CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (level + 1) st := by
  apply h.next
  intro hncl
  rw [hncl, hlab, hptn]
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hgb hsymm hloop hS
    hreach hinit

/-- Admitting a checked scatter between reached labellings preserves the
root automorphism ledger. -/
theorem AutosOk.pushFmperm {ctx : Ctx} {G : Colored n k}
    {st : SearchSt} {lab₁ lab₂ gamma : Array Nat}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hs₂ : lab₂.size = n) (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → gamma[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g gamma ctx.n = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (pushAuto st (fmperm gamma ctx.n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmperm_of_reach hn hn0 hgb hs₁ hr₁ hs₂ hr₂ hsc hca

/-- Recording the scan-free pair justified by a small-cell subtree
preserves the root automorphism ledger. -/
theorem AutosOk.pushFmptn {ctx : Ctx} {G : Colored ctx.n k}
    {st : SearchSt} {level : Nat} {r : RefineSt}
    (hn0 : 0 < ctx.n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hprev : AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1) :
    AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (pushAuto st (fmptn r.lab r.ptn level ctx.n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hgb hsymm hloop hS
    hreach hinit

/-- A successful code-one admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeAuto {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx
      (firstScatter ctx.n st.firstlab st.lab) = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  have hinj := labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach
  have hfirstOk := labOk_of_reach hrefs.firstSize hrefs.firstReach
  have hsc : ∀ i, i < ctx.n →
      (firstScatter ctx.n st.firstlab st.lab)[st.firstlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hfirstOk j (by rw [hrefs.firstSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (firstScatter ctx.n st.firstlab st.lab) ctx.n = true := by
    apply checkAutom_scatter_of_isautom
      (firstScatter_size ctx.n st.firstlab st.lab)
      hrefs.firstSize
      (isPerm_of_cellsReach hrefs.firstSize hn0 hrefs.firstReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega)) hsymm hloop hgb hpass
  rw [processnode_auto_autos heq hsent hnc hpass]
  exact hprev.pushFmperm rfl hn0 hgb hrefs.firstSize hrefs.firstReach
    hok.labSize hok.reach hsc hca

/-- A successful code-two admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeRowTie {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  have hcanonOk := labOk_of_reach hrefs.canonSize hrefs.canonReach
  have hinj := labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach
  have hsc : ∀ i, i < ctx.n →
      (canonScatter ctx.n st.canonlab st.lab)[st.canonlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    rw [canonScatter_eq_firstScatter]
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hcanonOk j (by rw [hrefs.canonSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (canonScatter ctx.n st.canonlab st.lab) ctx.n = true := by
    apply checkAutom_scatter_of_leafRows_eq
      (by rw [canonScatter_eq_firstScatter]; exact
        firstScatter_size ctx.n st.canonlab st.lab)
      hrefs.canonSize
      (isPerm_of_cellsReach hrefs.canonSize hn0 hrefs.canonReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega)) hgb
      (rows_eq_of_testcanlab_tie hcanong htie)
  rw [processnode_rowTie_autos hef hnc hcc hge htie]
  exact hprev.pushFmperm rfl hn0 hgb hrefs.canonSize hrefs.canonReach
    hok.labSize hok.reach hsc hca

/-- The shared code-three/code-four tail preserves the ledger whenever
its optional implicit pair is valid. -/
theorem AutosOk.pruneAutos {ctx : Ctx} {G : Colored n k}
    {level : Nat} {st : SearchSt}
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n (pruneAutos ctx level st) := by
  unfold Hex.GraphIso.Nauty.pruneAutos
  split
  · exact hprev
  · exact autosOk_pushAuto hprev (hpair (by assumption))

private theorem processnode_plain_autos {ctx : Ctx}
    {level numcells : Nat} {st : SearchSt}
    (hfast : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == ctx.n) = true)) :
    (processnode ctx level numcells st).2.autos = st.autos := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.autos)]
  simp [hfast, hnc]

/-- On a non-discrete node admitted to its child sweep, `processnode`
performs no state update. -/
theorem processnode_internal {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt}
    (hgate : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == ctx.n) = true)) :
    processnode ctx level numcells st = (Int.ofNat level, st) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  simp [hgate, hnc]

/-- Off the first path, `processnode` preserves the root ledger in every
comparison-machine outcome. -/
theorem AutosOk.processnodeOff {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2)
    (hef : ¬((st.eqlevFirst == level) = true)) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  have hef' : st.eqlevFirst ≠ level := fun he => hef (beq_iff_eq.mpr he)
  have hprune := hprev.pruneAutos hpair
  rcases hcode.tri with hzero | ⟨j, hj1, hjc, hjb, heqlev, hpre, hcase⟩
  · have hcc : st.compCanon = 0 := hzero.1
    rcases hnc : (numcells == ctx.n) with _ | _
    · rw [processnode_plain_autos (by rw [hcc]; omega)
          (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == ctx.n) = true := hnc
      rcases Decidable.em (level < st.canonlevel) with hlt | hge
      · rw [processnode_shortInstall_autos hef hnc' hcc hlt]
        exact hprune
      · let row := (testcanlab ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        rcases Int.lt_trichotomy row 0 with hrow | hrow | hrow
        · rw [processnode_rowReject_autos hef hnc' hcc hge hrow]
          exact hprune
        · exact hprev.processnodeRowTie hn hn0 hgb hok hrefs hcanong
            hef hnc' hcc hge hrow
        · rw [processnode_rowInstall_autos hef hnc' hcc hge hrow]
          exact hprune
  · rcases hcase with hdown | hup
    · have hcc : st.compCanon = -1 := hdown.1
      rw [processnode_fast_autos ⟨hef', by rw [hcc]; omega⟩]
      exact hprune
    · have hcc : st.compCanon = 1 := hup.1
      rcases hnc : (numcells == ctx.n) with _ | _
      · rw [processnode_plain_autos (by rw [hcc]; omega)
            (by simp [hnc])]
        exact hprev
      · have hnc' : (numcells == ctx.n) = true := hnc
        rw [processnode_upInstall_autos hef hnc' hcc]
        exact hprune

/-- A failed first-path generator gate reduces to the ordinary off-path
ledger proof once canonical-labelling validity discharges the reused
workspace overwrite. -/
theorem AutosOk.processnodeGateFail {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2)
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == ctx.n) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter ctx.n st.firstlab st.lab) = false) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  let off := { st with eqlevFirst := level + 1 }
  have hoff : AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells off).2.autos := by
    apply AutosOk.processnodeOff rfl hn0 hgb (st := off) (cs := cs)
      (bs := bs)
    · exact ⟨hok.labSize, hok.ptnSize, hok.reach, hok.init1, hok.vals,
        hok.count, hok.bc, hok.canon⟩
    · exact ⟨hrefs.firstSize, hrefs.firstReach, hrefs.canonSize,
        hrefs.canonReach⟩
    · change CanongInv ctx st.canong st.canonlab st.samerows
      exact hcanong
    · change CodeCmpInv ctx.n cs bs st.canoncode st.canonlevel
        st.eqlevCanon st.compCanon
      exact hcode
    · change AutosOk ctx.g
        (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n st.autos
      exact hprev
    · change level ≠ st.noncheaplevel →
        PairOk ctx.g
          (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
          (initialPartition G).1 1 ctx.n
          (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
          (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2
      exact hpair
    · simp [off]
  rw [processnode_gateFail_autos hrefs.canonSize
    (labOk_of_reach hrefs.canonSize hrefs.canonReach)
    (labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach)
    heq hnc hfail]
  exact hoff

/-- `processnode` preserves the root automorphism ledger in every leaf,
internal, generator, and comparison-prune outcome. -/
theorem AutosOk.processnode {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  rcases heq : (st.eqlevFirst == level) with _ | _
  · exact hprev.processnodeOff hn hn0 hgb hok hrefs hcanong hcode
      hpair (by
        intro htrue
        rw [heq] at htrue
        exact Bool.noConfusion htrue)
  · rcases hnc : (numcells == ctx.n) with _ | _
    · rw [processnode_plain_autos
        (by intro h; exact h.1 (beq_iff_eq.mp heq)) (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == ctx.n) = true := hnc
      rcases hsent : (st.firstcode[level + 1]! == codeSentinel) with _ | _
      · apply hprev.processnodeGateFail hn hn0 hgb hok hrefs hcanong hcode
          hpair heq hnc'
        exact Or.inl (by simpa only [beq_eq_false_iff_ne] using hsent)
      · have hsent' : st.firstcode[level + 1]! = codeSentinel :=
          beq_iff_eq.mp hsent
        rcases hpass : isautom ctx
            (firstScatter ctx.n st.firstlab st.lab) with _ | _
        · apply hprev.processnodeGateFail hn hn0 hgb hok hrefs hcanong
            hcode hpair heq hnc'
          exact Or.inr hpass
        · exact hprev.processnodeAuto hn hn0 hgb hsymm hloop hok hrefs
            heq hsent' hnc' hpass

/-- The stable search invariant now discharges the last independent
ledger premise of `processnode`: the runtime bound selects the frozen
pair carried by `CheapOk`. -/
theorem RunInv.processnodeAutos {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn hn0 hgb hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- The prepared state also discharges the root-ledger premise of a leaf
event; unlike `RunInv`, it permits the positive comparison sign produced
by the immediately preceding code comparison. -/
theorem RunPrep.processnodeAutos {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn hn0 hgb hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- An ordinary off-first-path discrete leaf turns the prepared state
into an event state whose incumbent is exactly the maximum of the old
incumbent and that leaf.  The return disjunction is retained for the
node outcome split. -/
theorem RunPrep.leaf {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail) :
    ∃ bs' : List Nat,
      RunEvent G ctx tcLevel level cs bs' fs
        (processnode ctx level numcells st).2
        (some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab)) trail ∧
      incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab) (pathLeafKey ctx cs st.lab) ∧
      ((processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∨
        (processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  subst level
  have hcsn : cs.length ≤ n := by
    have hb := bcount_le st.ptn cs.length n
    have hc := h.searchOk.bc
    omega
  obtain ⟨bs', hmax, hcanong, hmachines, hreturn⟩ :=
    processnode_leaf h.codeInv h.canongInv hcsn hef hnc
  have hcs : cs ≠ [] := by
    intro he
    subst cs
    simp at hlevel
  have hbs' : bs' ≠ [] :=
    incKey_max_nonempty h.bestCodes hcs hmax
  have hinc : IncGrows best
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) := by
    intro b hb
    rw [h.incumbent] at hb
    injection hb with hb
    subst b
    refine ⟨incKey ctx bs'
      (processnode ctx cs.length numcells st).2.canonlab, rfl, ?_⟩
    rw [hmax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  obtain ⟨hlab, hptn, heqFirst, hfirstCode, hfirstlab, -, hgcaFirst,
      -, -⟩ := processnode_frames ctx cs.length numcells st
  have hguides : GuideStore ctx tcLevel cs.length
      (processnode ctx cs.length numcells st).2
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) trail := by
    apply h.guides.processnode hinc hgcaFirst hfirstlab
    intro hlt
    rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · exact hold
    · rw [hnew.1] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn hn0 hgb hsymm hloop hbound
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew.1]
      exact hlevel
  · rw [hgcaFirst]
    exact h.firstBound
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonBound
    · rw [hnew.1]
      exact Nat.le_refl _

/-- A first-path-agreeing leaf whose generator admission guard fails has
the same exact event invariant as an ordinary compared leaf. -/
theorem RunPrep.leafFirst {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (heq : (st.eqlevFirst == level) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter ctx.n st.firstlab st.lab) = false)
    (hnc : (numcells == ctx.n) = true)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail) :
    ∃ bs' : List Nat,
      RunEvent G ctx tcLevel level cs bs' fs
        (processnode ctx level numcells st).2
        (some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab)) trail ∧
      incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab) (pathLeafKey ctx cs st.lab) ∧
      ((processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∨
        (processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  subst level
  have hcsn : cs.length ≤ n := by
    have hb := bcount_le st.ptn cs.length n
    have hc := h.searchOk.bc
    omega
  obtain ⟨bs', hmax, hcanong, hmachines, hreturn⟩ :=
    processnode_leafFirst h.codeInv h.canongInv hcsn heq hnc hfail
  have hcs : cs ≠ [] := by
    intro he
    subst cs
    simp at hlevel
  have hbs' : bs' ≠ [] :=
    incKey_max_nonempty h.bestCodes hcs hmax
  have hinc : IncGrows best
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) := by
    intro b hb
    rw [h.incumbent] at hb
    injection hb with hb
    subst b
    refine ⟨incKey ctx bs'
      (processnode ctx cs.length numcells st).2.canonlab, rfl, ?_⟩
    rw [hmax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  obtain ⟨-, -, heqFirst, hfirstCode, hfirstlab, -, hgcaFirst,
      -, -⟩ := processnode_frames ctx cs.length numcells st
  have hguides : GuideStore ctx tcLevel cs.length
      (processnode ctx cs.length numcells st).2
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) trail := by
    apply h.guides.processnode hinc hgcaFirst hfirstlab
    intro hlt
    rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · exact hold
    · rw [hnew.1] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn hn0 hgb hsymm hloop hbound
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew.1]
      exact hlevel
  · rw [hgcaFirst]
    exact h.firstBound
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonBound
    · rw [hnew.1]
      exact Nat.le_refl _

end Hex.GraphIso.Nauty
