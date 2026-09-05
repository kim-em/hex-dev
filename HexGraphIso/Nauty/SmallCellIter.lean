/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellBranch
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix

public section

/-!
The cheapautom subtree iteration (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

`HexGraphIso.Nauty.SmallCellBranch` relates the two children of a pair
target cell by the flip at a single level; this file carries the
relation down the subtree. The mechanism is a bisimulation: a state
whose labelling is cell-equivalent to a renamed copy of another
state's stays so after both individualize corresponding vertices and
refine (`stPerm_child`), so a whole descent below one state mirrors
below the other (`descends_transport`), and at discrete leaves the
renaming is absorbed by `leafRows_map` (`descends_leafRows`). Gluing
`branch_step` at the deviation level gives the single-deviation
theorem: any leaf reached below the second child of a pair target has
the same leaf rows as the mirrored leaf below the first child
(`deviation_leafRows`).

Remaining on top of this file: the triple analogues (the unique
triple's transpositions preserve rows, giving the branch step at
triple targets), the all-leaves induction over the fixed target
policy, the `noncheaplevel` event lemma, and the arm-2 assembly in
`StoreValid.lean` — plus the exotic defect-four configurations, which
the probe showed are conformance-reachable and need their own flip
analogues.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Window effect of individualization

`breakout` rotates the target value to the front of its cell window
and touches nothing outside it; the rotated window is the value
followed by the window with its first occurrence erased. -/

/-- The rotated target window. -/
theorem breakout_segN_target {lab ptn : Array Nat}
    {level tc len tv : Nat}
    (hw : ∃ k, tc ≤ k ∧ k < tc + len ∧ k < lab.size ∧ lab[k]! = tv)
    (hsz : tc + len ≤ lab.size) :
    segN (breakout n lab ptn level tc tv).1 tc len =
      tv :: (segN lab tc len).erase tv := by
  show segN (breakout.go tv (lab.size + 1) lab tc tv) tc len = _
  exact breakout_go_seg (lab.size + 1) len lab tc tv hw (by omega) hsz

/-- The individualized vertex lands at the front of its cell. -/
theorem breakout_getElem!_front {lab ptn : Array Nat}
    {level tc len tv : Nat}
    (hw : ∃ k, tc ≤ k ∧ k < tc + len ∧ k < lab.size ∧ lab[k]! = tv)
    (hlen : 0 < len) (hsz : tc + len ≤ lab.size) :
    (breakout n lab ptn level tc tv).1[tc]! = tv := by
  have h := breakout_segN_target (n := n) (ptn := ptn) (level := level) hw hsz
  rw [show len = (len - 1) + 1 by omega, segN_cons] at h
  injection h

/-- The remainder window after the rotation: the cell with its first
occurrence of the value erased. -/
theorem breakout_segN_rest {lab ptn : Array Nat}
    {level tc len tv : Nat}
    (hw : ∃ k, tc ≤ k ∧ k < tc + len ∧ k < lab.size ∧ lab[k]! = tv)
    (hlen : 0 < len) (hsz : tc + len ≤ lab.size) :
    segN (breakout n lab ptn level tc tv).1 (tc + 1) (len - 1) =
      (segN lab tc len).erase tv := by
  have h := breakout_segN_target (n := n) (ptn := ptn) (level := level) hw hsz
  rw [show len = (len - 1) + 1 by omega, segN_cons] at h
  injection h with h1 h2
  rw [show (len - 1) + 1 = len by omega] at h2
  exact h2

/-- Windows outside the rotated cell are untouched. -/
theorem breakout_segN_outside {lab ptn : Array Nat}
    {level tc len tv a alen : Nat}
    (hw : ∃ k, tc ≤ k ∧ k < tc + len ∧ k < lab.size ∧ lab[k]! = tv)
    (hout : a + alen ≤ tc ∨ tc + len ≤ a) :
    segN (breakout n lab ptn level tc tv).1 a alen = segN lab a alen := by
  refine segN_congr fun o ho => ?_
  show (breakout.go tv (lab.size + 1) lab tc tv)[a + o]! = lab[a + o]!
  rcases hout with h | h
  · exact breakout_go_outside _ _ _ _ _ (by omega)
  · exact breakout_go_outside_right _ len _ _ _ hw _ (by omega)

/-! # List toolkit -/

/-- Erasure commutes with an injective map. -/
private theorem map_erase_of_inj {f : Nat → Nat}
    (hinj : ∀ a b, f a = f b → a = b) :
    ∀ (l : List Nat) (a : Nat),
      (l.erase a).map f = (l.map f).erase (f a)
  | [], _ => rfl
  | b :: t, a => by
    rcases Decidable.em (b = a) with rfl | hne
    · rw [List.erase_cons_head, List.map_cons, List.erase_cons_head]
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hne),
        List.map_cons, List.map_cons,
        List.erase_cons_tail (by
          simp only [beq_iff_eq]
          exact fun h => hne (hinj _ _ h)),
        map_erase_of_inj hinj t a]

/-- Erasure preserves permutation equivalence. -/
private theorem perm_erase {l1 l2 : List Nat} (a : Nat)
    (h : l1.Perm l2) : (l1.erase a).Perm (l2.erase a) := by
  rcases Decidable.em (a ∈ l1) with hm | hm
  · have hm2 : a ∈ l2 := h.mem_iff.mp hm
    have h1 := List.perm_cons_erase hm
    have h2 := List.perm_cons_erase hm2
    exact List.Perm.cons_inv ((h1.symm.trans h).trans h2)
  · have hm2 : a ∉ l2 := fun hx => hm (h.mem_iff.mpr hx)
    rw [List.erase_of_not_mem hm, List.erase_of_not_mem hm2]
    exact h

/-! # Corresponding individualization

Two labellings whose cells are equivalent up to a renaming stay so
after individualizing corresponding vertices: the split singletons
match by the correspondence, the remainders by erasing it, and the
untouched cells by the parent equivalence. -/

/-- Individualizing corresponding vertices preserves the renamed cell
equivalence on the split partition. -/
theorem breakout_cellsPerm_map {σ : Renaming n}
    {labV labU ptn : Array Nat} {level tc e oV oU : Nat}
    (hpsz : ptn.size = n)
    (hVsz : labV.size = n) (hUsz : labU.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hcp : cellsPerm ptn level labV (labU.map σ.toFun))
    (hcell : (tc, e) ∈ cells ptn level n) (hne : tc < e)
    (hoV : oV ≤ e - tc) (hoU : oU ≤ e - tc)
    (hvv : labV[tc + oV]! = σ.toFun labU[tc + oU]!) :
    cellsPerm (ptn.set! tc (level + 1)) (level + 1)
      (breakout n labV ptn (level + 1) tc labV[tc + oV]!).1
      (((breakout n labU ptn (level + 1) tc
        labU[tc + oU]!).1).map σ.toFun) := by
  intro a len hIs
  have hen : e < n := target_end_lt hpsz hend hcell
  have hlenT : 0 < e + 1 - tc := by omega
  have hwV : ∃ k, tc ≤ k ∧ k < tc + (e + 1 - tc) ∧ k < labV.size ∧
      labV[k]! = labV[tc + oV]! :=
    ⟨tc + oV, by omega, by omega, by omega, rfl⟩
  have hwU : ∃ k, tc ≤ k ∧ k < tc + (e + 1 - tc) ∧ k < labU.size ∧
      labU[k]! = labU[tc + oU]! :=
    ⟨tc + oU, by omega, by omega, by omega, rfl⟩
  have hVbsz : (breakout n labV ptn (level + 1) tc
      labV[tc + oV]!).1.size = n := by
    rw [breakout_lab_size, hVsz]
  have hUbsz : (breakout n labU ptn (level + 1) tc
      labU[tc + oU]!).1.size = n := by
    rw [breakout_lab_size, hUsz]
  have hsz' : (ptn.set! tc (level + 1)).size = n := by
    rw [Array.size_set!, hpsz]
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz', ← hpsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hcellIs : IsCell ptn level tc (e + 1 - tc) := by
    have h := cells_isCell (by omega) hend _ hcell
    exact h
  rcases Decidable.em (a < n) with han | han
  · have hcross : a + len ≤ n := by
      have := isCell_no_cross hend' hIs (by omega)
      omega
    have hmem : (a, a + len - 1) ∈
        cells (ptn.set! tc (level + 1)) (level + 1) n :=
      mem_cells_of_isCell (by omega) hend' hIs han (by omega)
    have hpos := hIs.1
    rcases child_cells_cases hpsz hend hvals hcell hne hmem with
      heq | heq | ⟨hmemP, hane⟩
    · -- the split-off singleton
      have h1 : a = tc := congrArg Prod.fst heq
      have h2 : a + len - 1 = tc := congrArg Prod.snd heq
      have hlen1 : len = 1 := by omega
      subst h1
      rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
      rw [breakout_getElem!_front hwV hlenT (by omega)]
      rw [getElem!_map_of_lt _ _ (by rw [hUbsz]; omega),
        breakout_getElem!_front hwU hlenT (by omega), ← hvv]
    · -- the remainder
      have h1 : a = tc + 1 := congrArg Prod.fst heq
      have h2 : a + len - 1 = e := congrArg Prod.snd heq
      have hlen2 : len = e - tc := by omega
      subst h1
      rw [hlen2,
        show e - tc = (e + 1 - tc) - 1 by omega,
        breakout_segN_rest hwV hlenT (by omega)]
      have hmapseg : segN ((breakout n labU ptn (level + 1) tc
          labU[tc + oU]!).1.map σ.toFun) (tc + 1) (e + 1 - tc - 1) =
          ((segN labU tc (e + 1 - tc)).erase labU[tc + oU]!).map
            σ.toFun := by
        rw [segN_map (by rw [hUbsz]; omega),
          breakout_segN_rest hwU hlenT (by omega)]
      rw [hmapseg,
        map_erase_of_inj σ.inj, ← hvv]
      refine perm_erase _ ?_
      have h := hcp tc (e + 1 - tc) hcellIs
      rwa [segN_map (by omega)] at h
    · -- an untouched parent cell
      obtain ⟨hq1, hq2, hqe⟩ :=
        (mem_cells_iff (by omega) hend).mp hmemP
      have hout : a + len - 1 < tc ∨ e < a := by
        rcases Decidable.em (a < tc) with hlt | hge
        · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
          have htcs : ptn[tc - 1]! ≤ level := by
            rcases h2t with h0 | hcl
            · omega
            · exact hcl
          refine Or.inl ?_
          rw [hqe]
          exact cellEnd_lt_start hlt htcs
        · refine Or.inr ?_
          rcases Decidable.em (a ≤ e) with hle | hgt
          · exfalso
            have hop := target_open hpsz hend hcell (a - 1) (by omega)
              (by omega)
            rcases hq2 with h0 | hcl
            · omega
            · omega
          · omega
      have hout' : a + len ≤ tc ∨ tc + (e + 1 - tc) ≤ a := by
        rcases hout with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hIsP : IsCell ptn level a len := by
        have h := cells_isCell (by omega) hend _ hmemP
        rw [show a + len - 1 + 1 - a = len by omega] at h
        exact h
      rw [breakout_segN_outside hwV hout']
      have hmapseg : segN ((breakout n labU ptn (level + 1) tc
          labU[tc + oU]!).1.map σ.toFun) a len =
          segN (labU.map σ.toFun) a len := by
        rw [segN_map (by rw [hUbsz]; omega),
          breakout_segN_outside hwU hout',
          ← segN_map (by omega)]
      rw [hmapseg]
      exact hcp a len hIsP
  · -- beyond the bound: phantom singletons
    have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
    rw [getElem!_oob (by omega : (breakout n labV ptn (level + 1) tc
        labV[tc + oV]!).1.size ≤ a)]
    rw [getElem!_oob (by
      rw [Array.size_map]
      omega : ((breakout n labU ptn (level + 1) tc
        labU[tc + oU]!).1.map σ.toFun).size ≤ a)]

/-! # Renamed and permuted labelling facts -/

/-- A renaming keeps every entry a vertex. -/
theorem labOk_map {n : Nat} (σ : Renaming n) {lab : Array Nat}
    (h : LabOk lab n) : LabOk (lab.map σ.toFun) n := by
  intro i hi
  rw [Array.size_map] at hi
  rw [getElem!_map_of_lt _ _ hi]
  exact (σ.maps _).mp (h i hi)

/-- A renaming keeps a labelling injective. -/
theorem labInj_map {n : Nat} (σ : Renaming n) {lab : Array Nat}
    (h : LabInj lab n) (hsz : lab.size = n) :
    LabInj (lab.map σ.toFun) n := by
  intro i j hi hj he
  rw [getElem!_map_of_lt _ _ (by omega),
    getElem!_map_of_lt _ _ (by omega)] at he
  exact h i j hi hj (σ.inj _ _ he)

/-- A whole-segment permutation keeps every entry a vertex. -/
theorem labOk_of_perm {lab lab' : Array Nat} {nn : Nat}
    (hp : (segN lab' 0 nn).Perm (segN lab 0 nn))
    (h : LabOk lab nn) (hsz : lab.size = nn) (hsz' : lab'.size = nn) :
    LabOk lab' nn := by
  intro i hi
  rw [hsz'] at hi
  have hm : lab'[i]! ∈ segN lab' 0 nn :=
    mem_segN_iff.mpr ⟨i, hi, by rw [Nat.zero_add]⟩
  obtain ⟨o, ho, hov⟩ := mem_segN_iff.mp (hp.mem_iff.mp hm)
  rw [← hov]
  exact h (0 + o) (by omega)

/-! # The subtree step and its node invariant -/

/-- One individualize-and-refine step of the search subtree. -/
@[expose] def childSt (ctx : Ctx n) (level : Nat) (st : RefineSt n)
    (tc tv : Nat) : RefineSt n :=
  refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc tv).1
    (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (st.numcells + 1)

/-- The facts carried at every node of the subtree: state
well-formedness, an injective labelling, and the partition-value
dichotomy (closed at the level or the open marker). -/
structure IterOk (ctx : Ctx n) (level : Nat) (st : RefineSt n) : Prop where
  ok : StOk n level st
  inj : LabInj st.lab n
  vals : ∀ q, q < n → st.ptn[q]! ≤ level ∨ st.ptn[q]! = n + 2
  lvl : level ≤ n

/-- The weak value dichotomy the classification lemmas consume. -/
theorem IterOk.valsWeak {st : RefineSt n} {level : Nat}
    (h : IterOk ctx level st) :
    ∀ q, q < n → st.ptn[q]! ≤ level ∨ level + 1 < st.ptn[q]! := by
  intro q hq
  rcases h.vals q hq with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have := h.lvl
    omega

/-- The final position of the split partition stays closed. -/
private theorem setTc_end {ptn : Array Nat} {level tc : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) (htc : tc < ptn.size) :
    (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
  rw [Array.size_set!]
  rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
  · rw [Array.getElem!_set!_self _ _ _ (by omega)]
    omega
  · rw [Array.getElem!_set!_ne _ _ _ _ hx]
    omega

/-- The singleton active position is a cell start of the split
partition. -/
private theorem setTc_starts {ptn : Array Nat} {level tc e : Nat}
    (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hcell : (tc, e) ∈ cells ptn level n) :
    ∀ v : Nat, ((VSet.empty : VSet n).insert tc).mem v = true →
      v = 0 ∨ (ptn.set! tc (level + 1))[v - 1]! ≤ level + 1 := by
  intro v hv
  have hen := target_end_lt hpsz hend hcell
  have hle := cells_le _ hcell
  rw [mem_single (by omega)] at hv
  have hvtc : v = tc := of_decide_eq_true hv
  subst hvtc
  obtain ⟨-, hstart, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
  rcases Decidable.em (v = 0) with h00 | h00
  · exact Or.inl h00
  · rcases hstart with h0 | hcl
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      omega

/-- The node invariant survives one subtree step. -/
theorem iterOk_child {st : RefineSt n} {level tc e o : Nat}
    (h : IterOk ctx level st) (hlvl : level < n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    IterOk ctx (level + 1) (childSt ctx level st tc st.lab[tc + o]!) := by
  have hpsz := h.ok.ptnSize
  have hlsz := h.ok.labSize
  have hend := h.ok.ptnEnd
  have hen : e < n := target_end_lt hpsz hend hcell
  have hinj' : LabInj st.lab st.lab.size := by
    rw [hlsz]
    exact h.inj
  have hto : tc + o < st.lab.size := by rw [hlsz]; omega
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1.size = n := by
    rw [breakout_lab_size, hlsz]
  have hbOk : LabOk (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1 n := labOk_breakout hinj' hto h.ok.labOk
  have hbinj : LabInj (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1 n := by
    have hb := labInj_breakout (n := n) (ptn := st.ptn) (level := level)
      (tc := tc) (o := o) hinj' hto
    rw [hlsz] at hb
    exact hb
  have hsz' : (st.ptn.set! tc (level + 1)).size = n := by
    rw [Array.size_set!, hpsz]
  have hend' := setTc_end (level := level) (tc := tc) hend (by omega)
  have hok : StOk n (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) :=
    refine_stOk (ctx := ctx) (active := VSet.empty.insert tc) hbsz hbOk hsz' hend'
  refine ⟨hok, ?_, ?_, by omega⟩
  · have hRI := refine_refInv (ctx := ctx) (level := level + 1)
      (lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1)
      (ptn := st.ptn.set! tc (level + 1))
      (active := VSet.empty.insert tc) (numcells := st.numcells + 1)
      (by omega) (by rw [hbsz, hsz']) hend'
    have hendn' : (st.ptn.set! tc (level + 1))[n - 1]! ≤
        level + 1 := by
      have h := hend'
      rw [hsz'] at h
      exact h
    exact labInj_of_perm
      (cellsPerm_segN_perm hRI.perm (by omega) hend' hendn').symm hbinj
  · intro q hq
    rcases ptn_refine_vals ctx (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
      (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
      (st.numcells + 1) q with hold | hnew
    · rw [childSt] at *
      rw [hold]
      rcases Decidable.em (q = tc) with rfl | hqne
      · rw [Array.getElem!_set!_self _ _ _ (by omega)]
        exact Or.inl (Nat.le_refl _)
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun hx => hqne hx.symm)]
        rcases h.vals q hq with h1 | h1
        · exact Or.inl (by omega)
        · exact Or.inr h1
    · rw [childSt] at *
      rw [hnew]
      exact Or.inl (Nat.le_refl _)

/-- The node invariant transports across the renamed cell
equivalence. -/
theorem iterOk_of_stPerm {σ : Renaming n} {V U : RefineSt n}
    {level : Nat} (hU : IterOk ctx level U)
    (hsp : StPerm level V (mapSt σ U)) : IterOk ctx level V := by
  have hptn : U.ptn = V.ptn := hsp.ptn
  have hlszm : (U.lab.map σ.toFun).size = V.lab.size := hsp.labSize
  have hlsz : V.lab.size = n := by
    rw [← hlszm, Array.size_map]
    exact hU.ok.labSize
  have hUlsz := hU.ok.labSize
  have hpszV : V.ptn.size = n := by
    rw [← hptn]
    exact hU.ok.ptnSize
  have hendV : V.ptn[V.ptn.size - 1]! ≤ level := by
    rw [← hptn]
    exact hU.ok.ptnEnd
  have hendn : V.ptn[n - 1]! ≤ level := by
    have h := hendV
    rw [hpszV] at h
    exact h
  have hcells : cellsPerm V.ptn level V.lab (U.lab.map σ.toFun) :=
    hsp.cells
  have hw : (segN V.lab 0 n).Perm
      (segN (U.lab.map σ.toFun) 0 n) :=
    cellsPerm_segN_perm hcells (by omega) hendV hendn
  have hactV : V.active = U.active := (hsp.active).symm
  refine ⟨⟨hlsz, ?_, hpszV, hendV⟩, ?_, ?_, hU.lvl⟩
  · exact labOk_of_perm hw (labOk_map σ hU.ok.labOk)
      (by rw [Array.size_map, hUlsz]) hlsz
  · exact labInj_of_perm hw (labInj_map σ hU.inj hUlsz)
  · intro q hq
    rw [← hptn]
    exact hU.vals q hq

/-! # The bisimulation step -/

/-- Cell equivalence up to a row-preserving renaming survives
individualizing corresponding vertices and refining. -/
theorem stPerm_child {σ : Renaming n} {V U : RefineSt n}
    {level tc e oV oU : Nat}
    (hg : RowsMap σ ctx.g ctx.g)
    (hsp : StPerm level V (mapSt σ U))
    (hU : IterOk ctx level U)
    (hcell : (tc, e) ∈ cells U.ptn level n) (hne : tc < e)
    (hoV : oV ≤ e - tc) (hoU : oU ≤ e - tc)
    (hvv : V.lab[tc + oV]! = σ.toFun U.lab[tc + oU]!) :
    StPerm (level + 1) (childSt ctx level V tc V.lab[tc + oV]!)
      (mapSt σ (childSt ctx level U tc U.lab[tc + oU]!)) := by
  have hV := iterOk_of_stPerm hU hsp
  have hptn : U.ptn = V.ptn := hsp.ptn
  have hnum : U.numcells = V.numcells := hsp.numcells
  have hpszV := hV.ok.ptnSize
  have hVsz := hV.ok.labSize
  have hUsz := hU.ok.labSize
  have hendV := hV.ok.ptnEnd
  have hcellV : (tc, e) ∈ cells V.ptn level n := by
    rw [← hptn]
    exact hcell
  have hen : e < n := target_end_lt hpszV hendV hcellV
  have hbcp := breakout_cellsPerm_map (σ := σ) (ptn := V.ptn)
    hpszV hVsz hUsz hendV hV.valsWeak hsp.cells hcellV hne hoV hoU hvv
  have hUinj' : LabInj U.lab U.lab.size := by
    rw [hUsz]
    exact hU.inj
  have hVinj' : LabInj V.lab V.lab.size := by
    rw [hVsz]
    exact hV.inj
  have hVbsz : (breakout n V.lab V.ptn (level + 1) tc
      V.lab[tc + oV]!).1.size = n := by
    rw [breakout_lab_size, hVsz]
  have hUbsz : (breakout n U.lab V.ptn (level + 1) tc
      U.lab[tc + oU]!).1.size = n := by
    rw [breakout_lab_size, hUsz]
  have hVbOk : LabOk (breakout n V.lab V.ptn (level + 1) tc
      V.lab[tc + oV]!).1 n :=
    labOk_breakout hVinj' (by rw [hVsz]; omega) hV.ok.labOk
  have hUbOk : LabOk (breakout n U.lab V.ptn (level + 1) tc
      U.lab[tc + oU]!).1 n :=
    labOk_breakout hUinj' (by rw [hUsz]; omega) hU.ok.labOk
  have hsz' : (V.ptn.set! tc (level + 1)).size = n := by
    rw [Array.size_set!, hpszV]
  have hend' := setTc_end (level := level) (tc := tc) hendV
    (by omega)
  have hstarts := setTc_starts hpszV hendV hcellV
  have h1 := refine_perm (ctx := ctx) hbcp
    (by rw [Array.size_map, hUbsz, hVbsz]) hVbsz hVbOk hsz'
    hend' hstarts (numcells := V.numcells + 1)
  have h2 := refine_map σ hg (level + 1)
    (breakout n U.lab V.ptn (level + 1) tc U.lab[tc + oU]!).1
    (V.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (V.numcells + 1)
    hUbsz hUbOk hsz' hend'
  rw [h2] at h1
  show StPerm (level + 1)
    (refine ctx (level + 1)
      (breakout n V.lab V.ptn (level + 1) tc V.lab[tc + oV]!).1
      (V.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (V.numcells + 1))
    (mapSt σ (refine ctx (level + 1)
      (breakout n U.lab U.ptn (level + 1) tc U.lab[tc + oU]!).1
      (U.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (U.numcells + 1)))
  rw [hptn, hnum]
  exact h1

/-! # Descents through the subtree -/

/-- A descent: a sequence of individualize-and-refine steps, each at a
nontrivial cell of the current partition. -/
inductive Descends (ctx : Ctx n) :
    Nat → RefineSt n → Nat → RefineSt n → Prop where
  | refl (level : Nat) (st : RefineSt n) : Descends ctx level st level st
  | step {level level' : Nat} {st st' : RefineSt n} (tc e o : Nat)
      (hlvl : level < n)
      (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
      (ho : o ≤ e - tc)
      (htail : Descends ctx (level + 1)
        (childSt ctx level st tc st.lab[tc + o]!) level' st') :
      Descends ctx level st level' st'

/-- The node invariant holds along every descent. -/
theorem descends_iterOk {level level' : Nat} {st st' : RefineSt n}
    (h : Descends ctx level st level' st')
    (hok : IterOk ctx level st) : IterOk ctx level' st' := by
  induction h with
  | refl _ _ => exact hok
  | step tc e o hlvl hcell hne ho htail ih =>
    exact ih (iterOk_child hok hlvl hcell hne ho)

/-- The bisimulation: a descent below one state mirrors below any
state whose labelling is cell-equivalent up to a row-preserving
renaming, ending in the transported relation. -/
theorem descends_transport {σ : Renaming n}
    (hg : RowsMap σ ctx.g ctx.g) :
    ∀ {level level' : Nat} {U U' V : RefineSt n},
      Descends ctx level U level' U' → IterOk ctx level U →
      StPerm level V (mapSt σ U) →
      ∃ V', Descends ctx level V level' V' ∧
        StPerm level' V' (mapSt σ U')
  | _, _, _, _, V, .refl _ _, _, hsp => ⟨V, .refl _ _, hsp⟩
  | level, level', U, U', V,
      .step tc e o hlvl hcell hne ho htail, hU, hsp => by
    have hV := iterOk_of_stPerm hU hsp
    have hptn : U.ptn = V.ptn := hsp.ptn
    have hpszV := hV.ok.ptnSize
    have hendV := hV.ok.ptnEnd
    have hcellV : (tc, e) ∈ cells V.ptn level n := by
      rw [← hptn]
      exact hcell
    have hen : e < n := target_end_lt hpszV hendV hcellV
    have hcellIsV : IsCell V.ptn level tc (e + 1 - tc) :=
      cells_isCell (by omega) hendV _ hcellV
    have hmemU : σ.toFun U.lab[tc + o]! ∈
        segN (U.lab.map σ.toFun) tc (e + 1 - tc) := by
      rw [segN_map (by rw [hU.ok.labSize]; omega)]
      exact List.mem_map.mpr
        ⟨U.lab[tc + o]!, mem_segN_iff.mpr ⟨o, by omega, rfl⟩, rfl⟩
    have hcpT := hsp.cells tc (e + 1 - tc) hcellIsV
    have hmemV : σ.toFun U.lab[tc + o]! ∈
        segN V.lab tc (e + 1 - tc) := hcpT.mem_iff.mpr hmemU
    obtain ⟨oV, hoVlt, hoVval⟩ := mem_segN_iff.mp hmemV
    have hsp' := stPerm_child hg hsp hU hcell hne
      (by omega) ho hoVval
    have hUok' := iterOk_child hU hlvl hcell hne ho
    obtain ⟨V', hdesc, hspL⟩ :=
      descends_transport hg htail hUok' hsp'
    exact ⟨V', .step tc e oV hlvl hcellV hne (by omega) hdesc, hspL⟩

/-- The leaf collapse: a descent to a discrete state below one side
mirrors below the other with equal leaf rows — the renaming is
absorbed at the leaf. -/
theorem descends_leafRows {σ : Renaming n}
    (hg : RowsMap σ ctx.g ctx.g)
    {level level' : Nat} {U U' V : RefineSt n}
    (h : Descends ctx level U level' U')
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V', Descends ctx level V level' V' ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab := by
  obtain ⟨V', hdesc, hspL⟩ := descends_transport hg h hU hsp
  have hU' := descends_iterOk h hU
  have hV' := iterOk_of_stPerm hU' hspL
  have hptn : U'.ptn = V'.ptn := hspL.ptn
  have hVdisc : ∀ q, q < V'.ptn.size → V'.ptn[q]! ≤ level' := by
    intro q hq
    rw [← hptn]
    rw [hV'.ok.ptnSize] at hq
    exact hdisc q hq
  have hVsz : V'.lab.size = V'.ptn.size := by
    rw [hV'.ok.labSize, hV'.ok.ptnSize]
  have hlabeq := stPerm_lab_eq hspL hVdisc hVsz
  have hlabeq' : U'.lab.map σ.toFun = V'.lab := hlabeq
  have hlr : leafRows ctx V'.lab = leafRows ctx U'.lab := by
    rw [← hlabeq']
    exact leafRows_map σ hg hU'.ok.labOk hU'.ok.labSize
  exact ⟨V', hdesc, hlr⟩

/-! # The single-deviation theorem

Gluing the branch step at the deviation level: any descent to a leaf
below the first child of a pair target mirrors below the second child
with equal leaf rows. -/

/-- A deviation at a pair target: descents below the two children
reach leaves with the same rows. -/
theorem deviation_leafRows {S : Nat → Prop} {f : Nat → Nat}
    {st : RefineSt n} {level tc level' : Nat} {U' : RefineSt n}
    (hIt : IterOk ctx level st) (hgsz : ctx.g.size = n)
    (hlvl : level < n)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hrows : ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f)
    (hcell : (tc, tc + 1) ∈ cells st.ptn level n)
    (hStc : S tc)
    (hSpair : ∀ p ∈ cells st.ptn level n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells st.ptn level n, S p.1 →
      f st.lab[p.1]! = st.lab[p.1 + 1]! ∧
        f st.lab[p.1 + 1]! = st.lab[p.1]!)
    (hSfix : ∀ p ∈ cells st.ptn level n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f st.lab[p.1 + o]! = st.lab[p.1 + o]!)
    (hdesc : Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + 0]!) level' U')
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V', Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + 1]!) level' V' ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab := by
  have hg : RowsMap (renamingOfFlip f n hfb hinvol) ctx.g ctx.g :=
    rowsMap_of_flip_rows hgsz hfb hinvol hrows
  have hstep := branch_step (S := S) hgsz hIt.ok.ptnSize
    hIt.ok.labSize hIt.ok.ptnEnd hIt.valsWeak hIt.ok.labOk hIt.inj
    hfb hinvol hrows hcell hStc hSpair hSswap hSfix
    (numcells := st.numcells)
  have hU0 : IterOk ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + 0]!) :=
    iterOk_child hIt hlvl hcell (by omega) (by omega)
  have hstep' : StPerm (level + 1)
      (childSt ctx level st tc st.lab[tc + 1]!)
      (mapSt (renamingOfFlip f n hfb hinvol)
        (childSt ctx level st tc st.lab[tc + 0]!)) := hstep
  exact descends_leafRows hg hdesc hU0 hstep' hdisc

end Hex.GraphIso.Nauty
