/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Guard
public import HexGraphIso.Nauty.SmallCell.Flip
import all HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
Cell-stabilizing automorphisms for equitable partitions admitted by
cheapautom. Pair cells use matching closure. The remaining shapes use
balanced distinguishing sets and regularity inside cells of size at most
five. Every construction uses the same transposition and cell-map criteria.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

section OneCell

variable {st : RefineSt n} {level tc te oU oV : Nat}

/-- The transposition route: every other window member has equal bits
at the two swapped ones. -/
private theorem oneCell_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hAllEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have huv : st.lab[tc + oU]! ≠ st.lab[tc + oV]! := by
    intro hcon
    have := hinj (tc + oU) (tc + oV) (by omega) (by omega) hcon
    omega
  -- every other reachable vertex has equal bits at the pair
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · -- j sits in the target window
      have hw : j - tc ≤ te - tc := by
        have h2 : j ≤ te := hj2
        omega
      have hwu : j - tc ≠ oU := by
        intro hcon
        refine hzu ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oU := by omega
        rw [this]
      have hwv : j - tc ≠ oV := by
        intro hcon
        refine hzv ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oV := by omega
        rw [this]
      have h := hAllEq (j - tc) hw hwu hwv
      have h1 : tc ≤ j := hj1
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    · -- j sits in a singleton cell
      have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      exact hconst
  -- the swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hC hoU hoV hne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The crossed-pair route: the two chosen members swap together with
the differ pair, every other window member having equal bits at both
pairs. -/
private theorem oneCell_sw2 {wa wb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hab : wa ≠ wb)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! =
      true)
    (hRestEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!)
    (hWfix : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + wa]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + wb]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hvne : ∀ w w' : Nat, w ≤ te - tc → w' ≤ te - tc → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hvne _ _ hoU hoV hne,
      hvne _ _ hoU hwa (fun h => hau h.symm),
      hvne _ _ hoU hwb (fun h => hbu h.symm),
      hvne _ _ hoV hwa (fun h => hav h.symm),
      hvne _ _ hoV hwb (fun h => hbv h.symm),
      hvne _ _ hwa hwb hab⟩
  obtain ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩ := hOk
  have hOk2 : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + wa]! →
      z ≠ st.lab[tc + wb]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + wa]! =
        (ctx.g[z]!).mem st.lab[tc + wb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ te := hj2
      have hw : j - tc ≤ te - tc := by omega
      have hwneq : ∀ w' : Nat, w' ≤ te - tc →
          st.lab[j]! ≠ st.lab[tc + w']! → j - tc ≠ w' := by
        intro w' hw' hne' hcon
        exact hne' (by rw [show j = tc + w' by omega])
      have hwu := hwneq oU hoU hzu
      have hwv := hwneq oV hoV hzv
      have hwx := hwneq wa hwa hzx
      have hwy := hwneq wb hwb hzy
      have hr := hRestEq (j - tc) hw hwu hwv hwx hwy
      have hf := hWfix (j - tc) hw hwu hwv hwx hwy
      rw [show tc + (j - tc) = j by omega] at hr hf
      exact ⟨hr, hf⟩
    · have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
        exact hconst
      · have hconst := cell_const_into_singleton hE hC hpmem hwa hwb
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn]
        exact hconst
  -- the cross bits between the two pairs match diagonally
  have hc1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + wb]! := by
    rw [hsymm _ _ hun hxn, hsymm _ _ hvn hyn, htau, htbv]
  have hc2 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + wb]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + wa]! := by
    rw [hsymm _ _ hun hyn, hsymm _ _ hvn hxn, htbu, htav]
  -- the double swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
          st.lab[tc + wb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk2 (sw1_cells hIt.ok hIt.inj hC hoU hoV hne)
      (sw1_cells hIt.ok hIt.inj hC hwa hwb hab)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
      st.lab[tc + wb]!) hIt hgsz
    (sw2_lt hOk2) (fun w _ => sw2_invol hOk2 w)
    (sw2_bits hsymm hloop hOk2 hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

set_option maxHeartbeats 2000000 in
/-- The flip data at a nontrivial cell of size at most five whose
companions are all singletons: the differ classification of the two
chosen members is forced by the window row sums, and the flip is the
bare transposition or the crossed double swap. -/
theorem oneCell_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hm : te + 1 - tc ≤ 5)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the window row sums
  have hcic : ∀ o : Nat, o ≤ te - tc →
      (worksetOf n st.lab tc te).cardInter
          ctx.g[st.lab[tc + o]!]! =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hC
  have hrow := hE _ hC _ hC oU oV (by omega) (by omega)
  rw [hcic oU hoU, hcic oV hoV] at hrow
  -- the remaining window offsets
  have hnd1 := nodup_erase (List.nodup_range (n := te + 1 - tc)) oU
  have hndL := nodup_erase hnd1 oV
  have hoUm : oU ∈ List.range (te + 1 - tc) :=
    List.mem_range.mpr (by omega)
  have hoVm : oV ∈ (List.range (te + 1 - tc)).erase oU :=
    (mem_erase_nodup (List.nodup_range) oU oV).mpr
      ⟨List.mem_range.mpr (by omega), fun h => hne h.symm⟩
  have hmemL : ∀ w,
      w ∈ ((List.range (te + 1 - tc)).erase oU).erase oV ↔
        (w < te + 1 - tc ∧ w ≠ oU ∧ w ≠ oV) := by
    intro w
    rw [mem_erase_nodup hnd1 oV w,
      mem_erase_nodup (List.nodup_range) oU w, List.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hlenL :
      (((List.range (te + 1 - tc)).erase oU).erase oV).length + 2 =
        te + 1 - tc := by
    have l1 := (List.perm_cons_erase hoUm).length_eq
    have l2 := (List.perm_cons_erase hoVm).length_eq
    rw [List.length_range] at l1
    simp only [List.length_cons] at l1 l2
    omega
  -- split the two row sums at the chosen offsets
  have hsplit : ∀ F : Nat → Nat,
      ((List.range (te + 1 - tc)).map F).sum =
        F oU + F oV +
          (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
            F).sum := by
    intro F
    have e1 := sum_of_perm ((List.perm_cons_erase hoUm).map F)
    have e2 := sum_of_perm ((List.perm_cons_erase hoVm).map F)
    simp only [List.map_cons, List.sum_cons] at e1 e2
    omega
  rw [hsplit, hsplit] at hrow
  have hlu : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hlv : bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsuv : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oV]! =
      bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + oU]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hrest :
      (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
          fun w => bitCnt ctx.g[st.lab[tc + oU]!]!
            st.lab[tc + w]!).sum =
      (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
          fun w => bitCnt ctx.g[st.lab[tc + oV]!]!
            st.lab[tc + w]!).sum := by
    omega
  have hcount :
      (((List.range (te + 1 - tc)).erase oU).erase oV).countP
          (fun w => (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w]!) =
        (((List.range (te + 1 - tc)).erase oU).erase oV).countP
          (fun w => (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w]!) := by
    have he :
        (((((List.range (te + 1 - tc)).erase oU).erase oV).map
          (fun w => st.lab[tc + w]!))).countP (ctx.g[st.lab[tc + oU]!]!).mem =
        (((((List.range (te + 1 - tc)).erase oU).erase oV).map
          (fun w => st.lab[tc + w]!))).countP (ctx.g[st.lab[tc + oV]!]!).mem := by
      rw [countP_bits, countP_bits]
      simpa only [List.map_map, Function.comp_def] using hrest
    simpa only [List.countP_map, Function.comp_def] using he
  rcases differ_pair _ _ (by omega) hcount with heq |
      ⟨wa, hwa, wb, hwb, hab, hAu, hAv, hBu, hBv, hfix⟩
  · refine oneCell_sw1 hIt hgsz hsymm hloop hE hC hsing hoU hoV hne ?_
    intro w hw hwu hwv
    rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oU) (by omega)),
      hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oV) (by omega))]
    exact heq w ((hmemL w).mpr ⟨by omega, hwu, hwv⟩)
  · obtain ⟨ha, hau, hav⟩ := (hmemL wa).mp hwa
    obtain ⟨hb, hbu, hbv⟩ := (hmemL wb).mp hwb
    have htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! = true := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hAu
    have htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! = false := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hAv
    have htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! = false := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hBu
    have htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! = true := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hBv
    refine oneCell_sw2 hIt hgsz hsymm hloop hE hC hsing hoU hoV hne
      (by omega) (by omega) hab hau hav hbu hbv htau htav htbu htbv ?_ ?_
    · intro w hw hwu hwv hwa hwb
      rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oU) (by omega)),
        hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oV) (by omega))]
      exact hfix w ((hmemL w).mpr ⟨by omega, hwu, hwv⟩) hwa hwb
    · intro w hw hwu hwv hwa hwb
      have hnd : ([oU, oV, wa, wb, w] : List Nat).Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
        grind
      have hsub : ∀ x ∈ ([oU, oV, wa, wb, w] : List Nat),
          x ∈ List.range (te + 1 - tc) := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil] at hx
        apply List.mem_range.mpr
        grind
      have hlen := nodup_subset_length _ _ hnd hsub
      simp only [List.length_cons, List.length_nil, List.length_range] at hlen
      exact differ_five hIt hsymm hloop hE hC (by omega) hoU hoV hne
        (by omega) (by omega) hw hab (Ne.symm hwa) (Ne.symm hwb)
        hau hav hbu hbv hwu hwv htau htav htbu htbv

end OneCell

section TwoTriple

variable {st : RefineSt n} {level tc d2 oU oV : Nat}

set_option maxHeartbeats 4000000 in
/-- The cross-cell double swap: the two chosen members of the target
triple swap together with their partners in the other triple. -/
theorem twoTriple_sw2 {pa pb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (hpa : pa ≤ 2) (hpb : pb ≤ 2) (hpab : pa ≠ pb)
    (hfixT1 : ∀ w, w ≤ 2 → w ≠ oU → w ≠ oV →
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pb]!))
    (hfixT2 : ∀ w, w ≤ 2 → w ≠ pa → w ≠ pb →
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pb]!))
    (hc1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pa]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pb]!)
    (hc2 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pb]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pa]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the two windows are disjoint
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hin2 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[d2 + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (d2 + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[d2 + pa]! st.lab[d2 + pb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hin1 _ _ hoU hoV hne,
      hcross _ _ hoU hpa, hcross _ _ hoU hpb,
      hcross _ _ hoV hpa, hcross _ _ hoV hpb,
      hin2 _ _ hpa hpb hpab⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[d2 + pa]! →
      z ≠ st.lab[d2 + pb]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[d2 + pa]! =
        (ctx.g[z]!).mem st.lab[d2 + pb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := hfixT1 (j - tc) hw hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have hwa : j - d2 ≠ pa := fun hcon =>
        hzx (by rw [show j = d2 + pa by omega])
      have hwb : j - d2 ≠ pb := fun hcon =>
        hzy (by rw [show j = d2 + pb by omega])
      have h := hfixT2 (j - d2) hw hwa hwb
      rw [show d2 + (j - d2) = j by omega] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hT1 hpmem
          (o := oU) (o' := oV) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (tc + oU) (by omega)) hz,
          hsymm _ _ (hlb (tc + oV) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hT2 hpmem
          (o := pa) (o' := pb) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (d2 + pa) (by omega)) hz,
          hsymm _ _ (hlb (d2 + pb) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
  -- the swap permutes both triples within themselves
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
          st.lab[d2 + pb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk (sw1_cells hIt.ok hIt.inj hT1 (by omega) (by omega) hne)
      (sw1_cells hIt.ok hIt.inj hT2 (by omega) (by omega) hpab)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
      st.lab[d2 + pb]!) hIt hgsz
    (sw2_lt hOk) (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

set_option maxHeartbeats 4000000 in
/-- The uniform cross-count route: the other triple's bits do not
distinguish the two chosen members, so the bare transposition
suffices. -/
theorem twoTriple_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (huni : ∀ q, q ≤ 2 →
      (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + q]! =
        (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + q]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have huv := hin1 _ _ hoU hoV hne
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := triple_internal hE hpsz hend hinj hlb hsymm hloop
        hT1 (j - tc) oU (j - tc) oV (by omega) (by omega) (by omega)
        (by omega) hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have h := huni (j - d2) hw
      rw [show d2 + (j - d2) = j by omega] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hT1 hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      exact hconst
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hT1 (by omega) (by omega) hne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The flip data at a triple target beside a second triple, all other
cells singletons: the constant cross-count is uniform (`0` or `3`,
reducing to the bare transposition) or matched (`1` or `2`, pairing
each chosen member with its unique minority partner and swapping the
partners along). -/
theorem twoTriple_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have ht1n : tc + 2 < n := by
    have := cells_bound (by omega) hend _ hT1
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by omega) hend _ hT2
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hIt.ok.labSize]; exact hi)
  have hcount := hE _ hT1 _ hT2 oU oV (by omega) (by omega)
  rw [← countP_cell hpsz hend hinj hT2, ← countP_cell hpsz hend hinj hT2,
    show d2 + 2 + 1 - d2 = 3 by omega] at hcount
  simp only at hcount
  rcases differ_pair _ _ (by simp) hcount with heq |
      ⟨pa, hpa, pb, hpb, hpab, hAu, hAv, hBu, hBv, hfix⟩
  · exact twoTriple_sw1 hIt hgsz hsymm hloop hE hT1 hT2 hT12 hsing hoU hoV hne
      (fun q hq => heq q (List.mem_range.mpr (by omega)))
  · have ha : pa ≤ 2 := by have := List.mem_range.mp hpa; omega
    have hb : pb ≤ 2 := by have := List.mem_range.mp hpb; omega
    refine twoTriple_sw2 hIt hgsz hsymm hloop hE hT1 hT2 hT12 hsing
      hoU hoV hne ha hb hpab ?_ ?_ ?_ ?_
    · intro w hw hwu hwv
      refine ⟨triple_internal hE hpsz hend hinj hlb hsymm hloop hT1
        w oU w oV (by omega) (by omega) (by omega) (by omega) hwu hwv, ?_⟩
      have hrow := hE _ hT2 _ hT1 pa pb (by omega) (by omega)
      rw [count_into_cell hpsz hend hinj hT1,
        count_into_cell hpsz hend hinj hT1,
        show tc + 2 + 1 - tc = 3 by omega, sum_range_three, sum_range_three] at hrow
      rw [sum3_eq_of_cover (f := fun j => bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + j]!)
          hoU hoV hw hne (Ne.symm hwu) (Ne.symm hwv),
        sum3_eq_of_cover (f := fun j => bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + j]!)
          hoU hoV hw hne (Ne.symm hwu) (Ne.symm hwv)] at hrow
      have h1 : bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + oU]! = 1 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_one.mpr hAu
      have h2 : bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + oV]! = 0 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_zero.mpr hAv
      have h3 : bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + oU]! = 0 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_zero.mpr hBu
      have h4 : bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + oV]! = 1 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_one.mpr hBv
      rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (d2 + pa) (by omega)),
        hsymm _ _ (hlb (tc + w) (by omega)) (hlb (d2 + pb) (by omega))]
      apply bitCnt_inj.mp
      omega
    · intro w hw hwa hwb
      constructor
      · rw [hsymm _ _ (hlb (d2 + w) (by omega)) (hlb (tc + oU) (by omega)),
          hsymm _ _ (hlb (d2 + w) (by omega)) (hlb (tc + oV) (by omega))]
        exact hfix w (List.mem_range.mpr (by omega)) hwa hwb
      · exact triple_internal hE hpsz hend hinj hlb hsymm hloop hT2
          w pa w pb (by omega) (by omega) (by omega) (by omega) hwa hwb
    · rw [hAu, hBv]
    · rw [hBu, hAv]

end TwoTriple

section FourCell

variable {st : RefineSt n} {level tc d2 oU oV w1 w2 : Nat}

/-- The double-swap route at a four-cell beside a pair. -/
theorem fourPair_sw2
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hPfix : ∀ q, q ≤ 1 →
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oV]! ∧
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w1]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w2]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  -- distinct labels inside the cell and across the two cells
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! :=
    ⟨hun, hvn, hxn, hyn, hin1 _ _ hoU hoV hUV,
      hin1 _ _ hoU hw1 hUw1, hin1 _ _ hoU hw2 hUw2,
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hin1 _ _ hw1 hw2 h12⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- everything outside the four moved members treats them in pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · -- a member of the four-cell is one of the four moved labels
      have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      rw [hjd]
      exact hPfix (j - d2) hq
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hd := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      rw [← hjp] at hc hd
      have hjn : st.lab[j]! < n := hlb j hj
      constructor
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
        exact hc
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]
        exact hd
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) hUV)
      (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) h12)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]!) hIt hgsz (sw2_lt hOk)
    (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

/-- The triple-swap route at a four-cell beside a pair: the chosen
members cross the pair coherently, as they do on opposite sides of a
matched split. -/
theorem fourPair_sw3
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hUV0 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 1]!)
    (hUV1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 0]!)
    (hW0 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 1]!)
    (hW1 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 0]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! ∧
      st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
      st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hpne : st.lab[d2 + 0]! ≠ st.lab[d2 + 1]! := by
    intro hcon
    have := hinj (d2 + 0) (d2 + 1) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have han : st.lab[d2 + 0]! < n := hlb _ (by omega)
  have hbn : st.lab[d2 + 1]! < n := hlb _ (by omega)
  have hOk : Sw3Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! st.lab[d2 + 0]!
      st.lab[d2 + 1]! :=
    ⟨hun, hvn, hxn, hyn, han, hbn,
      hin1 _ _ hoU hoV hUV, hin1 _ _ hoU hw1 hUw1,
      hin1 _ _ hoU hw2 hUw2, hcross oU 0 hoU (by omega),
      hcross oU 1 hoU (by omega),
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hcross oV 0 hoV (by omega), hcross oV 1 hoV (by omega),
      hin1 _ _ hw1 hw2 h12, hcross w1 0 hw1 (by omega),
      hcross w1 1 hw1 (by omega), hcross w2 0 hw2 (by omega),
      hcross w2 1 hw2 (by omega), hpne⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- only the singletons remain outside the six moved members
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! → z ≠ st.lab[d2 + 0]! →
      z ≠ st.lab[d2 + 1]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! ∧
      (ctx.g[z]!).mem st.lab[d2 + 0]! =
        (ctx.g[z]!).mem st.lab[d2 + 1]! := by
    intro z hz hzu hzv hzx hzy hza hzb
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = 0 ∨ j - d2 = 1 := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hza hzb
      · exact absurd rfl hza
      · exact absurd rfl hzb
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hcU := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hcW := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      have hcP := cell_const_into_singleton hE hP hpmem
        (o := 0) (o' := 1) (by omega) (by omega)
      rw [← hjp] at hcU hcW hcP
      have hjn : st.lab[j]! < n := hlb j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]; exact hcU
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]; exact hcW
      · rw [hsymm _ _ hjn han, hsymm _ _ hjn hbn]; exact hcP
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!
            st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw3_cells hOk (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) hUV)
      (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) h12)
      (sw1_cells hIt.ok hIt.inj hP (a := 0) (b := 1) (by omega) (by omega) (by omega))
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!)
    hIt hgsz (sw3_lt hOk) (fun w _ => sw3_invol hOk w)
    (sw3_bits hsymm hloop hOk hfix hc1 hc2 hUV0 hUV1 hW0 hW1) hset
  refine ⟨σ, hrm, hsp, ?_, ?_, ?_⟩
  · rw [hat (tc + oU) (by omega), sw3_u]
  · rw [hat (d2 + 0) (by omega), sw3_a hOk]
  · rw [hat (d2 + 1) (by omega), sw3_b hOk]

set_option maxHeartbeats 1000000 in
/-- The flip data at a four-cell target beside a pair, all other cells
singletons. -/
theorem fourPair_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  obtain ⟨w1, w2, hw1, hw2, hUw1, hUw2, hVw1, hVw2, h12⟩ :=
    other_two hoU hoV hne
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hne, hUw1, hUw2, hVw1, hVw2, h12]
  have hbd : ∀ x ∈ ([oU, oV, w1, w2] : List Nat), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have : x = w2 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  -- the forward counts into the pair
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two] at h
    exact h
  -- the reverse counts into the four-cell
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w2]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- forward constancy across the four-cell, reverse across the pair
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  -- the two directions agree termwise
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the pair's view of the four members, in the two useful shapes
  have hbit : ∀ o q, o ≤ 3 → q ≤ 1 →
      ((ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + q]! = true ↔
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! = 1) :=
    fun o q ho hq => ⟨fun h => bitCnt_eq_one.mpr h,
      fun h => bitCnt_eq_one.mp h⟩
  have hPof : ∀ o o', o ≤ 3 → o' ≤ 3 →
      (∀ q, q ≤ 1 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! =
          bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + q]!) →
      ∀ q, q ≤ 1 →
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o]! =
          (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o']! := by
    intro o o' ho ho' h q hq
    have h1 := hsy o q ho hq
    have h2 := hsy o' q ho' hq
    exact bitCnt_inj.mp (by rw [h1, h2]; exact h q hq)
  -- the constant cross-count is zero, one or two
  have hsum : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 2 := by
    have := hle oU 0
    have := hle oU 1
    omega
  have hUVc := hfc oU oV hoU hoV
  have hUw1c := hfc oU w1 hoU hw1
  have hUw2c := hfc oU w2 hoU hw2
  rcases hsum with h0 | h1 | h2
  · -- no edges between the two cells
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
  · -- each member meets exactly one of the pair
    have hr0 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w2]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy oU 0 hoU (by omega)
      have s2 := hsy oV 0 hoV (by omega)
      have s3 := hsy w1 0 hw1 (by omega)
      have s4 := hsy w2 0 hw2 (by omega)
      have s5 := hsy oU 1 hoU (by omega)
      have s6 := hsy oV 1 hoV (by omega)
      have s7 := hsy w1 1 hw1 (by omega)
      have s8 := hsy w2 1 hw2 (by omega)
      omega
    rcases Decidable.em
        (bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! =
          bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]!)
      with hsame | hdiff
    · -- the chosen members sit on the same side of the split
      refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
        hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
      intro q hq
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      constructor
      · exact hPof oU oV hoU hoV (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
      · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
    · -- opposite sides: name the partner of each chosen member
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      have hVc := hfc oV w1 hoV hw1
      rcases Decidable.em
          (bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! =
            bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]!)
        with hw1U | hw1V
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw2 hw1 hne hUw2 hUw1 hVw2 hVw1
            (Ne.symm h12)
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
  · -- every member meets both of the pair
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq

/-- The transposition route at a pair target beside a four-cell. -/
theorem pairFour_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV)
    (huni : ∀ o, o ≤ 3 →
      (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qU]! =
        (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qV]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hin2 : ∀ q q' : Nat, q ≤ 1 → q' ≤ 1 → q ≠ q' →
      st.lab[d2 + q]! ≠ st.lab[d2 + q']! := by
    intro q q' hq hq' hne' hcon
    have := hinj (d2 + q) (d2 + q') (by omega) (by omega) hcon
    omega
  have hun : st.lab[d2 + qU]! < n := hlb _ (by omega)
  have hvn : st.lab[d2 + qV]! < n := hlb _ (by omega)
  have huv := hin2 _ _ hqU hqV hqne
  have hfix : ∀ z, z < n → z ≠ st.lab[d2 + qU]! →
      z ≠ st.lab[d2 + qV]! →
      (ctx.g[z]!).mem st.lab[d2 + qU]! =
        (ctx.g[z]!).mem st.lab[d2 + qV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    have hjn : st.lab[j]! < n := hlb j hj
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rw [hjt]
      exact huni (j - tc) hw
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = qU ∨ j - d2 = qV := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hzu hzv
      · exact absurd rfl hzu
      · exact absurd rfl hzv
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hP hpmem
        (o := qU) (o' := qV) (by omega) (by omega)
      rw [← hjp] at hc
      rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
      exact hc
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[d2 + qU]! st.lab[d2 + qV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hP (by omega) (by omega) hqne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[d2 + qU]! st.lab[d2 + qV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (d2 + qU) (by omega), sw1_u]

set_option maxHeartbeats 1000000 in
/-- The flip data at a pair target beside a four-cell, all other cells
singletons. -/
theorem pairFour_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two] at h
    exact h
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 0]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 2]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 3]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (l := [0, 1, 2, 3]) (by simp)
      (by simp) (by intro x hx; simp at hx; omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the matched route, given the split named explicitly
  have route : ∀ a b c d : Nat, a ≤ 3 → b ≤ 3 → c ≤ 3 → d ≤ 3 →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      bitCnt ctx.g[st.lab[tc + a]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + b]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + c]!]! st.lab[d2 + 0]! = 0 →
      bitCnt ctx.g[st.lab[tc + d]!]! st.lab[d2 + 0]! = 0 →
      (∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1) →
      ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd hAa hAb hAc
      hAd hone
    have o1 := hone a ha
    have o2 := hone b hb
    have o3 := hone c hc
    have o4 := hone d hd
    obtain ⟨σ, hrm, hsp, -, hp1, hp2⟩ :=
      fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP hsing
        ha hc hb hd hac hab had (Ne.symm hbc) hcd hbd
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
    exact ⟨σ, hrm, hsp, hp1, hp2⟩
  have hsum : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 2 := by
    have := hle 0 0
    have := hle 0 1
    omega
  have c1 := hfc 0 1 (by omega) (by omega)
  have c2 := hfc 0 2 (by omega) (by omega)
  have c3 := hfc 0 3 (by omega) (by omega)
  have e1 := hle 0 0
  have e2 := hle 0 1
  have e3 := hle 1 0
  have e4 := hle 1 1
  have e5 := hle 2 0
  have e6 := hle 2 1
  have e7 := hle 3 0
  have e8 := hle 3 1
  rcases hsum with h0 | h1 | h2
  · -- the pair meets no member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)
  · -- each member meets exactly one, so the four-cell splits in two
    have hone : ∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1 := by
      intro o ho
      have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      rcases ho4 with rfl | rfl | rfl | rfl <;> omega
    have hr0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy 0 0 (by omega) (by omega)
      have s2 := hsy 1 0 (by omega) (by omega)
      have s3 := hsy 2 0 (by omega) (by omega)
      have s4 := hsy 3 0 (by omega) (by omega)
      have s5 := hsy 0 1 (by omega) (by omega)
      have s6 := hsy 1 1 (by omega) (by omega)
      have s7 := hsy 2 1 (by omega) (by omega)
      have s8 := hsy 3 1 (by omega) (by omega)
      omega
    have hpick : ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
      have v0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v1 : bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v2 : bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v3 : bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 1 := by
        omega
      rcases v0 with q0 | q0 <;> rcases v1 with q1 | q1 <;>
        rcases v2 with q2 | q2 <;> rcases v3 with q3 | q3 <;>
        first
          | (exfalso; omega)
          | exact route 0 1 2 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 2 1 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 3 1 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 2 0 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 3 0 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 2 3 0 1 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
    obtain ⟨σ, hrm, hsp, hp1, hp2⟩ := hpick
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨σ, hrm, hsp, hp1⟩
    · exact ⟨σ, hrm, hsp, hp2⟩
  · -- the pair meets every member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)

end FourCell

section Dispatch

variable {st : RefineSt n} {level tc te oU oV : Nat}

set_option maxHeartbeats 1000000 in
/-- Flip data at every cell of a partition whose defect is at most
four. This is the shape the cheapautom guard's second branch admits;
it dispatches to the pair and triple routes of the first branch
together with the four exotic routes. -/
theorem defect4_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hdef : n - (cells st.ptn level n).length ≤ 4)
    (hT : (tc, te) ∈ cells st.ptn level n)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hnn : n ≤ st.ptn.size := by rw [hpsz]; exact Nat.le_refl _
  have hexc := exc_sum_eq_defect (nn := n) (level := level)
    (ptn := st.ptn) hpsz hend
  have hle : tc ≤ te := cells_le _ hT
  have hsize5 : ∀ q ∈ cells st.ptn level n, q.2 - q.1 ≤ 4 := by
    intro q hq
    have := exc_ge_one (q := q) _ hq
    omega
  have hpair2 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n, q ≠ q' →
        (q.2 - q.1) + (q'.2 - q'.1) ≤ 4 := by
    intro q hq q' hq' hqq
    have := exc_ge_two (q := q) (q' := q') _ hq hq' hqq
    omega
  have htri3 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n,
      ∀ q'' ∈ cells st.ptn level n, q ≠ q' → q ≠ q'' → q' ≠ q'' →
        (q.2 - q.1) + (q'.2 - q'.1) + (q''.2 - q''.1) ≤ 4 := by
    intro q hq q' hq' q'' hq'' h1 h2 h3
    have := exc_ge_three (q := q) (q' := q') (q'' := q'') _ hq hq'
      hq'' h1 h2 h3
    omega
  have hT5 := hsize5 _ hT
  have hs : te - tc = 1 ∨ te - tc = 2 ∨ te - tc = 3 ∨ te - tc = 4 := by
    omega
  rcases hs with hs | hs | hs | hs
  · -- a pair target
    have hte : te = tc + 1 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 1)) - (Prod.fst (tc, tc + 1)) = 1 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        3 ≤ q.2 - q.1) with ⟨C, hC, hCbig⟩ | hnobig
    · -- a four-cell beside it: the exotic route
      have hCle : C.1 ≤ C.2 := cells_le _ hC
      have hCne : C ≠ (tc, tc + 1) := by
        intro hcon
        rw [hcon] at hCbig
        omega
      have hCex : C.2 - C.1 = 3 := by
        have := hpair2 _ hC _ hT hCne
        omega
      have hCform : C = (C.1, C.1 + 3) := by
        obtain ⟨ca, cb⟩ := C
        simp only at hCex ⊢
        have hcb : cb = ca + 3 := by omega
        rw [hcb]
      have hC' : (C.1, C.1 + 3) ∈ cells st.ptn level n :=
        hCform ▸ hC
      have hCP : C.1 ≠ tc := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hC' hT (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine pairFour_flip_data hIt hgsz hsymm hloop hE hC' hT
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqC hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hCq : C ≠ q := fun hcon => hqC (by rw [← hcon, ← hCform])
        have h3 := htri3 _ hC _ hT _ hq hCne hCq
          (fun hcon => hqP hcon.symm)
        omega
    · -- no large cell: the first branch's pair route applies
      refine pair_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqp
      have hql := cells_le _ hq
      have hq2 : q.2 - q.1 ≤ 2 := by
        rcases Nat.lt_or_ge (q.2 - q.1) 3 with h | h
        · omega
        · exact absurd ⟨q, hq, h⟩ hnobig
      omega
  · -- a triple target
    have hte : te = tc + 2 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 2)) - (Prod.fst (tc, tc + 2)) = 2 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 2) ∧ q.2 - q.1 = 2) with ⟨D, hD, hDne, hDex⟩ |
      hnotri
    · -- two triples: the exotic route
      have hDform : D = (D.1, D.1 + 2) := by
        obtain ⟨da, db⟩ := D
        simp only at hDex ⊢
        have hdb : db = da + 2 := by omega
        rw [hdb]
      have hD' : (D.1, D.1 + 2) ∈ cells st.ptn level n :=
        hDform ▸ hD
      have hTD : tc ≠ D.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hD' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        exact hDne (by rw [hDform, ← heq])
      refine twoTriple_flip_data hIt hgsz hsymm hloop hE hT hD'
        hTD ?_ (by omega) (by omega) hne
      intro q hq hqT hqD
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hDq : D ≠ q := fun hcon => hqD (by rw [← hcon, ← hDform])
        have h3 := htri3 _ hT _ hD _ hq (Ne.symm hDne) 
          (fun hcon => hqT hcon.symm) hDq
        omega
    · -- a unique triple with everything else small
      refine triple_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqT
      have hql := cells_le _ hq
      rcases Decidable.em (q.2 - q.1 = 2) with h2 | h2
      · exact absurd ⟨q, hq, hqT, h2⟩ hnotri
      · have := hpair2 _ hq _ hT hqT
        omega
  · -- a four-cell target
    have hte : te = tc + 3 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 3)) - (Prod.fst (tc, tc + 3)) = 3 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 3) ∧ q.1 < q.2) with ⟨P, hP, hPne, hPnt⟩ |
      hnopair
    · -- a pair beside it: the exotic route
      have hPle := cells_le _ hP
      have hPex : P.2 - P.1 = 1 := by
        have := hpair2 _ hT _ hP (fun hcon => hPne hcon.symm)
        omega
      have hPform : P = (P.1, P.1 + 1) := by
        obtain ⟨pa, pb⟩ := P
        simp only at hPex ⊢
        have hpb : pb = pa + 1 := by omega
        rw [hpb]
      have hP' : (P.1, P.1 + 1) ∈ cells st.ptn level n :=
        hPform ▸ hP
      have hCP : tc ≠ P.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hP' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine fourPair_flip_data hIt hgsz hsymm hloop hE hT hP'
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqT hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hPq : P ≠ q := fun hcon => hqP (by rw [← hcon, ← hPform])
        have h3 := htri3 _ hT _ hP _ hq (Ne.symm hPne)
          (fun hcon => hqT hcon.symm) hPq
        omega
    · -- a lone four-cell
      refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
        (by omega) ?_ (by omega) (by omega) hne
      intro q hq hqT
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exact absurd ⟨q, hq, hqT, hlt⟩ hnopair
  · -- a five-cell target: nothing else can be nontrivial
    have hte : te = tc + 4 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 4)) - (Prod.fst (tc, tc + 4)) = 4 :=
      by omega
    refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
      (by omega) ?_ (by omega) (by omega) hne
    intro q hq hqT
    rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
    · exact heq.symm
    · exfalso
      have := hpair2 _ hT _ hq (fun h => hqT h.symm)
      omega

end Dispatch

end Hex.GraphIso.Nauty
