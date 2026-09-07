/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Leaves
public import HexGraphIso.Nauty.SmallCell.Flip
import all HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
The exotic defect-four flip data.

`cheapautom`'s second branch passes on partitions whose defect
(vertices minus cells) is at most four without the all-pairs-and-one-
triple shape of the first branch. The possible nontrivial cell
multisets are `{4}`, `{5}`, `{4,2}` and `{3,3}`. This file proves the
flip data for those configurations: for any two members of any
nontrivial cell, a row-preserving self-symmetry of the node carrying
one to the other, in the shape the pair and triple deviations consume.

No shape enumeration is needed. Everything is forced by counting:

* the differ set of two cell members (the other members whose bits at
  the two differ) always has even size, one half adjacent to the
  first, so with at most three other members it is empty or a single
  crossed pair (`differ` classification);
* in a five-cell the internal degree is even (the handshake), so the
  members outside a crossed pair have equal bits at the pair;
* in a four-cell the equitability row equations force full invariance
  under every double transposition (the `vlemma`);
* between two triples and between a four-cell and a pair, the constant
  cross-counts pair the members up by their minority bit, and swapping
  matched partners preserves every cross bit.

The constructions share one generic involution `sw` (up to three
simultaneous swaps, degenerate swaps allowed) with one bit-invariance
lemma (`sw_bits`), one generic rows conclusion (`rows_of_label_bits`,
the factored tail of `flip_rows`), and one generic self-equivalence
(`cellsPerm_self_setwise`: a renaming permuting every cell's members
within the cell is a cell-contents self-equivalence).
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Bit invariance to rows

A value-level bit-invariant involution preserves the adjacency rows;
with the involution available no surjectivity is needed, since the
image bit at `z` reads off the bit at `f z`. -/


/-! # The flip-data assembly

A raw bit-invariant involution permuting every cell's members within
the cell packages into the renaming, rows map and state
self-equivalence the deviation doors consume. -/

theorem flip_data_of_bits {st : RefineSt n} {level : Nat}
    {f : Nat → Nat}
    (hIt : IterOk ctx level st) (hgsz : ctx.g.size = n)
    (hfb : ∀ w, w < n → f w < n)
    (hinvol : ∀ w, w < n → f (f w) = w)
    (hbits : ∀ z z', z < n → z' < n →
      (ctx.g[f z]!).mem (f z') = (ctx.g[z]!).mem z')
    (hset : ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      ∀ i, i < n → σ.toFun st.lab[i]! = f st.lab[i]! := by
  refine ⟨renamingOfFlip f n hfb hinvol, ?_, ?_, ?_⟩
  · exact rowsMap_of_flip_rows hgsz hfb hinvol
      (rows_of_bits hfb hinvol hbits)
  · exact stPerm_self_setwise hIt.ok hIt.inj hfb hinvol hset
  · intro i hi
    exact renamingOfFlip_at hfb hinvol
      (hIt.ok.labOk i (by rw [hIt.ok.labSize]; omega))

/-! # Position and counting toolkit for the configurations -/

private theorem mem_erase_nodup :
    ∀ {l : List Nat}, l.Nodup → ∀ a w,
      (w ∈ l.erase a ↔ w ∈ l ∧ w ≠ a)
  | [], _, a, w => by simp
  | b :: t, hnd, a, w => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      constructor
      · intro hw
        exact ⟨List.mem_cons_of_mem _ hw,
          fun hcon => hnd.1 (hcon ▸ hw)⟩
      · rintro ⟨hw, hne⟩
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd rfl hne
        · exact hmem
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba)]
      rw [List.mem_cons, List.mem_cons,
        mem_erase_nodup hnd.2 a w]
      constructor
      · rintro (rfl | ⟨hw, hne⟩)
        · exact ⟨Or.inl rfl, hba⟩
        · exact ⟨Or.inr hw, hne⟩
      · rintro ⟨rfl | hw, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hw, hne⟩

/-- The count of one row into a singleton cell is its bit there, so
equitability makes the bits of all members of a cell agree at every
singleton-cell vertex. -/
theorem cell_const_into_singleton {lab ptn : Array Nat}
    {level : Nat}
    (hE : Equitable ctx level lab ptn)
    {tc te : Nat} (hC : (tc, te) ∈ cells ptn level n)
    {s : Nat} (hS : (s, s) ∈ cells ptn level n)
    {o o' : Nat} (ho : o ≤ te - tc) (ho' : o' ≤ te - tc) :
    (ctx.g[lab[tc + o]!]!).mem lab[s]! =
      (ctx.g[lab[tc + o']!]!).mem lab[s]! := by
  have hle : tc ≤ te := cells_le _ hC
  have h := hE _ hC _ hS o o' (by omega) (by omega)
  rw [worksetOf_singleton, VSet.cardInter_singleton,
    VSet.cardInter_singleton] at h
  rcases hb : (ctx.g[lab[tc + o]!]!).mem lab[s]! with _ | _ <;>
    rcases hb' : (ctx.g[lab[tc + o']!]!).mem lab[s]! with _ | _ <;>
      rw [hb, hb'] at h <;> simp_all

/-! # The single-nontrivial-cell configurations

With every other cell a singleton, the flip at a target cell of size
at most five is a transposition of the two chosen members, together
with the crossed transposition of the differ pair when the counting
classification produces one. -/

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
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
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
        rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hC hpmem hwa hwb
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn]
        rw [hsymm _ _ hxn hz, hsymm _ _ hyn hz] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn] at hconst
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

private theorem nodup_erase :
    ∀ {l : List Nat}, l.Nodup → ∀ a, (l.erase a).Nodup
  | [], _, _ => by simp
  | b :: t, hnd, a => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      exact hnd.2
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba),
        List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_erase hnd.2 a⟩
      exact hnd.1 ((mem_erase_nodup hnd.2 a b).mp hmem).1

private theorem nodup_subset_length :
    ∀ (l r : List Nat), l.Nodup → (∀ x ∈ l, x ∈ r) →
      l.length ≤ r.length
  | [], r, _, _ => by simp
  | a :: t, r, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ r := hsub a List.mem_cons_self
    have hlen := (List.perm_cons_erase ha).length_eq
    have hsub' : ∀ x ∈ t, x ∈ r.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun hcon => hnd.1
        (by rw [← hcon]; exact hx))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have h := nodup_subset_length t (r.erase a) hnd.2 hsub'
    simp only [List.length_cons] at hlen ⊢
    omega

set_option maxHeartbeats 1000000 in
/-- In a five-member window, the member outside a crossed pair has
equal bits at the pair: the pair's two row sums expand over the five
named offsets, the crossed types cancel, and the shared internal bit
cancels by symmetry. -/
private theorem oneCell_wfix {wa wb wf : Nat}
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hm : te + 1 - tc = 5)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hwf : wf ≤ te - tc)
    (hab : wa ≠ wb) (haf : wa ≠ wf) (hbf : wb ≠ wf)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (hfu : wf ≠ oU) (hfv : wf ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! =
      true) :
    (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wb]! := by
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
  have hnd : ([oU, oV, wa, wb, wf] : List Nat).Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro (h | h | h | h | h) <;> omega
    · rintro (h | h | h | h) <;> omega
    · rintro (h | h | h) <;> omega
    · rintro (h | h) <;> omega
    · simp
  have hbd : ∀ x ∈ ([oU, oV, wa, wb, wf] : List Nat),
      x < te + 1 - tc := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hxf : x = wf := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hcic : ∀ o : Nat, o ≤ te - tc →
      (worksetOf n st.lab tc te).cardInter
          ctx.g[st.lab[tc + o]!]! =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hC
  have hrow := hE _ hC _ hC wa wb (by omega) (by omega)
  rw [hcic wa hwa, hcic wb hwb, hm] at hrow
  rw [sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd),
    sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd)] at hrow
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hrow
  have hloopa : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wa]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hloopb : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wb]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsymab : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wb]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wa]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have h1 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oU]! = 1 :=
    bitCnt_eq_one.mpr htau
  have h2 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr htav
  have h3 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr htbu
  have h4 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oV]! = 1 :=
    bitCnt_eq_one.mpr htbv
  have hkey : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wf]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wf]! := by
    omega
  have hbit := bitCnt_inj.mp hkey
  rw [hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wa) (by omega)),
    hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wb) (by omega))]
  exact hbit

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
      exact oneCell_wfix hIt hsymm hloop hE hC (by omega) hoU hoV hne
        (by omega) (by omega) hw hab (Ne.symm hwa) (Ne.symm hwb)
        hau hav hbu hbv hwu hwv htau htav htbu htbv

end OneCell

end Hex.GraphIso.Nauty
