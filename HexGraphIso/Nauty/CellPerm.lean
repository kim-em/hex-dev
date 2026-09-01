/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Refine
public import HexGraphIso.Nauty.Image
public import HexGraphIso.Nauty.Equivariance

public section

/-!
Refinement as a function of cell contents.

nauty's canonical form is well defined on a coloured graph because the
refinement machinery depends on an ordered partition only through the
multiset of vertices in each cell: two labellings whose cells hold the
same vertices in any order refine to the same positions and codes with
cell-wise permuted labellings. This file builds that invariance, cell
processor by cell processor, mirroring `Nauty.Equivariance`.

`segN lab lo len` reads the labelling segment of `len` positions from
`lo` as a list; cell contents are compared with `List.Perm`. The crux
is `splitCellLoop_spec`: the two-pointer partition's final pointers are
determined by the adjacency count of the cell's multiset, and its two
output segments are permutations of the adjacency filters.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The labelling segment of `len` positions from `lo`, as a list. -/
@[expose] def segN (lab : Array Nat) (lo len : Nat) : List Nat :=
  (List.range len).map fun o => lab[lo + o]!

theorem segN_length (lab : Array Nat) (lo len : Nat) :
    (segN lab lo len).length = len := by
  rw [segN, List.length_map, List.length_range]

theorem segN_zero (lab : Array Nat) (lo : Nat) : segN lab lo 0 = [] := rfl

/-- Split the first position off a segment. -/
theorem segN_cons (lab : Array Nat) (lo len : Nat) :
    segN lab lo (len + 1) = lab[lo]! :: segN lab (lo + 1) len := by
  rw [segN, segN, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero]
  exact congrArg _ (List.map_congr_left fun o _ => by
    show lab[lo + (o + 1)]! = lab[lo + 1 + o]!
    rw [show lo + (o + 1) = lo + 1 + o by omega])

/-- Split the last position off a segment. -/
theorem segN_concat (lab : Array Nat) (lo len : Nat) :
    segN lab lo (len + 1) = segN lab lo len ++ [lab[lo + len]!] := by
  rw [segN, segN, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- Segments agree when the underlying positions agree. -/
theorem segN_congr {lab lab' : Array Nat} {lo len : Nat}
    (h : ∀ o, o < len → lab[lo + o]! = lab'[lo + o]!) :
    segN lab lo len = segN lab' lo len := by
  rw [segN, segN]
  exact List.map_congr_left fun o ho => h o (List.mem_range.mp ho)

/-- The two-pointer partition, characterized: the final pointers are the
adjacency count of the cell multiset, positions outside the cell are
untouched, and the two output segments are permutations of the
adjacency filters. -/
theorem splitCellLoop_spec {gRow : Nat} :
    ∀ (k fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      0 ≤ c1 → c2 < (lab.size : Int) → c2 + 1 - c1 = (k : Int) →
      k + 1 ≤ fuel →
      (splitCellLoop gRow fuel lab c1 c2).2.1 =
          c1 + ((segN lab c1.toNat k).countP (elem gRow ·) : Int) ∧
        (splitCellLoop gRow fuel lab c1 c2).2.2 =
          c1 + ((segN lab c1.toNat k).countP (elem gRow ·) : Int) - 1 ∧
        (splitCellLoop gRow fuel lab c1 c2).1.size = lab.size ∧
        (∀ j : Nat, ((j : Int) < c1 ∨ c2 < (j : Int)) →
          (splitCellLoop gRow fuel lab c1 c2).1[j]! = lab[j]!) ∧
        ((segN (splitCellLoop gRow fuel lab c1 c2).1 c1.toNat
            ((segN lab c1.toNat k).countP (elem gRow ·))).Perm
          ((segN lab c1.toNat k).filter (elem gRow ·))) ∧
        ((segN (splitCellLoop gRow fuel lab c1 c2).1
            (c1.toNat + (segN lab c1.toNat k).countP (elem gRow ·))
            (k - (segN lab c1.toNat k).countP (elem gRow ·))).Perm
          ((segN lab c1.toNat k).filter fun v => !(elem gRow v)))
  | 0, fuel, lab, c1, c2, h1, h2, hk, hf => by
    rcases fuel with _ | f
    · omega
    rw [splitCellLoop, if_neg (by omega)]
    refine ⟨by simp [segN_zero], by simp [segN_zero]; omega, rfl,
      fun j _ => rfl, by simp [segN_zero], by simp [segN_zero]⟩
  | k + 1, fuel, lab, c1, c2, h1, h2, hk, hf => by
    rcases fuel with _ | f
    · omega
    rw [splitCellLoop, if_pos (by omega)]
    have hc1s : c1.toNat < lab.size := by omega
    have hc2s : c2.toNat < lab.size := by omega
    have hS : segN lab c1.toNat (k + 1) =
        lab[c1.toNat]! :: segN lab (c1.toNat + 1) k := segN_cons lab _ k
    rcases hadj : elem gRow lab[c1.toNat]! with _ | _
    · -- non-adjacent head: swap the ends, recurse on `[c1, c2 - 1]`
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨hp1, hp2, hsz, hout, hleft, hright⟩ :=
        splitCellLoop_spec (gRow := gRow) k f
        ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!)
        c1 (c2 - 1) h1
        (by rw [Array.size_set!, Array.size_set!]; omega)
        (by omega) (by omega)
      -- the original segment is the swapped one plus its old head
      have hS2 : (segN lab c1.toNat (k + 1)).Perm
          (lab[c1.toNat]! ::
            segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k) := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [segN_zero, hS, segN_zero]
        · have hc12 : c1.toNat ≠ c2.toNat := by omega
          have hgot : ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!)[c1.toNat]! = lab[c2.toNat]! := by
            rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hc12),
              Array.getElem!_set!_self _ _ _ hc1s]
          have hmid : segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
              c2.toNat lab[c1.toNat]!) (c1.toNat + 1) (k - 1) =
              segN lab (c1.toNat + 1) (k - 1) := by
            refine segN_congr fun o ho => ?_
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
              Array.getElem!_set!_ne _ _ _ _ (by omega)]
          have hrhs : segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
              c2.toNat lab[c1.toNat]!) c1.toNat k =
              lab[c2.toNat]! :: segN lab (c1.toNat + 1) (k - 1) := by
            rw [show k = (k - 1) + 1 by omega, segN_cons, hgot, hmid,
              Nat.add_sub_cancel]
          have hlhs : segN lab c1.toNat (k + 1) =
              lab[c1.toNat]! :: (segN lab (c1.toNat + 1) (k - 1) ++
                [lab[c2.toNat]!]) := by
            rw [hS, show k = (k - 1) + 1 by omega, segN_concat,
              show c1.toNat + 1 + (k - 1) = c2.toNat by omega,
              Nat.add_sub_cancel]
          rw [hlhs, hrhs]
          exact List.Perm.cons _ (List.perm_append_singleton _ _)
      have hcnt : (segN lab c1.toNat (k + 1)).countP (elem gRow ·) =
          (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
            lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) := by
        rw [hS2.countP_eq, List.countP_cons]
        simp [hadj]
      have hcle := List.countP_le_length (p := (elem gRow ·))
        (l := segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
          lab[c1.toNat]!) c1.toNat k)
      rw [segN_length] at hcle
      have hto1 : (c1 + ((segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
          c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) :
            Int)) = c1 + ((segN lab c1.toNat (k + 1)).countP
              (elem gRow ·) : Int) := by
        rw [hcnt]
      have hfe : ((segN lab c1.toNat (k + 1)).filter (elem gRow ·)).Perm
          ((segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
            lab[c1.toNat]!) c1.toNat k).filter (elem gRow ·)) := by
        have h := hS2.filter (elem gRow ·)
        rw [List.filter_cons_of_neg (by simp [hadj])] at h
        exact h
      have hfn : ((segN lab c1.toNat (k + 1)).filter
          fun v => !(elem gRow v)).Perm
          (lab[c1.toNat]! :: ((segN ((lab.set! c1.toNat
            lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!) c1.toNat
              k).filter fun v => !(elem gRow v))) := by
        have h := hS2.filter (fun v => !(elem gRow v))
        rw [List.filter_cons_of_pos (by simp [hadj])] at h
        exact h
      refine ⟨by rw [hcnt]; exact hp1, by rw [hcnt]; exact hp2,
        by rw [hsz, Array.size_set!, Array.size_set!], ?_, ?_, ?_⟩
      · intro j hj
        rw [hout j (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rw [hcnt]
        exact hleft.trans hfe.symm
      · rw [hcnt,
          show k + 1 - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
            c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) =
            (k - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·)) + 1
            by omega,
          segN_concat,
          show c1.toNat + (segN ((lab.set! c1.toNat lab[c2.toNat]!).set!
            c2.toNat lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·) +
            (k - (segN ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1.toNat k).countP (elem gRow ·)) =
            c2.toNat by omega]
        have hlast : (splitCellLoop gRow f
            ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat
              lab[c1.toNat]!) c1 (c2 - 1)).1[c2.toNat]! =
            lab[c1.toNat]! := by
          rw [hout c2.toNat (by omega),
            Array.getElem!_set!_self _ _ _
              (by rw [Array.size_set!]; omega)]
        rw [hlast]
        refine (List.perm_append_singleton _ _).trans ?_
        exact (List.Perm.cons _ hright).trans hfn.symm
    · -- adjacent head: advance the left pointer
      simp only [if_true]
      obtain ⟨hp1, hp2, hsz, hout, hleft, hright⟩ :=
        splitCellLoop_spec (gRow := gRow) k f lab (c1 + 1) c2 (by omega)
          h2 (by omega) (by omega)
      have hto : (c1 + 1).toNat = c1.toNat + 1 := by omega
      rw [hto] at hp1 hp2 hleft hright
      have hcnt : (segN lab c1.toNat (k + 1)).countP (elem gRow ·) =
          (segN lab (c1.toNat + 1) k).countP (elem gRow ·) + 1 := by
        rw [hS, List.countP_cons]
        simp [hadj]
      refine ⟨by rw [hcnt]; rw [hp1]; push_cast; omega,
        by rw [hcnt]; rw [hp2]; push_cast; omega, hsz, ?_, ?_, ?_⟩
      · intro j hj
        exact hout j (by omega)
      · rw [hcnt, segN_cons, hS,
          List.filter_cons_of_pos (by simp [hadj]),
          hout c1.toNat (by omega)]
        exact List.Perm.cons _ hleft
      · rw [hcnt, hS, List.filter_cons_of_neg (by simp [hadj]),
          show c1.toNat + ((segN lab (c1.toNat + 1) k).countP
            (elem gRow ·) + 1) = c1.toNat + 1 + (segN lab
              (c1.toNat + 1) k).countP (elem gRow ·) by omega,
          show k + 1 - ((segN lab (c1.toNat + 1) k).countP
            (elem gRow ·) + 1) = k - (segN lab (c1.toNat + 1) k).countP
              (elem gRow ·) by omega]
        exact hright

/-! # Cells as local runs -/

/-- A maximal run of the partition at `level`: `len` positions from `a`,
open on the inside and closed at both ends. -/
@[expose] def IsCell (ptn : Array Nat) (level a len : Nat) : Prop :=
  0 < len ∧ (a = 0 ∨ ptn[a - 1]! ≤ level) ∧
    (∀ i, a ≤ i → i + 1 < a + len → ptn[i]! > level) ∧
    ptn[a + len - 1]! ≤ level

theorem cellEnd_go_interior {ptn : Array Nat} {level : Nat} :
    ∀ (fuel j i : Nat), j ≤ i → i < cellEnd.go ptn level fuel j →
      ptn[i]! > level
  | 0, j, i, hj, hi => absurd hi (by rw [cellEnd.go]; omega)
  | fuel + 1, j, i, hj, hi => by
    rw [cellEnd.go] at hi
    split at hi
    · next h =>
      rcases Decidable.em (i = j) with rfl | hne
      · exact h
      · exact cellEnd_go_interior fuel (j + 1) i (by omega) hi
    · omega

theorem cellEnd_go_end {ptn : Array Nat} {level : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel j : Nat), j < ptn.size → ptn.size ≤ fuel + j →
      ptn[cellEnd.go ptn level fuel j]! ≤ level
  | 0, j, hj, hf => absurd hf (by omega)
  | fuel + 1, j, hj, hf => by
    rw [cellEnd.go]
    split
    · next h =>
      have hne : j ≠ ptn.size - 1 := by
        intro hjeq
        rw [hjeq] at h
        omega
      exact cellEnd_go_end hend fuel (j + 1) (by omega) (by omega)
    · next h => omega

/-- A cell of the partition, as reported by `cellEnd`, is a maximal
run. -/
theorem isCell_cellEnd {ptn : Array Nat} {level a : Nat}
    (ha : a < ptn.size) (hstart : a = 0 ∨ ptn[a - 1]! ≤ level)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    IsCell ptn level a (cellEnd ptn level a + 1 - a) := by
  have hge : a ≤ cellEnd ptn level a := cellEnd_ge
  have hlt : cellEnd ptn level a < ptn.size := cellEnd_lt ha hend
  refine ⟨by omega, hstart, ?_, ?_⟩
  · intro i hi hi2
    rw [cellEnd] at hi2
    exact cellEnd_go_interior (ptn.size - a) a i hi (by omega)
  · rw [show a + (cellEnd ptn level a + 1 - a) - 1 = cellEnd ptn level a
      by omega, cellEnd]
    exact cellEnd_go_end hend _ _ ha (by omega)

theorem cells_go_isCell {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel c1 : Nat), (c1 = 0 ∨ ptn[c1 - 1]! ≤ level) →
      ∀ p ∈ cells.go ptn level nn fuel c1,
        IsCell ptn level p.1 (p.2 + 1 - p.1)
  | 0, _, _, p, hp => absurd hp (by simp [cells.go])
  | fuel + 1, c1, hstart, p, hp => by
    rw [cells.go] at hp
    split at hp
    · next h =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · exact isCell_cellEnd (by omega) hstart hend
      · refine cells_go_isCell hnn hend fuel _ ?_ p hmem
        right
        rw [show cellEnd ptn level c1 + 1 - 1 = cellEnd ptn level c1
          by omega, cellEnd]
        exact cellEnd_go_end hend _ _ (by omega) (by omega)
    · exact absurd hp (by simp)

/-- Every cell of the partition list is a maximal run. -/
theorem cells_isCell {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ p ∈ cells ptn level nn, IsCell ptn level p.1 (p.2 + 1 - p.1) := by
  intro p hp
  rw [cells] at hp
  exact cells_go_isCell hnn hend nn 0 (Or.inl rfl) p hp

/-! # Cell-contents equivalence -/

/-- The two labellings agree, as multisets, on every cell of the
partition. -/
@[expose] def cellsPerm (ptn : Array Nat) (level : Nat)
    (lab lab' : Array Nat) : Prop :=
  ∀ a len, IsCell ptn level a len → (segN lab a len).Perm (segN lab' a len)

/-- On singleton cells, cell-equivalent labellings agree exactly. -/
theorem cellsPerm_singleton {ptn : Array Nat} {level : Nat}
    {lab lab' : Array Nat} (h : cellsPerm ptn level lab lab') {a : Nat}
    (hc : IsCell ptn level a 1) : lab[a]! = lab'[a]! := by
  have hp := h a 1 hc
  rw [segN_cons, segN_zero, segN_cons, segN_zero] at hp
  simpa using List.perm_singleton.mp hp

/-- Splitting one cell at an interior boundary: the new partition's
cells are the two halves of the split cell and the untouched old cells,
so cell-contents equivalence follows from equivalence of the halves and
of every disjoint old cell. -/
theorem cellsPerm_set! {ptn : Array Nat} {level : Nat}
    {lab lab' : Array Nat} {A lenA c : Nat}
    (hcell : IsCell ptn level A lenA) (hsize : A + lenA ≤ ptn.size)
    (hcA : A ≤ c) (hc2 : c + 1 < A + lenA)
    (hL : (segN lab A (c + 1 - A)).Perm (segN lab' A (c + 1 - A)))
    (hR : (segN lab (c + 1) (A + lenA - (c + 1))).Perm
      (segN lab' (c + 1) (A + lenA - (c + 1))))
    (hout : ∀ a len, IsCell ptn level a len →
      a + len ≤ A ∨ A + lenA ≤ a →
      (segN lab a len).Perm (segN lab' a len)) :
    cellsPerm (ptn.set! c level) level lab lab' := by
  obtain ⟨hlenA, hstartA, hintA, hendA⟩ := hcell
  intro a len hc'
  obtain ⟨hlen, hstart, hint, hend⟩ := hc'
  have hcget : (ptn.set! c level)[c]! = level :=
    Array.getElem!_set!_self _ _ _ (by omega)
  rcases Nat.lt_or_ge c a with hca | hca
  · -- the block lies right of the written boundary
    rcases Decidable.em (a = c + 1) with heq | hne
    · -- right half: show the block ends exactly at the old cell end
      have hebound : a + len - 1 = A + lenA - 1 := by
        rcases Nat.lt_trichotomy (a + len - 1) (A + lenA - 1) with
          hlt | heq | hgt
        · exfalso
          have hi := hintA (a + len - 1) (by omega) (by omega)
          rw [← Array.getElem!_set!_ne ptn c (a + len - 1) level
            (by omega)] at hi
          omega
        · exact heq
        · exfalso
          have hi := hint (A + lenA - 1) (by omega) (by omega)
          rw [Array.getElem!_set!_ne ptn c (A + lenA - 1) _
            (by omega)] at hi
          omega
      have hleneq : len = A + lenA - (c + 1) := by omega
      rw [heq, hleneq]
      exact hR
    · -- disjoint block right of the old cell
      have haright : A + lenA ≤ a := by
        rcases Nat.lt_or_ge a (A + lenA) with hlt | hge
        · exfalso
          have hi := hintA (a - 1) (by omega) (by omega)
          have hb : (ptn.set! c level)[a - 1]! ≤ level := by
            rcases hstart with h0 | hb
            · omega
            · exact hb
          rw [Array.getElem!_set!_ne ptn c (a - 1) _ (by omega)] at hb
          omega
        · exact hge
      refine hout a len ⟨hlen, ?_, ?_, ?_⟩ (Or.inr haright)
      · rcases hstart with h0 | hb
        · exact Or.inl h0
        · right
          rw [← Array.getElem!_set!_ne ptn c (a - 1) level (by omega)]
          exact hb
      · intro i hi hi2
        have := hint i hi hi2
        rw [Array.getElem!_set!_ne ptn c i _ (by omega)] at this
        exact this
      · rw [← Array.getElem!_set!_ne ptn c (a + len - 1) level (by omega)]
        exact hend
  · rcases Nat.lt_or_ge c (a + len) with hcin | hcout
    · -- the written boundary lies inside the block: block ends at `c`
      have hce : a + len - 1 = c := by
        rcases Nat.lt_trichotomy (a + len - 1) c with hlt | heq | hgt
        · omega
        · exact heq
        · exfalso
          have hi := hint c (by omega) (by omega)
          rw [hcget] at hi
          omega
      -- and starts at `A`
      have hsa : a = A := by
        rcases Nat.lt_trichotomy a A with hlt | heq | hgt
        · exfalso
          have hb : A ≥ 1 := by omega
          have hi := hint (A - 1) (by omega) (by omega)
          have hpb : ptn[A - 1]! ≤ level := by
            rcases hstartA with h0 | hb'
            · omega
            · exact hb'
          rw [Array.getElem!_set!_ne ptn c (A - 1) _ (by omega)] at hi
          omega
        · exact heq
        · exfalso
          have hi := hintA (a - 1) (by omega) (by omega)
          have hb : (ptn.set! c level)[a - 1]! ≤ level := by
            rcases hstart with h0 | hb
            · omega
            · exact hb
          rw [Array.getElem!_set!_ne ptn c (a - 1) _ (by omega)] at hb
          omega
      rw [hsa, show len = c + 1 - A by omega]
      exact hL
    · -- disjoint block left of the written boundary
      have haleft : a + len ≤ A := by
        rcases Nat.lt_or_ge (a + len - 1) A with hlt | hge
        · omega
        · exfalso
          have hi := hintA (a + len - 1) (by omega) (by omega)
          rw [← Array.getElem!_set!_ne ptn c (a + len - 1) level
            (by omega)] at hi
          omega
      refine hout a len ⟨hlen, ?_, ?_, ?_⟩ (Or.inl haleft)
      · rcases hstart with h0 | hb
        · exact Or.inl h0
        · right
          rw [← Array.getElem!_set!_ne ptn c (a - 1) level (by omega)]
          exact hb
      · intro i hi hi2
        have := hint i hi hi2
        rw [Array.getElem!_set!_ne ptn c i _ (by omega)] at this
        exact this
      · rw [← Array.getElem!_set!_ne ptn c (a + len - 1) level (by omega)]
        exact hend

end Hex.GraphIso.Nauty
