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

/-- Concatenate adjacent segments. -/
theorem segN_append (lab : Array Nat) (lo m p : Nat) :
    segN lab lo (m + p) = segN lab lo m ++ segN lab (lo + m) p := by
  induction p with
  | zero => rw [segN_zero, Nat.add_zero, List.append_nil]
  | succ q ih =>
    rw [show m + (q + 1) = (m + q) + 1 by omega, segN_concat, ih,
      segN_concat, List.append_assoc,
      show lo + (m + q) = lo + m + q by omega]

/-! # Cell-contents state equivalence -/

/-- Equal position-level fields with cell-multiset-equal labellings,
relative to the state's own partition. -/
structure StPerm (level : Nat) (st st' : RefineSt) : Prop where
  ptn : st'.ptn = st.ptn
  active : st'.active = st.active
  numcells : st'.numcells = st.numcells
  hint : st'.hint = st.hint
  maxpos : st'.maxpos = st.maxpos
  longcode : st'.longcode = st.longcode
  labSize : st'.lab.size = st.lab.size
  cells : cellsPerm st.ptn level st.lab st'.lab

/-- A cell-equivalent state is its partner with the labelling swapped
out. -/
theorem StPerm.eq_setLab {level : Nat} {st st' : RefineSt}
    (h : StPerm level st st') : st' = { st with lab := st'.lab } := by
  obtain ⟨hp, ha, hn, hh, hm, hc, _, _⟩ := h
  cases st
  cases st'
  simp only at hp ha hn hh hm hc
  simp [hp, ha, hn, hh, hm, hc]

/-- The split bookkeeping never reads the labelling, so it commutes with
swapping the labelling out. -/
theorem trivialSplit_setLab (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt) (X : Array Nat) :
    trivialSplit level cell1 cell2 c1 c2 { st with lab := X } =
      { trivialSplit level cell1 cell2 c1 c2 st with lab := X } := by
  rw [trivialSplit, trivialSplit]
  dsimp only
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · simp only [if_pos hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · simp only [if_pos hB]
      rcases hC : (c1.toNat == cell2) with _ | _ <;>
        simp only [Bool.false_eq_true, if_false, if_true]
    · simp only [if_neg hB]
      rcases hD : (c2.toNat == cell1) with _ | _ <;>
        simp only [Bool.false_eq_true, if_false, if_true]
  · simp only [if_neg hA]

/-- Two maximal runs either coincide or are disjoint. -/
theorem isCell_disjoint_or_eq {ptn : Array Nat} {level a len a' len' : Nat}
    (h : IsCell ptn level a len) (h' : IsCell ptn level a' len') :
    a' + len' ≤ a ∨ a + len ≤ a' ∨ (a = a' ∧ len = len') := by
  obtain ⟨hl, hs, hi, he⟩ := h
  obtain ⟨hl', hs', hi', he'⟩ := h'
  rcases Nat.lt_or_ge (a' + len' - 1) a with hlt | hge
  · exact Or.inl (by omega)
  rcases Nat.lt_or_ge (a + len - 1) a' with hlt' | hge'
  · exact Or.inr (Or.inl (by omega))
  right; right
  -- the runs overlap; first the starts agree
  have hstarts : a = a' := by
    rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
    · exfalso
      have hb : ptn[a' - 1]! ≤ level := by
        rcases hs' with h0 | hb
        · omega
        · exact hb
      have := hi (a' - 1) (by omega) (by omega)
      omega
    · exact heq
    · exfalso
      have hb : ptn[a - 1]! ≤ level := by
        rcases hs with h0 | hb
        · omega
        · exact hb
      have := hi' (a - 1) (by omega) (by omega)
      omega
  subst hstarts
  -- then the ends agree
  have hends : len = len' := by
    rcases Nat.lt_trichotomy len len' with hlt | heq | hgt
    · exfalso
      have := hi' (a + len - 1) (by omega) (by omega)
      omega
    · exact heq
    · exfalso
      have := hi (a + len' - 1) (by omega) (by omega)
      omega
  exact ⟨rfl, hends⟩

/-- One trivial-splitter cell preserves cell-contents equivalence: the
positional results agree and the labellings stay cell-equivalent for
the result's partition. -/
theorem trivialCell_perm {level gRow cell1 cell2 : Nat} {st st' : RefineSt}
    (h : StPerm level st st')
    (hcell : IsCell st.ptn level cell1 (cell2 + 1 - cell1))
    (hc12 : cell1 ≤ cell2) (h2 : cell2 < st.lab.size)
    (hsz : st.ptn.size = st.lab.size) :
    StPerm level (trivialCell level gRow cell1 cell2 st)
      (trivialCell level gRow cell1 cell2 st') ∧
      (∀ q : Nat, q < cell1 ∨ cell2 ≤ q →
        (trivialCell level gRow cell1 cell2 st).ptn[q]! = st.ptn[q]!) ∧
      (trivialCell level gRow cell1 cell2 st).ptn.size = st.ptn.size ∧
      (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size := by
  rcases hc : (cell1 == cell2) with _ | _
  case true =>
    rw [trivialCell, trivialCell, if_pos (by rw [hc]), if_pos (by rw [hc])]
    exact ⟨h, fun q _ => rfl, rfl, rfl⟩
  case false =>
  obtain ⟨hp1, hp2, hsz1, hout1, hleft1, hright1⟩ :=
    splitCellLoop_spec (gRow := gRow) (cell2 + 1 - cell1)
      (cell2 - cell1 + 2) st.lab (cell1 : Int) (cell2 : Int)
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hp1', hp2', hsz1', hout1', hleft1', hright1'⟩ :=
    splitCellLoop_spec (gRow := gRow) (cell2 + 1 - cell1)
      (cell2 - cell1 + 2) st'.lab (cell1 : Int) (cell2 : Int)
      (by omega)
      (by
        have := h.labSize
        omega)
      (by omega) (by omega)
  simp only [Int.toNat_natCast] at hp1 hp2 hout1 hleft1 hright1
  simp only [Int.toNat_natCast] at hp1' hp2' hout1' hleft1' hright1'
  have hseg : (segN st.lab cell1 (cell2 + 1 - cell1)).Perm
      (segN st'.lab cell1 (cell2 + 1 - cell1)) :=
    h.cells cell1 _ hcell
  have hcq : (segN st'.lab cell1 (cell2 + 1 - cell1)).countP
      (elem gRow ·) = (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) := (hseg.countP_eq _).symm
  rw [hcq] at hp1' hp2' hleft1' hright1'
  have hcle := List.countP_le_length (p := (elem gRow ·))
    (l := segN st.lab cell1 (cell2 + 1 - cell1))
  rw [segN_length] at hcle
  -- both runs feed identical pointers to the split bookkeeping
  have e1 : trivialCell level gRow cell1 cell2 st =
      { trivialSplit level cell1 cell2
          ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
            cell1)).countP (elem gRow ·) : Int))
          ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
            cell1)).countP (elem gRow ·) : Int) - 1) st with
        lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (cell1 : Int) (cell2 : Int)).1 } := by
    rw [trivialCell, if_neg (by rw [hc]; simp)]
    simp only [Int.ofNat_eq_natCast]
    rw [hp1, hp2, trivialSplit_setLab _ _ _ _ _ st]
  have e2 : trivialCell level gRow cell1 cell2 st' =
      { trivialSplit level cell1 cell2
          ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
            cell1)).countP (elem gRow ·) : Int))
          ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
            cell1)).countP (elem gRow ·) : Int) - 1) st with
        lab := (splitCellLoop gRow (cell2 - cell1 + 2) st'.lab
          (cell1 : Int) (cell2 : Int)).1 } := by
    rw [trivialCell, if_neg (by rw [hc]; simp)]
    simp only [Int.ofNat_eq_natCast]
    rw [hp1', hp2', trivialSplit_setLab _ _ _ _ _ st', h.eq_setLab,
      trivialSplit_setLab _ _ _ _ _ st]
  rw [e1, e2]
  -- disjoint old cells are untouched by both runs
  have houtP : ∀ a len, IsCell st.ptn level a len →
      a + len ≤ cell1 ∨ cell1 + (cell2 + 1 - cell1) ≤ a →
      (segN (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
        (cell1 : Int) (cell2 : Int)).1 a len).Perm
      (segN (splitCellLoop gRow (cell2 - cell1 + 2) st'.lab
        (cell1 : Int) (cell2 : Int)).1 a len) := by
    intro a len hic hdis
    have hLseg : segN (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
        (cell1 : Int) (cell2 : Int)).1 a len =
        segN st.lab a len :=
      segN_congr fun o ho => hout1 (a + o) (by omega)
    have hRseg : segN (splitCellLoop gRow (cell2 - cell1 + 2) st'.lab
        (cell1 : Int) (cell2 : Int)).1 a len =
        segN st'.lab a len :=
      segN_congr fun o ho => hout1' (a + o) (by omega)
    rw [hLseg, hRseg]
    exact h.cells a len hic
  -- the whole processed segment stays cell-equivalent
  have hwhole : (segN (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
      (cell1 : Int) (cell2 : Int)).1 cell1
        (cell2 + 1 - cell1)).Perm
      (segN (splitCellLoop gRow (cell2 - cell1 + 2) st'.lab
        (cell1 : Int) (cell2 : Int)).1 cell1
          (cell2 + 1 - cell1)) := by
    have hsplitL := segN_append (splitCellLoop gRow (cell2 - cell1 + 2)
      st.lab (cell1 : Int) (cell2 : Int)).1 cell1
      ((segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·))
      ((cell2 + 1 - cell1) - (segN st.lab cell1 (cell2 + 1 -
        cell1)).countP (elem gRow ·))
    have hsplitR := segN_append (splitCellLoop gRow (cell2 - cell1 + 2)
      st'.lab (cell1 : Int) (cell2 : Int)).1 cell1
      ((segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·))
      ((cell2 + 1 - cell1) - (segN st.lab cell1 (cell2 + 1 -
        cell1)).countP (elem gRow ·))
    rw [show (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) + ((cell2 + 1 - cell1) - (segN st.lab cell1
          (cell2 + 1 - cell1)).countP (elem gRow ·)) =
        cell2 + 1 - cell1 by omega] at hsplitL hsplitR
    rw [hsplitL, hsplitR]
    have hA1 := (hleft1.append hright1).trans (List.filter_append_perm _ _)
    have hA2 := (hleft1'.append hright1').trans (List.filter_append_perm _ _)
    exact hA1.trans (hseg.trans hA2.symm)
  -- classify the result partition by the split guard
  rcases Decidable.em (((cell1 : Int) + ((segN st.lab cell1 (cell2 +
      1 - cell1)).countP (elem gRow ·) : Int) - 1) ≥ Int.ofNat cell1 ∧
      ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
        cell1)).countP (elem gRow ·) : Int)) ≤ Int.ofNat cell2) with
    hg | hg
  · -- proper split: one boundary written strictly inside the cell
    have hcnt1 : 1 ≤ (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) := by
      have h1 := hg.1
      simp only [Int.ofNat_eq_natCast] at h1
      omega
    have hcnt2 : (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) ≤ cell2 - cell1 := by
      have h1 := hg.2
      simp only [Int.ofNat_eq_natCast] at h1
      omega
    have hptn : (trivialSplit level cell1 cell2
        ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) : Int))
        ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) : Int) - 1) st).ptn =
        st.ptn.set! (cell1 + (segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) - 1) level := by
      rw [trivialSplit, if_pos hg,
        show (((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) : Int) - 1)).toNat =
          cell1 + (segN st.lab cell1 (cell2 + 1 - cell1)).countP
            (elem gRow ·) - 1 by omega]
      split
      · split <;> rfl
      · split <;> rfl
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl,
      by rw [hsz1', hsz1, h.labSize], ?_⟩, ?_, ?_, by dsimp only; rw [hsz1]⟩
    · dsimp only
      rw [hptn]
      refine cellsPerm_set! hcell (by omega) (by omega) (by omega)
        ?_ ?_ houtP
      · rw [show cell1 + (segN st.lab cell1 (cell2 + 1 - cell1)).countP
          (elem gRow ·) - 1 + 1 - cell1 =
          (segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·)
          by omega]
        exact hleft1.trans ((hseg.filter _).trans hleft1'.symm)
      · rw [show cell1 + (segN st.lab cell1 (cell2 + 1 - cell1)).countP
            (elem gRow ·) - 1 + 1 = cell1 + (segN st.lab cell1 (cell2 +
              1 - cell1)).countP (elem gRow ·) by omega,
          show cell1 + (cell2 + 1 - cell1) - (cell1 + (segN st.lab cell1
            (cell2 + 1 - cell1)).countP (elem gRow ·)) =
            (cell2 + 1 - cell1) - (segN st.lab cell1 (cell2 + 1 -
              cell1)).countP (elem gRow ·) by omega]
        exact hright1.trans ((hseg.filter _).trans hright1'.symm)
    · intro q hq
      dsimp only
      rw [hptn, Array.getElem!_set!_ne _ _ _ _ (by omega : cell1 +
        (segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) -
          1 ≠ q)]
    · dsimp only
      rw [hptn, Array.size_set!]
  · -- degenerate split: the partition is unchanged
    have hptn : (trivialSplit level cell1 cell2
        ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) : Int))
        ((cell1 : Int) + ((segN st.lab cell1 (cell2 + 1 -
          cell1)).countP (elem gRow ·) : Int) - 1) st).ptn =
        st.ptn := by
      rw [trivialSplit, if_neg hg]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl,
      by rw [hsz1', hsz1, h.labSize], ?_⟩,
      fun q _ => by dsimp only; rw [hptn],
      by dsimp only; rw [hptn],
      by dsimp only; rw [hsz1]⟩
    dsimp only
    rw [hptn]
    intro a len hic
    rcases isCell_disjoint_or_eq hic hcell with hd | hd | ⟨ha, hlen⟩
    · exact houtP a len hic (Or.inr (by omega))
    · exact houtP a len hic (Or.inl (by omega))
    · subst ha
      rw [hlen]
      exact hwhole

/-! # The trivial-splitter pass -/

theorem cells_go_start {ptn : Array Nat} {level nn : Nat} :
    ∀ (fuel c1 : Nat), ∀ p ∈ cells.go ptn level nn fuel c1, c1 ≤ p.1
  | 0, _, p, hp => absurd hp (by simp [cells.go])
  | fuel + 1, c1, p, hp => by
    rw [cells.go] at hp
    split at hp
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · exact Nat.le_refl _
      · have h1 := cells_go_start fuel _ p hmem
        have hge : c1 ≤ cellEnd ptn level c1 := cellEnd_ge
        omega
    · exact absurd hp (by simp)

theorem cells_go_pairwise {ptn : Array Nat} {level nn : Nat} :
    ∀ (fuel c1 : Nat),
      (cells.go ptn level nn fuel c1).Pairwise fun p q => p.2 < q.1
  | 0, _ => by
    rw [cells.go]
    exact List.Pairwise.nil
  | fuel + 1, c1 => by
    rw [cells.go]
    split
    · refine List.Pairwise.cons ?_ (cells_go_pairwise fuel _)
      intro q hq
      have h1 := cells_go_start fuel _ q hq
      show cellEnd ptn level c1 < q.1
      omega
    · exact List.Pairwise.nil

/-- The partition's cells are listed in strictly increasing position
order. -/
theorem cells_pairwise {ptn : Array Nat} {level nn : Nat} :
    (cells ptn level nn).Pairwise fun p q => p.2 < q.1 := by
  rw [cells]
  exact cells_go_pairwise nn 0

/-- A maximal run survives partition edits that avoid its closed
neighbourhood. -/
theorem isCell_of_agree {ptn ptn' : Array Nat} {level a len : Nat}
    (h : IsCell ptn level a len)
    (hagree : ∀ q, a - 1 ≤ q → q ≤ a + len - 1 → ptn'[q]! = ptn[q]!) :
    IsCell ptn' level a len := by
  obtain ⟨hl, hs, hi, he⟩ := h
  refine ⟨hl, ?_, ?_, ?_⟩
  · rcases hs with h0 | hb
    · exact Or.inl h0
    · exact Or.inr (by rw [hagree (a - 1) (by omega) (by omega)]; exact hb)
  · intro i hi1 hi2
    rw [hagree i (by omega) (by omega)]
    exact hi i hi1 hi2
  · rw [hagree (a + len - 1) (by omega) (by omega)]
    exact he

theorem refineTrivial_go_perm {level gRow : Nat} :
    ∀ (cs : List (Nat × Nat)) (st st' : RefineSt), StPerm level st st' →
      st.ptn.size = st.lab.size →
      (∀ p ∈ cs, IsCell st.ptn level p.1 (p.2 + 1 - p.1) ∧
        p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      StPerm level (refineTrivial.go level gRow cs st)
        (refineTrivial.go level gRow cs st') ∧
      (refineTrivial.go level gRow cs st).lab.size = st.lab.size ∧
      (refineTrivial.go level gRow cs st).ptn.size = st.ptn.size
  | [], _, _, h, _, _, _ => ⟨h, rfl, rfl⟩
  | (c1, c2) :: rest, st, st', h, hsz, hcs, hpair => by
    rw [refineTrivial.go, refineTrivial.go]
    obtain ⟨hstep, hdiff, hpsz, hlsz⟩ := trivialCell_perm
      (gRow := gRow) h (hcs (c1, c2) (by simp)).1
      (by
        have h1 := (hcs (c1, c2) (by simp)).1.1
        omega)
      (hcs (c1, c2) (by simp)).2 hsz
    have hrest := (List.pairwise_cons.mp hpair).1
    obtain ⟨hrec, hrsz, hrpsz⟩ := refineTrivial_go_perm rest
      (trivialCell level gRow c1 c2 st)
      (trivialCell level gRow c1 c2 st') hstep
      (by rw [hpsz, hlsz]; exact hsz)
      (fun p hp => ⟨isCell_of_agree (hcs p (by simp [hp])).1
          (fun q hq1 hq2 => hdiff q (Or.inr (by
            have := hrest p hp
            omega))),
        by rw [hlsz]; exact (hcs p (by simp [hp])).2⟩)
      (List.pairwise_cons.mp hpair).2
    exact ⟨hrec, by rw [hrsz, hlsz], by rw [hrpsz, hpsz]⟩

/-- The trivial-splitter pass preserves cell-contents equivalence. -/
theorem refineTrivial_perm {ctx : Ctx} {level split1 : Nat}
    {st st' : RefineSt} (h : StPerm level st st')
    (hsz : st.ptn.size = st.lab.size) (hnn : ctx.n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hsplit : IsCell st.ptn level split1 1) :
    StPerm level (refineTrivial ctx level split1 st)
      (refineTrivial ctx level split1 st') ∧
    (refineTrivial ctx level split1 st).lab.size = st.lab.size ∧
    (refineTrivial ctx level split1 st).ptn.size = st.ptn.size := by
  rw [refineTrivial, refineTrivial, h.ptn,
    show st'.lab[split1]! = st.lab[split1]! from
      (cellsPerm_singleton h.cells hsplit).symm]
  exact refineTrivial_go_perm (cells st.ptn level ctx.n) st st' h hsz
    (fun p hp => ⟨cells_isCell hnn hend p hp,
      by
        have := cells_bound hnn hend p hp
        omega⟩)
    cells_pairwise

/-! # Region-confined partition edits -/

/-- Cell-contents equivalence after arbitrary partition edits confined
to the interior of one old cell: every new cell either lies inside the
edited region (equivalence supplied per new cell) or is an untouched
old cell. -/
theorem cellsPerm_of_region {ptn ptn' : Array Nat} {level : Nat}
    {lab lab' : Array Nat} {A lenA : Nat}
    (hcell : IsCell ptn level A lenA)
    (hagree : ∀ q, q < A ∨ A + lenA - 1 ≤ q → ptn'[q]! = ptn[q]!)
    (hin : ∀ x len', IsCell ptn' level x len' → A ≤ x →
      x + len' ≤ A + lenA → (segN lab x len').Perm (segN lab' x len'))
    (hout : ∀ x len', IsCell ptn level x len' →
      x + len' ≤ A ∨ A + lenA ≤ x →
      (segN lab x len').Perm (segN lab' x len')) :
    cellsPerm ptn' level lab lab' := by
  obtain ⟨hlenA, hstartA, hintA, hendA⟩ := hcell
  intro a len hc'
  obtain ⟨hlen, hstart, hint, hend⟩ := hc'
  rcases Decidable.em (a + len ≤ A ∨ A + lenA ≤ a) with hdis | hmid
  · -- disjoint: an untouched old cell
    refine hout a len ⟨hlen, ?_, ?_, ?_⟩ hdis
    · rcases hstart with h0 | hb
      · exact Or.inl h0
      · exact Or.inr (by rw [← hagree (a - 1) (by omega)]; exact hb)
    · intro i hi1 hi2
      rw [← hagree i (by omega)]
      exact hint i hi1 hi2
    · rw [← hagree (a + len - 1) (by omega)]
      exact hend
  · -- intersecting: contained in the edited region
    have hAin : A ≤ a := by
      rcases Nat.lt_or_ge a A with hlt | hge
      · exfalso
        have hb : ptn'[A - 1]! ≤ level := by
          rcases hstartA with h0 | hb
          · omega
          · rw [hagree (A - 1) (by omega)]
            exact hb
        have := hint (A - 1) (by omega) (by omega)
        omega
      · exact hge
    have hBin : a + len ≤ A + lenA := by
      rcases Nat.lt_or_ge (A + lenA) (a + len) with hlt | hge
      · exfalso
        have hb : ptn'[A + lenA - 1]! ≤ level := by
          rw [hagree (A + lenA - 1) (by omega)]
          exact hendA
        have := hint (A + lenA - 1) (by omega) (by omega)
        omega
      · exact hge
    exact hin a len ⟨hlen, hstart, hint, hend⟩ hAin hBin

/-! # Nontrivial-splitter ingredients -/

theorem testBit_foldl_insert (lab : Array Nat) (lo : Nat) (v : Nat) :
    ∀ (l : List Nat) (w : Nat),
      ((l.foldl (fun w o => insert w lab[lo + o]!) w).testBit v) =
        (w.testBit v || l.any fun o => lab[lo + o]! == v)
  | [], w => by simp
  | o :: l, w => by
    rw [List.foldl_cons, List.any_cons,
      testBit_foldl_insert lab lo v l (insert w lab[lo + o]!),
      testBit_insert]
    simp [Bool.or_assoc]

/-- The splitter set holds exactly the segment's members. -/
theorem testBit_worksetOf (lab : Array Nat) (lo hi v : Nat) :
    (worksetOf lab lo hi).testBit v =
      (segN lab lo (hi + 1 - lo)).any (· == v) := by
  rw [worksetOf, testBit_foldl_insert, segN, List.any_map,
    Nat.zero_testBit, Bool.false_or]
  congr 1

/-- Cell-equivalent segments give the same splitter set. -/
theorem worksetOf_perm {lab lab' : Array Nat} {lo hi : Nat}
    (h : (segN lab lo (hi + 1 - lo)).Perm (segN lab' lo (hi + 1 - lo))) :
    worksetOf lab lo hi = worksetOf lab' lo hi := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [testBit_worksetOf, testBit_worksetOf, Bool.eq_iff_iff,
    List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mp hx, hp⟩,
    fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.mpr hx, hp⟩⟩

/-- The neighbour counts are the segment mapped through the per-vertex
count. -/
theorem countsOf_eq_map (ctx : Ctx) (lab : Array Nat)
    (workset cell1 cell2 : Nat) :
    countsOf ctx lab workset cell1 cell2 =
      (segN lab cell1 (cell2 + 1 - cell1)).map
        fun v => popCount (workset &&& ctx.g[v]!) := by
  rw [countsOf, segN, List.map_map]
  exact List.map_congr_left fun o _ => rfl

theorem foldl_min_le : ∀ (l : List Nat) (a : Nat), l.foldl Nat.min a ≤ a
  | [], a => Nat.le_refl a
  | x :: l, a =>
    Nat.le_trans (foldl_min_le l (Nat.min a x)) (Nat.min_le_left a x)

theorem foldl_min_le_mem :
    ∀ (l : List Nat) (a x : Nat), x ∈ l → l.foldl Nat.min a ≤ x
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.le_trans (foldl_min_le l (Nat.min a x))
        (Nat.min_le_right a x)
    · exact foldl_min_le_mem l (Nat.min a y) x hmem

theorem foldl_min_choice :
    ∀ (l : List Nat) (a : Nat), l.foldl Nat.min a = a ∨ l.foldl Nat.min a ∈ l
  | [], a => Or.inl rfl
  | x :: l, a => by
    rw [List.foldl_cons]
    rcases foldl_min_choice l (Nat.min a x) with heq | hmem
    · rw [heq]
      rcases Nat.le_total a x with hax | hax
      · exact Or.inl (by rw [Nat.min_eq_min]; omega)
      · exact Or.inr (by
          rw [show Nat.min a x = x by rw [Nat.min_eq_min]; omega]
          simp)
    · exact Or.inr (by simp [hmem])

/-- The running minimum seeded by the head is permutation-invariant. -/
theorem foldl_min_headD_perm {l l' : List Nat} (h : l.Perm l') :
    l.foldl Nat.min (l.headD 0) = l'.foldl Nat.min (l'.headD 0) := by
  rcases l with _ | ⟨x, t⟩
  · rw [List.nil_perm.mp h]
  · rcases l' with _ | ⟨y, t'⟩
    · exact absurd h (by simp)
    · have hmem1 : (x :: t).foldl Nat.min ((x :: t).headD 0) ∈ x :: t := by
        rcases foldl_min_choice (x :: t) ((x :: t).headD 0) with heq | hm
        · rw [heq]
          simp
        · exact hm
      have hmem2 : (y :: t').foldl Nat.min ((y :: t').headD 0) ∈
          y :: t' := by
        rcases foldl_min_choice (y :: t') ((y :: t').headD 0) with heq | hm
        · rw [heq]
          simp
        · exact hm
      exact Nat.le_antisymm
        (foldl_min_le_mem _ _ _ (h.mem_iff.mpr hmem2))
        (foldl_min_le_mem _ _ _ (h.mem_iff.mp hmem1))

theorem foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl Nat.max a
  | [], a => Nat.le_refl a
  | x :: l, a =>
    Nat.le_trans (Nat.le_max_left a x) (foldl_max_ge l (Nat.max a x))

theorem foldl_max_ge_mem :
    ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl Nat.max a
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge l _)
    · exact foldl_max_ge_mem l (Nat.max a y) x hmem

theorem foldl_max_choice :
    ∀ (l : List Nat) (a : Nat), l.foldl Nat.max a = a ∨ l.foldl Nat.max a ∈ l
  | [], a => Or.inl rfl
  | x :: l, a => by
    rw [List.foldl_cons]
    rcases foldl_max_choice l (Nat.max a x) with heq | hmem
    · rw [heq]
      rcases Nat.le_total a x with hax | hax
      · exact Or.inr (by
          rw [show Nat.max a x = x by rw [Nat.max_eq_max]; omega]
          simp)
      · exact Or.inl (by rw [Nat.max_eq_max]; omega)
    · exact Or.inr (by simp [hmem])

/-- The running maximum seeded by the head is permutation-invariant. -/
theorem foldl_max_headD_perm {l l' : List Nat} (h : l.Perm l') :
    l.foldl Nat.max (l.headD 0) = l'.foldl Nat.max (l'.headD 0) := by
  rcases l with _ | ⟨x, t⟩
  · rw [List.nil_perm.mp h]
  · rcases l' with _ | ⟨y, t'⟩
    · exact absurd h (by simp)
    · have hmem1 : (x :: t).foldl Nat.max ((x :: t).headD 0) ∈ x :: t := by
        rcases foldl_max_choice (x :: t) ((x :: t).headD 0) with heq | hm
        · rw [heq]
          simp
        · exact hm
      have hmem2 : (y :: t').foldl Nat.max ((y :: t').headD 0) ∈
          y :: t' := by
        rcases foldl_max_choice (y :: t') ((y :: t').headD 0) with heq | hm
        · rw [heq]
          simp
        · exact hm
      exact Nat.le_antisymm
        (foldl_max_ge_mem _ _ _ (h.mem_iff.mp hmem1))
        (foldl_max_ge_mem _ _ _ (h.mem_iff.mpr hmem2))

/-! # Window-scan structure -/

/-- The window-scan bookkeeping never reads the labelling. -/
theorem windowStep_setLab (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt) (X : Array Nat) :
    windowStep level cell1 cell2 v c1 c2 maxcell { st with lab := X } =
      { windowStep level cell1 cell2 v c1 c2 maxcell st with
        lab := X } := by
  rw [windowStep, windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, if_false, if_true]

theorem windowScan_setLab (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt)
      (X : Array Nat),
      windowScan level cell1 cell2 counts values c1 maxcell
          { st with lab := X } =
        { windowScan level cell1 cell2 counts values c1 maxcell st with
          lab := X }
  | [], _, _, _, _ => rfl
  | v :: vs, c1, maxcell, st, X => by
    rw [windowScan, windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [if_pos hm]
      rw [windowStep_setLab]
      exact windowScan_setLab level cell1 cell2 counts vs _ _ _ X
    · simp only [if_neg hm]
      exact windowScan_setLab level cell1 cell2 counts vs c1 maxcell st X

/-- The window scan reads the counts only through the multiplicities. -/
theorem windowScan_counts_congr (level cell1 cell2 : Nat)
    {counts counts' : List Nat}
    (hm : ∀ v, multOf counts v = multOf counts' v) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      windowScan level cell1 cell2 counts values c1 maxcell st =
        windowScan level cell1 cell2 counts' values c1 maxcell st
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScan, windowScan, hm v]
    rcases Decidable.em (multOf counts' v > 0) with hmv | hmv
    · simp only [if_pos hmv]
      rw [windowScan_counts_congr level cell1 cell2 hm vs _ _ _]
    · simp only [if_neg hmv]
      exact windowScan_counts_congr level cell1 cell2 hm vs c1 maxcell st

/-- One window step's partition effect: the group end boundary, if it
lies inside the cell. -/
theorem ptn_windowStep_eq (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).ptn =
      if c2 ≤ cell2 then st.ptn.set! (c2 - 1) level else st.ptn := by
  rw [windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, if_false, if_true]

/-! # Segment write-back -/

theorem writeSegment_outside :
    ∀ (seg : List Nat) (lab : Array Nat) (lo q : Nat),
      q < lo ∨ lo + seg.length ≤ q →
      (writeSegment lab lo seg)[q]! = lab[q]!
  | [], _, _, _, _ => rfl
  | x :: seg, lab, lo, q, hq => by
    simp only [List.length_cons] at hq
    rw [writeSegment,
      writeSegment_outside seg _ (lo + 1) q (by omega),
      Array.getElem!_set!_ne _ _ _ _ (by omega)]

theorem writeSegment_size :
    ∀ (seg : List Nat) (lab : Array Nat) (lo : Nat),
      (writeSegment lab lo seg).size = lab.size
  | [], _, _ => rfl
  | x :: seg, lab, lo => by
    rw [writeSegment, writeSegment_size seg _ (lo + 1), Array.size_set!]

/-- Writing a segment and reading it back. -/
theorem segN_writeSegment :
    ∀ (seg : List Nat) (lab : Array Nat) (lo : Nat),
      lo + seg.length ≤ lab.size →
      segN (writeSegment lab lo seg) lo seg.length = seg
  | [], _, _, _ => rfl
  | x :: seg, lab, lo, hsz => by
    simp only [List.length_cons] at hsz ⊢
    rw [segN_cons, writeSegment]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · rw [writeSegment_outside seg _ (lo + 1) lo (by omega),
        Array.getElem!_set!_self _ _ _ (by omega)]
    · exact segN_writeSegment seg (lab.set! lo x) (lo + 1)
        (by rw [Array.size_set!]; omega)

/-! # Group decomposition -/

theorem isCell_split_right {ptn : Array Nat} {level A lenA c : Nat}
    (h : IsCell ptn level A lenA) (hc1 : A ≤ c) (hc2 : c + 1 < A + lenA)
    (hcs : c < ptn.size) :
    IsCell (ptn.set! c level) level (c + 1) (A + lenA - (c + 1)) := by
  obtain ⟨hl, hs, hi, he⟩ := h
  refine ⟨by omega, Or.inr ?_, ?_, ?_⟩
  · rw [show c + 1 - 1 = c by omega, Array.getElem!_set!_self _ _ _ hcs]
    exact Nat.le_refl level
  · intro i hi1 hi2
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact hi i (by omega) (by omega)
  · rw [show c + 1 + (A + lenA - (c + 1)) - 1 = A + lenA - 1 by omega,
      Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact he

theorem flatMap_congr_mem {g g' : Nat → List Nat} :
    ∀ (l : List Nat), (∀ a ∈ l, g a = g' a) →
      l.flatMap g = l.flatMap g'
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      flatMap_congr_mem l (fun a ha => h a (by simp [ha]))]

theorem flatMap_perm_of_pointwise {g g' : Nat → List Nat} :
    ∀ (vs : List Nat), (∀ v ∈ vs, (g v).Perm (g' v)) →
      (vs.flatMap g).Perm (vs.flatMap g')
  | [], _ => List.Perm.refl _
  | v :: vs, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h v (by simp)).append
      (flatMap_perm_of_pointwise vs fun u hu => h u (by simp [hu]))

theorem zipIdx_filter_map_eq_filter (f : Nat → Nat) (v : Nat) :
    ∀ (S : List Nat) (k : Nat) (get : Nat → Nat),
      (∀ j, j < S.length → get (k + j) = S[j]!) →
      ((((S.map f).zipIdx k).filter fun p => p.1 == v).map
        fun p => get p.2) = S.filter fun x => f x == v
  | [], _, _, _ => rfl
  | x :: S, k, get, hget => by
    rw [List.map_cons, List.zipIdx_cons, List.filter_cons, List.filter_cons]
    have hx : get k = x := by
      have := hget 0 (by simp)
      simpa using this
    rcases hfx : (f x == v) with _ | _
    · simp only [Bool.false_eq_true, if_false]
      exact zipIdx_filter_map_eq_filter f v S (k + 1) get
        (fun j hj => by
          rw [show k + 1 + j = k + (j + 1) by omega]
          have := hget (j + 1) (by simp; omega)
          simpa using this)
    · simp only [if_true, List.map_cons]
      refine List.cons_eq_cons.mpr ⟨hx, ?_⟩
      exact zipIdx_filter_map_eq_filter f v S (k + 1) get
        (fun j hj => by
          rw [show k + 1 + j = k + (j + 1) by omega]
          have := hget (j + 1) (by simp; omega)
          simpa using this)

/-- The stable counting redistribution groups the segment by count
value: with counts read off the segment, `segmentOf` is the
concatenation of the value filters. -/
theorem segmentOf_eq_flatMap (lab : Array Nat) (cell1 : Nat)
    (S : List Nat) (f : Nat → Nat) (values : List Nat)
    (hS : ∀ j, j < S.length → lab[cell1 + j]! = S[j]!) :
    segmentOf lab cell1 (S.map f) values =
      values.flatMap fun v => S.filter fun x => f x == v := by
  rw [segmentOf]
  refine congrArg values.flatMap ?_
  funext v
  exact zipIdx_filter_map_eq_filter f v S 0 (fun j => lab[cell1 + j]!)
    (fun j hj => by rw [Nat.zero_add]; exact hS j hj)

theorem segN_getElem! (lab : Array Nat) (lo len j : Nat) (hj : j < len) :
    (segN lab lo len)[j]! = lab[lo + j]! := by
  rw [segN, getElem!_pos _ _ (by rw [List.length_map, List.length_range]; exact hj),
    List.getElem_map, List.getElem_range]

theorem filter_filter_ne {f : Nat → Nat} {u v : Nat} (huv : u ≠ v)
    (S : List Nat) :
    (S.filter fun x => !(f x == v)).filter (fun x => f x == u) =
      S.filter fun x => f x == u := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    rw [List.filter_cons]
    rcases hfv : (f x == v) with _ | _
    · simp only [Bool.not_false, if_true]
      rw [List.filter_cons, List.filter_cons, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [List.filter_cons, ih]
      have hfu : (f x == u) = false := by
        simp only [beq_iff_eq] at hfv
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      rw [hfu]
      simp

/-- Concatenating the value-filters over distinct values that cover the
list recovers the list, as a multiset. -/
theorem flatMap_filters_perm {f : Nat → Nat} :
    ∀ (values S : List Nat), values.Nodup → (∀ x ∈ S, f x ∈ values) →
      ((values.flatMap fun v => S.filter fun x => f x == v).Perm S)
  | [], S, _, hcov => by
    rcases S with _ | ⟨x, S⟩
    · exact List.Perm.refl _
    · exact absurd (hcov x (by simp)) (by simp)
  | v :: values, S, hnd, hcov => by
    rw [List.flatMap_cons]
    have hrec := flatMap_filters_perm values
      (S.filter fun x => !(f x == v)) (List.nodup_cons.mp hnd).2
      (fun x hx => by
        have hm := List.mem_filter.mp hx
        have := hcov x hm.1
        simp only [List.mem_cons] at this
        rcases this with heq | hmem
        · exfalso
          have := hm.2
          simp [heq] at this
        · exact hmem)
    have hcong : (values.flatMap fun u =>
        (S.filter fun x => !(f x == v)).filter fun x => f x == u) =
        values.flatMap fun u => S.filter fun x => f x == u := by
      refine flatMap_congr_mem values fun u hu => ?_
      refine filter_filter_ne (fun heq => ?_) S
      subst heq
      exact (List.nodup_cons.mp hnd).1 hu
    rw [hcong] at hrec
    exact (List.Perm.append (List.Perm.refl _) hrec).trans
      (List.filter_append_perm _ S)

/-! # Window writes preserve cell equivalence -/

theorem ptn_windowScan_outside (level cell1 cell2 : Nat)
    (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt),
      cell1 ≤ c1acc → ∀ q, q < cell1 ∨ cell2 ≤ q →
      (windowScan level cell1 cell2 counts vs c1acc maxcell
        st).ptn[q]! = st.ptn[q]!
  | [], _, _, _, _, _, _ => rfl
  | v :: vs, c1acc, maxcell, st, hc1, q, hq => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [if_pos hm]
      rw [ptn_windowScan_outside level cell1 cell2 counts vs _ _ _
        (by omega) q hq, ptn_windowStep_eq]
      split
      · next hle =>
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rfl
    · simp only [if_neg hm]
      exact ptn_windowScan_outside level cell1 cell2 counts vs _ _ _
        hc1 q hq

theorem ptn_windowScan_size (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1acc : Nat) (maxcell : Int) (st : RefineSt),
      (windowScan level cell1 cell2 counts vs c1acc maxcell
        st).ptn.size = st.ptn.size
  | [], _, _, _ => rfl
  | v :: vs, c1acc, maxcell, st => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [if_pos hm]
      rw [ptn_windowScan_size level cell1 cell2 counts vs _ _ _,
        ptn_windowStep_eq]
      split
      · rw [Array.size_set!]
      · rfl
    · simp only [if_neg hm]
      exact ptn_windowScan_size level cell1 cell2 counts vs _ _ _

/-- The window scan's boundary writes preserve cell-contents equivalence
of the final labellings: each nonempty group becomes a cell whose two
contents are permutations of matching value filters. -/
theorem windowScan_region_perm (level cell1 cell2 : Nat)
    (counts : List Nat) {L L' : Array Nat} (gL gL' : Nat → List Nat)
    (hGperm : ∀ v, (gL v).Perm (gL' v))
    (hGlen : ∀ v, (gL v).length = multOf counts v) :
    ∀ (vs : List Nat) (start : Nat) (maxcell : Int) (st : RefineSt),
      (start ≤ cell2 → IsCell st.ptn level start (cell2 + 1 - start)) →
      cell2 < st.ptn.size →
      cellsPerm st.ptn level L L' →
      segN L start (cell2 + 1 - start) = vs.flatMap gL →
      segN L' start (cell2 + 1 - start) = vs.flatMap gL' →
      cellsPerm (windowScan level cell1 cell2 counts vs start
        maxcell st).ptn level L L'
  | [], _, _, _, _, _, hcp, _, _ => hcp
  | v :: vs, start, maxcell, st, hcellR, hc2s, hcp, hlayL, hlayL' => by
    rw [windowScan]
    have hGlen' : ∀ u, (gL' u).length = multOf counts u := fun u => by
      rw [← (hGperm u).length_eq]
      exact hGlen u
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [if_pos hm]
      -- the group is nonempty, so the region reaches it
      have hlen0 := congrArg List.length hlayL
      rw [segN_length, List.flatMap_cons, List.length_append,
        hGlen v] at hlen0
      have hlen0' := congrArg List.length hlayL'
      rw [segN_length, List.flatMap_cons, List.length_append,
        hGlen' v] at hlen0'
      have hstart2 : start ≤ cell2 := by omega
      have hsplitL : segN L start (cell2 + 1 - start) =
          segN L start (multOf counts v) ++
            segN L (start + multOf counts v)
              (cell2 + 1 - start - multOf counts v) := by
        rw [← segN_append]
        congr 1
        omega
      have hsplitL' : segN L' start (cell2 + 1 - start) =
          segN L' start (multOf counts v) ++
            segN L' (start + multOf counts v)
              (cell2 + 1 - start - multOf counts v) := by
        rw [← segN_append]
        congr 1
        omega
      obtain ⟨hchunkL, hrestL⟩ := List.append_inj
        (hsplitL.symm.trans (by rw [hlayL, List.flatMap_cons]))
        (by rw [segN_length, hGlen v])
      obtain ⟨hchunkL', hrestL'⟩ := List.append_inj
        (hsplitL'.symm.trans (by rw [hlayL', List.flatMap_cons]))
        (by rw [segN_length, hGlen' v])
      have hptn1 := ptn_windowStep_eq level cell1 cell2 v start
        (start + multOf counts v) maxcell st
      rcases Decidable.em (start + multOf counts v ≤ cell2) with
        hin | houtc
      · rw [if_pos hin] at hptn1
        have hcellS := hcellR hstart2
        have hcp1 : cellsPerm (st.ptn.set!
            (start + multOf counts v - 1) level) level L L' := by
          refine cellsPerm_set! hcellS (by omega) (by omega) (by omega)
            ?_ ?_ (fun x len hx _ => hcp x len hx)
          · rw [show start + multOf counts v - 1 + 1 - start =
              multOf counts v by omega, hchunkL, hchunkL']
            exact hGperm v
          · rw [show start + multOf counts v - 1 + 1 =
                start + multOf counts v by omega,
              show start + (cell2 + 1 - start) -
                (start + multOf counts v) =
                cell2 + 1 - start - multOf counts v by omega,
              hrestL, hrestL']
            exact flatMap_perm_of_pointwise vs fun u _ => hGperm u
        have hcell1 : start + multOf counts v ≤ cell2 →
            IsCell (windowStep level cell1 cell2 v start
              (start + multOf counts v) maxcell st).ptn level
              (start + multOf counts v)
              (cell2 + 1 - (start + multOf counts v)) := by
          intro _
          rw [hptn1]
          have hs := isCell_split_right
            (c := start + multOf counts v - 1) hcellS (by omega)
            (by omega) (by omega)
          rw [show start + multOf counts v - 1 + 1 =
            start + multOf counts v by omega,
            show start + (cell2 + 1 - start) -
              (start + multOf counts v) =
              cell2 + 1 - (start + multOf counts v) by omega] at hs
          exact hs
        refine windowScan_region_perm level cell1 cell2 counts gL gL'
          hGperm hGlen vs (start + multOf counts v) _ _ hcell1
          (by rw [hptn1, Array.size_set!]; exact hc2s)
          (by rw [hptn1]; exact hcp1)
          (by
            rw [show cell2 + 1 - (start + multOf counts v) =
              cell2 + 1 - start - multOf counts v by omega]
            exact hrestL)
          (by
            rw [show cell2 + 1 - (start + multOf counts v) =
              cell2 + 1 - start - multOf counts v by omega]
            exact hrestL')
      · rw [if_neg houtc] at hptn1
        have hend : start + multOf counts v = cell2 + 1 := by omega
        refine windowScan_region_perm level cell1 cell2 counts gL gL'
          hGperm hGlen vs (start + multOf counts v) _ _
          (fun hcon => absurd hcon (by omega))
          (by rw [hptn1]; exact hc2s)
          (by rw [hptn1]; exact hcp)
          ?_ ?_
        · rw [show cell2 + 1 - (start + multOf counts v) = 0 by omega,
            segN_zero]
          have := hrestL
          rw [show cell2 + 1 - start - multOf counts v = 0 by omega,
            segN_zero] at this
          exact this
        · rw [show cell2 + 1 - (start + multOf counts v) = 0 by omega,
            segN_zero]
          have := hrestL'
          rw [show cell2 + 1 - start - multOf counts v = 0 by omega,
            segN_zero] at this
          exact this
    · simp only [if_neg hm]
      have hgv : gL v = [] :=
        List.length_eq_zero_iff.mp (by rw [hGlen v]; omega)
      have hgv' : gL' v = [] :=
        List.length_eq_zero_iff.mp (by rw [hGlen' v]; omega)
      exact windowScan_region_perm level cell1 cell2 counts gL gL'
        hGperm hGlen vs start maxcell st hcellR hc2s hcp
        (by rw [hlayL, List.flatMap_cons, hgv, List.nil_append])
        (by rw [hlayL', List.flatMap_cons, hgv', List.nil_append])

end Hex.GraphIso.Nauty
