/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Refine
public import HexGraphIso.Nauty.Image

public section

/-!
Equivariance of the ported nauty refinement.

A `Renaming` of the vertices carries the graph rows to their images and
the labelling to its composition, and leaves every position-level datum —
`ptn`, `active`, cell boundaries, counts, and refinement codes —
literally unchanged. This file proves that invariant through each
explicit recursion of `Nauty.Refine`, culminating in `refine_map`: the
whole refinement commutes with a renaming. This is stage 1 of the
certificate plan in the library README.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- `g'` holds the `σ`-images of the rows of `g`, both bounded. -/
@[expose] def RowsMap (σ : Renaming n) (g g' : Array Nat) : Prop :=
  g.size = n ∧ g'.size = n ∧
    ∀ v, v < n → g'[σ v]! = image σ n g[v]!

/-- Every entry is a vertex. -/
@[expose] def LabOk (lab : Array Nat) (n : Nat) : Prop :=
  ∀ i, i < lab.size → lab[i]! < n

/-! # Array transport helpers -/

theorem getElem!_map_of_lt (f : Nat → Nat) (a : Array Nat) {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD,
    Array.getD]
  rw [dite_eq_left (by simpa using hi), dite_eq_left hi]
  simp

theorem map_set! (f : Nat → Nat) (a : Array Nat) (i : Nat) (x : Nat) :
    (a.set! i x).map f = (a.map f).set! i (f x) := by
  simp

theorem labOk_set! {lab : Array Nat} (h : LabOk lab n) {x : Nat}
    (hx : x < n) (i : Nat) : LabOk (lab.set! i x) n := by
  intro j hj
  rw [Array.size_set!] at hj
  rcases Decidable.em (i = j) with rfl | hne
  · rw [Array.getElem!_set!_self _ _ _ hj]
    exact hx
  · rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact h j hj

/-! # The two-pointer partition -/

/-- Map a renaming over a loop result. -/
def mapResult (σ : Renaming n) (r : Array Nat × Int × Int) :
    Array Nat × Int × Int :=
  (r.1.map σ.toFun, r.2.1, r.2.2)

theorem splitCellLoop_map (σ : Renaming n) {gRow : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      LabOk lab n → 0 ≤ c1 → c2 < (lab.size : Int) →
      splitCellLoop (image σ n gRow) fuel (lab.map σ.toFun) c1 c2 =
        mapResult σ (splitCellLoop gRow fuel lab c1 c2)
  | 0, lab, c1, c2, hlab, h1, h2 => rfl
  | fuel + 1, lab, c1, c2, hlab, h1, h2 => by
    rw [splitCellLoop, splitCellLoop]
    rcases Decidable.em (c1 ≤ c2) with hle | hgt
    · rw [ite_eq_left hle, ite_eq_left hle]
      have hc1 : c1.toNat < lab.size := by omega
      have hc2 : c2.toNat < lab.size := by omega
      rw [getElem!_map_of_lt _ _ hc1]
      have hlt : lab[c1.toNat]! < n := hlab _ hc1
      rw [show elem (image σ n gRow) (σ.toFun lab[c1.toNat]!)
          = elem gRow lab[c1.toNat]! from testBit_image_apply σ gRow hlt]
      rcases hadj : elem gRow lab[c1.toNat]! with _ | _
      · simp only [Bool.false_eq_true, ite_false]
        rw [getElem!_map_of_lt _ _ hc2, ← map_set!, ← map_set!]
        exact splitCellLoop_map σ fuel _ c1 (c2 - 1)
          (labOk_set! (labOk_set! hlab (hlab _ hc2) _) hlt _)
          h1 (by rw [Array.size_set!, Array.size_set!]; omega)
      · simp only [ite_true]
        exact splitCellLoop_map σ fuel lab (c1 + 1) c2 hlab (by omega) h2
    · rw [ite_eq_right hgt, ite_eq_right hgt]
      rfl

/-- The final labelling of the two-pointer partition keeps its size and
its entries in range. -/
theorem splitCellLoop_ok {gRow : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      LabOk lab n → 0 ≤ c1 → c2 < (lab.size : Int) →
      (splitCellLoop gRow fuel lab c1 c2).1.size = lab.size ∧
        LabOk (splitCellLoop gRow fuel lab c1 c2).1 n
  | 0, lab, c1, c2, hlab, _, _ => ⟨rfl, hlab⟩
  | fuel + 1, lab, c1, c2, hlab, h1, h2 => by
    rw [splitCellLoop]
    rcases Decidable.em (c1 ≤ c2) with hle | hgt
    · rw [ite_eq_left hle]
      have hc1 : c1.toNat < lab.size := by omega
      have hc2 : c2.toNat < lab.size := by omega
      rcases hadj : elem gRow lab[c1.toNat]! with _ | _
      · simp only [Bool.false_eq_true, ite_false]
        have ih := splitCellLoop_ok (gRow := gRow) fuel
          ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!)
          c1 (c2 - 1)
          (labOk_set! (labOk_set! hlab (hlab _ hc2) _) (hlab _ hc1) _)
          h1 (by rw [Array.size_set!, Array.size_set!]; omega)
        rw [Array.size_set!, Array.size_set!] at ih
        exact ih
      · simp only [ite_true]
        exact splitCellLoop_ok fuel lab (c1 + 1) c2 hlab (by omega) h2
    · rw [ite_eq_right hgt]
      exact ⟨rfl, hlab⟩

/-! # State transport -/

/-- Apply a renaming to the labelling of a refinement state; every
position-level field is untouched. -/
@[reducible, expose] def mapSt (σ : Renaming n) (st : RefineSt) : RefineSt :=
  { st with lab := st.lab.map σ.toFun }

/-- The split bookkeeping reads and writes only position-level fields,
so it commutes with the labelling transport. -/
theorem trivialSplit_mapSt (σ : Renaming n) (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt) :
    trivialSplit level cell1 cell2 c1 c2 (mapSt σ st) =
      mapSt σ (trivialSplit level cell1 cell2 c1 c2 st) := by
  rw [trivialSplit, trivialSplit]
  dsimp only [mapSt]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with hA | hA
  · simp only [ite_eq_left hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with hB | hB
    · simp only [ite_eq_left hB]
      rcases hC : (c1.toNat == cell2) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true]
    · simp only [ite_eq_right hB]
      rcases hD : (c2.toNat == cell1) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp only [ite_eq_right hA]

/-- The split bookkeeping leaves the labelling untouched. -/
theorem lab_trivialSplit (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).lab = st.lab := by
  rw [trivialSplit]
  split
  · split
    · split <;> rfl
    · split <;> rfl
  · rfl

/-- One trivial-splitter cell commutes with the labelling transport. -/
theorem trivialCell_map (σ : Renaming n) (level : Nat) {gRow : Nat}
    (cell1 cell2 : Nat) (st : RefineSt) (hlab : LabOk st.lab n)
    (h2 : cell2 < st.lab.size) :
    trivialCell level (image σ n gRow) cell1 cell2 (mapSt σ st) =
      mapSt σ (trivialCell level gRow cell1 cell2 st) := by
  rw [trivialCell, trivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    dsimp only [mapSt]
    rw [splitCellLoop_map σ (cell2 - cell1 + 2) st.lab (Int.ofNat cell1)
      (Int.ofNat cell2) hlab (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [Int.ofNat_eq_natCast]; omega)]
    dsimp only [mapResult]
    exact trivialSplit_mapSt σ level cell1 cell2 _ _
      { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1 }
  · simp only [ite_true]

/-- One trivial-splitter cell keeps the labelling's size and range. -/
theorem trivialCell_ok {level gRow cell1 cell2 : Nat} {st : RefineSt}
    (hlab : LabOk st.lab n) (h2 : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size ∧
      LabOk (trivialCell level gRow cell1 cell2 st).lab n := by
  rw [trivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    rw [lab_trivialSplit]
    exact splitCellLoop_ok (cell2 - cell1 + 2) st.lab (Int.ofNat cell1)
      (Int.ofNat cell2) hlab (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [Int.ofNat_eq_natCast]; omega)
  · simp only [ite_true]
    exact ⟨trivial, hlab⟩

/-! # Cell boundaries -/

/-- With the partition's final position closed at `level`, a cell end
found from an in-range start stays in range. -/
theorem cellEnd_go_lt {ptn : Array Nat} {level : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel j : Nat), j < ptn.size → ptn.size ≤ fuel + j →
      cellEnd.go ptn level fuel j < ptn.size
  | 0, j, hj, hf => absurd hf (by omega)
  | fuel + 1, j, hj, hf => by
    rw [cellEnd.go]
    split
    · next h =>
      have hne : j ≠ ptn.size - 1 := by
        intro hjeq
        rw [hjeq] at h
        omega
      exact cellEnd_go_lt hend fuel (j + 1) (by omega) (by omega)
    · exact hj

theorem cellEnd_lt {ptn : Array Nat} {level : Nat} {i : Nat}
    (hi : i < ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    cellEnd ptn level i < ptn.size := by
  rw [cellEnd]
  exact cellEnd_go_lt hend (ptn.size - i) i hi (by omega)

theorem cells_go_bound {ptn : Array Nat} {level nn : Nat}
    (hn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel c1 : Nat) (p : Nat × Nat),
      p ∈ cells.go ptn level nn fuel c1 → p.2 < ptn.size
  | 0, _, p, hp => absurd hp (by simp [cells.go])
  | fuel + 1, c1, p, hp => by
    rw [cells.go] at hp
    split at hp
    · next h =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · exact cellEnd_lt (by omega) hend
      · exact cells_go_bound hn hend fuel _ p hmem
    · exact absurd hp (by simp)

/-- Every cell end of the partition at `level` is an in-range
position. -/
theorem cells_bound {ptn : Array Nat} {level nn : Nat}
    (hn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ p ∈ cells ptn level nn, p.2 < ptn.size := by
  intro p hp
  rw [cells] at hp
  exact cells_go_bound hn hend nn 0 p hp

/-! # The trivial-splitter pass -/

theorem refineTrivial_go_map (σ : Renaming n) (level : Nat) {gRow : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt), LabOk st.lab n →
      (∀ p ∈ cs, p.2 < st.lab.size) →
      refineTrivial.go level (image σ n gRow) cs (mapSt σ st) =
        mapSt σ (refineTrivial.go level gRow cs st)
  | [], st, _, _ => rfl
  | (cell1, cell2) :: rest, st, hlab, hcs => by
    rw [refineTrivial.go, refineTrivial.go]
    rw [trivialCell_map σ level cell1 cell2 st hlab (hcs (cell1, cell2) (by simp))]
    exact refineTrivial_go_map σ level rest
      (trivialCell level gRow cell1 cell2 st)
      (trivialCell_ok hlab (hcs (cell1, cell2) (by simp))).2
      (fun p hp => by
        rw [(trivialCell_ok hlab (hcs (cell1, cell2) (by simp))).1]
        exact hcs p (List.mem_cons_of_mem _ hp))

/-- The trivial-splitter pass commutes with the labelling transport: on
the renamed graph with the transported labelling it produces the
transported state, with all position-level data unchanged. -/
theorem refineTrivial_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (level split1 : Nat) (st : RefineSt) (hlab : LabOk st.lab n)
    (hsl : st.lab.size = n) (hsp : st.ptn.size = n) (hs1 : split1 < n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    refineTrivial ctx' level split1 (mapSt σ st) =
      mapSt σ (refineTrivial ctx level split1 st) := by
  rw [refineTrivial, refineTrivial]
  rw [show (mapSt σ st).lab[split1]! = σ.toFun st.lab[split1]! from
      getElem!_map_of_lt σ.toFun st.lab (by omega),
    hg.2.2 st.lab[split1]! (hlab split1 (by omega)),
    show (mapSt σ st).ptn = st.ptn from rfl, hn', hn]
  exact refineTrivial_go_map σ level (cells st.ptn level n) st hlab
    (fun p hp => by
      have hb := cells_bound (nn := n) (by omega) hend p hp
      omega)

/-! # The nontrivial-splitter pass: splitter set and counts -/

theorem foldl_insert_map (σ : Renaming n) (lab : Array Nat)
    (hlab : LabOk lab n) (lo : Nat) :
    ∀ (l : List Nat) (w : Nat), (∀ o ∈ l, lo + o < lab.size) →
      l.foldl (fun w o => insert w (lab.map σ.toFun)[lo + o]!)
          (image σ n w) =
        image σ n (l.foldl (fun w o => insert w lab[lo + o]!) w)
  | [], _, _ => rfl
  | o :: l, w, hb => by
    rw [List.foldl_cons, List.foldl_cons,
      getElem!_map_of_lt σ.toFun lab (hb o (by simp)),
      ← image_insert σ w (hlab _ (hb o (by simp)))]
    exact foldl_insert_map σ lab hlab lo l (insert w lab[lo + o]!)
      (fun o' ho' => hb o' (by simp [ho']))

/-- The splitter cell's vertex set transports to its image. -/
theorem worksetOf_map (σ : Renaming n) {lab : Array Nat}
    (hlab : LabOk lab n) {lo hi : Nat} (hhi : hi < lab.size) :
    worksetOf (lab.map σ.toFun) lo hi = image σ n (worksetOf lab lo hi) := by
  rw [worksetOf, worksetOf]
  have h := foldl_insert_map σ lab hlab lo (List.range (hi + 1 - lo)) 0
    (fun o ho => by
      have := List.mem_range.mp ho
      omega)
  rw [image_zero] at h
  exact h

/-- The splitter cell's vertex set is a bounded vertex set. -/
theorem worksetOf_lt {lab : Array Nat} (hlab : LabOk lab n)
    {lo hi : Nat} (hhi : hi < lab.size) :
    worksetOf lab lo hi < 2 ^ n := by
  rw [worksetOf]
  have hgen : ∀ (l : List Nat) (w : Nat), (∀ o ∈ l, lo + o < lab.size) →
      w < 2 ^ n → l.foldl (fun w o => insert w lab[lo + o]!) w < 2 ^ n := by
    intro l
    induction l with
    | nil => exact fun w _ hw => hw
    | cons o l ih =>
      intro w hb hw
      rw [List.foldl_cons]
      exact ih _ (fun o' ho' => hb o' (by simp [ho']))
        (insert_lt hw (hlab _ (hb o (by simp))))
  exact hgen (List.range (hi + 1 - lo)) 0
    (fun o ho => by
      have := List.mem_range.mp ho
      omega)
    (Nat.two_pow_pos n)

/-- The neighbour counts into the splitter set are invariant under a
renaming of graph, labelling, and splitter set. -/
theorem countsOf_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g)
    {lab : Array Nat} (hlab : LabOk lab n) {workset : Nat}
    (hws : workset < 2 ^ n) {cell1 cell2 : Nat} (h2 : cell2 < lab.size) :
    countsOf ctx' (lab.map σ.toFun) (image σ n workset) cell1 cell2 =
      countsOf ctx lab workset cell1 cell2 := by
  rw [countsOf, countsOf]
  refine List.map_congr_left fun o ho => ?_
  have hoo := List.mem_range.mp ho
  have hpos : cell1 + o < lab.size := by omega
  rw [getElem!_map_of_lt σ.toFun lab hpos,
    hg.2.2 lab[cell1 + o]! (hlab _ hpos), ← image_and σ,
    popCount_image σ (Nat.lt_of_le_of_lt Nat.and_le_left hws) (image_lt σ _)]

/-! # The window scan -/

/-- The window-scan bookkeeping reads and writes only position-level
fields, so it commutes with the labelling transport. -/
theorem windowStep_mapSt (σ : Renaming n) (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt) :
    windowStep level cell1 cell2 v c1 c2 maxcell (mapSt σ st) =
      mapSt σ (windowStep level cell1 cell2 v c1 c2 maxcell st) := by
  rw [windowStep, windowStep]
  dsimp only [mapSt]
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

theorem lab_windowStep (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).lab = st.lab := by
  rw [windowStep]
  dsimp only
  repeat' first | rfl | split

theorem windowScan_map (σ : Renaming n) (level cell1 cell2 : Nat)
    (counts : List Nat) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      windowScan level cell1 cell2 counts values c1 maxcell (mapSt σ st) =
        mapSt σ (windowScan level cell1 cell2 counts values c1 maxcell st)
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScan, windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rw [windowStep_mapSt]
      exact windowScan_map σ level cell1 cell2 counts vs _ _ _
    · simp only [ite_eq_right hm]
      exact windowScan_map σ level cell1 cell2 counts vs c1 maxcell st

/-- The window scan touches no labelling data. -/
theorem lab_windowScan (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      (windowScan level cell1 cell2 counts values c1 maxcell st).lab =
        st.lab
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScan]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      rw [lab_windowScan level cell1 cell2 counts vs _ _ _, lab_windowStep]
    · simp only [ite_eq_right hm]
      exact lab_windowScan level cell1 cell2 counts vs c1 maxcell st

/-! # The stable counting redistribution -/

theorem countsOf_length (ctx : Ctx) (lab : Array Nat)
    (workset cell1 cell2 : Nat) :
    (countsOf ctx lab workset cell1 cell2).length = cell2 + 1 - cell1 := by
  rw [countsOf]
  simp

theorem segmentOf_map (σ : Renaming n) {lab : Array Nat} {cell1 : Nat}
    {counts : List Nat} (hlen : cell1 + counts.length ≤ lab.size)
    (values : List Nat) :
    segmentOf (lab.map σ.toFun) cell1 counts values =
      (segmentOf lab cell1 counts values).map σ.toFun := by
  rw [segmentOf, segmentOf, List.map_flatMap]
  refine congrArg values.flatMap ?_
  funext v
  rw [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  rcases p with ⟨c, j⟩
  have hz := (List.mem_filter.mp hp).1
  rw [List.mem_zipIdx_iff_getElem?] at hz
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hz
  exact getElem!_map_of_lt σ.toFun lab (by omega)

/-- Segment entries are labelling entries, hence vertices. -/
theorem segmentOf_mem {lab : Array Nat} (hlab : LabOk lab n) {cell1 : Nat}
    {counts : List Nat} (hlen : cell1 + counts.length ≤ lab.size)
    (values : List Nat) : ∀ x ∈ segmentOf lab cell1 counts values, x < n := by
  intro x hx
  rw [segmentOf, List.mem_flatMap] at hx
  rcases hx with ⟨v, hv, hx⟩
  rw [List.mem_map] at hx
  rcases hx with ⟨⟨c, j⟩, hp, rfl⟩
  have hz := (List.mem_filter.mp hp).1
  rw [List.mem_zipIdx_iff_getElem?] at hz
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hz
  exact hlab _ (by omega)

theorem writeSegment_map (σ : Renaming n) :
    ∀ (seg : List Nat) (lab : Array Nat) (c1 : Nat),
      writeSegment (lab.map σ.toFun) c1 (seg.map σ.toFun) =
        (writeSegment lab c1 seg).map σ.toFun
  | [], _, _ => rfl
  | x :: seg, lab, c1 => by
    rw [List.map_cons, writeSegment, writeSegment, ← map_set!]
    exact writeSegment_map σ seg (lab.set! c1 x) (c1 + 1)

theorem writeSegment_ok :
    ∀ (seg : List Nat) (lab : Array Nat) (c1 : Nat), LabOk lab n →
      (∀ x ∈ seg, x < n) →
      (writeSegment lab c1 seg).size = lab.size ∧
        LabOk (writeSegment lab c1 seg) n
  | [], _, _, hlab, _ => ⟨rfl, hlab⟩
  | x :: seg, lab, c1, hlab, hseg => by
    rw [writeSegment]
    have ih := writeSegment_ok seg (lab.set! c1 x) (c1 + 1)
      (labOk_set! hlab (hseg x (by simp)) c1)
      (fun y hy => hseg y (by simp [hy]))
    rw [Array.size_set!] at ih
    exact ih

/-! # The nontrivial-splitter cell -/

/-- The active-set fix reads and writes only position-level fields, so
it commutes with the labelling transport. -/
theorem nontrivialFix_mapSt (σ : Renaming n) (cell1 : Nat)
    (st : RefineSt) :
    nontrivialFix cell1 (mapSt σ st) = mapSt σ (nontrivialFix cell1 st) := by
  rw [nontrivialFix, nontrivialFix]
  dsimp only [mapSt]
  rcases Decidable.em (¬ elem st.active cell1 = true) with h | h
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem lab_nontrivialFix (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).lab = st.lab := by
  rw [nontrivialFix]
  split <;> rfl

/-- One nontrivial-splitter cell commutes with the labelling
transport. -/
theorem nontrivialCell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) (level : Nat) {workset : Nat}
    (hws : workset < 2 ^ n) (cell1 cell2 : Nat) (st : RefineSt)
    (hlab : LabOk st.lab n) (h2 : cell2 < st.lab.size) :
    nontrivialCell ctx' level (image σ n workset) cell1 cell2 (mapSt σ st) =
      mapSt σ (nontrivialCell ctx level workset cell1 cell2 st) := by
  rw [nontrivialCell, nontrivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    rw [countsOf_map σ hg hlab hws h2]
    have hlen : (countsOf ctx st.lab workset cell1 cell2).length =
        cell2 + 1 - cell1 := countsOf_length ctx st.lab workset cell1 cell2
    generalize hcounts : countsOf ctx st.lab workset cell1 cell2 = counts
    rw [hcounts] at hlen
    rcases hbm : (counts.foldl Nat.min (counts.headD 0) ==
        counts.foldl Nat.max (counts.headD 0)) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have hne : cell1 ≤ cell2 := by
        rcases Decidable.em (cell1 ≤ cell2) with h | h
        · exact h
        · have h0 : counts = [] := List.length_eq_zero_iff.mp (by omega)
          rw [h0] at hbm
          simp at hbm
      rw [windowScan_map σ level cell1 cell2 counts (st := st),
        show ∀ x : RefineSt, (mapSt σ x).lab = x.lab.map σ.toFun from
          fun _ => rfl,
        lab_windowScan level cell1 cell2 counts,
        segmentOf_map σ (lab := st.lab) (cell1 := cell1) (counts := counts)
          (by omega),
        writeSegment_map σ, ← nontrivialFix_mapSt σ cell1]
    · simp only [ite_true]
  · simp only [ite_true]

/-- One nontrivial-splitter cell keeps the labelling's size and
range. -/
theorem nontrivialCell_ok {ctx : Ctx} {level workset cell1 cell2 : Nat}
    {st : RefineSt} (hlab : LabOk st.lab n) (h2 : cell2 < st.lab.size) :
    (nontrivialCell ctx level workset cell1 cell2 st).lab.size =
        st.lab.size ∧
      LabOk (nontrivialCell ctx level workset cell1 cell2 st).lab n := by
  rw [nontrivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    have hlen : (countsOf ctx st.lab workset cell1 cell2).length =
        cell2 + 1 - cell1 := countsOf_length ctx st.lab workset cell1 cell2
    generalize hcounts : countsOf ctx st.lab workset cell1 cell2 = counts
    rw [hcounts] at hlen
    rcases hbm : (counts.foldl Nat.min (counts.headD 0) ==
        counts.foldl Nat.max (counts.headD 0)) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have hne : cell1 ≤ cell2 := by
        rcases Decidable.em (cell1 ≤ cell2) with h | h
        · exact h
        · have h0 : counts = [] := List.length_eq_zero_iff.mp (by omega)
          rw [h0] at hbm
          simp at hbm
      rw [lab_nontrivialFix, lab_windowScan level cell1 cell2 counts]
      exact writeSegment_ok _ st.lab cell1 hlab
        (segmentOf_mem hlab (by omega) _)
    · simp only [ite_true]
      exact ⟨by trivial, hlab⟩
  · simp only [ite_true]
    exact ⟨by trivial, hlab⟩

/-! # The refinement-state invariant -/

/-- The refinement-state invariant threaded through `refine`: labelling
and partition are `n`-sized, labelling entries and active positions are
in range, and the final partition position is closed at `level`. -/
structure StOk (n level : Nat) (st : RefineSt) : Prop where
  labSize : st.lab.size = n
  labOk : LabOk st.lab n
  ptnSize : st.ptn.size = n
  activeLt : st.active < 2 ^ n
  ptnEnd : st.ptn[st.ptn.size - 1]! ≤ level

/-- Setting a partition position to the current level keeps the final
position closed at that level. -/
theorem ptnEnd_set! {ptn : Array Nat} {level i : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    (ptn.set! i level)[(ptn.set! i level).size - 1]! ≤ level := by
  rw [Array.size_set!]
  rcases Decidable.em (i = ptn.size - 1) with heq | hne
  · subst heq
    rcases Nat.lt_or_ge (ptn.size - 1) ptn.size with hlt | hge
    · rw [Array.getElem!_set!_self _ _ _ hlt]
      exact Nat.le_refl level
    · rw [Array.getElem!_eq_getD, Array.getD,
        dite_eq_right (by rw [Array.size_set!]; omega)]
      exact Nat.zero_le level
  · rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact hend

/-- A splitter chosen from a bounded active set is a vertex. -/
theorem pickSplit_lt {active hint s : Nat} (ha : active < 2 ^ n) :
    pickSplit active hint = some s → s < n := by
  rw [pickSplit]
  split
  · next h =>
    intro he
    injection he with he
    subst he
    exact lt_of_testBit_of_lt ha h
  · intro he
    rcases hne : nextElem active (some hint) with _ | v
    · rw [hne] at he
      dsimp only at he
      exact lt_of_testBit_of_lt ha (nextElem_mem he)
    · rw [hne] at he
      dsimp only at he
      injection he with he
      subst he
      exact lt_of_testBit_of_lt ha (nextElem_mem hne)

theorem trivialSplit_stOk {level cell1 cell2 : Nat} {c1 c2 : Int}
    {st : RefineSt} (h : StOk n level st) (h1 : cell1 < n) (h2 : cell2 < n) :
    StOk n level (trivialSplit level cell1 cell2 c1 c2 st) := by
  obtain ⟨hsl, hlab, hsp, hact, hend⟩ := h
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with hA | hA
  · have hA2 : c1.toNat ≤ cell2 := by
      have := hA.2
      simp only [Int.ofNat_eq_natCast] at this
      omega
    simp only [ite_eq_left hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with hB | hB
    · simp only [ite_eq_left hB]
      rcases hC : (c1.toNat == cell2) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        exact ⟨hsl, hlab, by rw [Array.size_set!]; exact hsp,
          insert_lt hact (by omega), ptnEnd_set! hend⟩
    · simp only [ite_eq_right hB]
      rcases hD : (c2.toNat == cell1) with _ | _ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        exact ⟨hsl, hlab, by rw [Array.size_set!]; exact hsp,
          insert_lt hact h1, ptnEnd_set! hend⟩
  · simp only [ite_eq_right hA]
    exact ⟨hsl, hlab, hsp, hact, hend⟩

theorem trivialCell_stOk {level gRow cell1 cell2 : Nat} {st : RefineSt}
    (h : StOk n level st) (h1 : cell1 < n) (h2 : cell2 < n) :
    StOk n level (trivialCell level gRow cell1 cell2 st) := by
  rw [trivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    have hsplit := splitCellLoop_ok (gRow := gRow) (cell2 - cell1 + 2) st.lab
      (Int.ofNat cell1) (Int.ofNat cell2) h.labOk
      (by simp only [Int.ofNat_eq_natCast]; omega)
      (by
        simp only [Int.ofNat_eq_natCast]
        have := h.labSize
        omega)
    exact trivialSplit_stOk
      ⟨hsplit.1.trans h.labSize, hsplit.2, h.ptnSize, h.activeLt, h.ptnEnd⟩
      h1 h2
  · simp only [ite_true]
    exact h

/-! # Multiplicity sums -/

theorem multOf_cons (x : Nat) (counts : List Nat) (v : Nat) :
    multOf (x :: counts) v = multOf counts v + if x == v then 1 else 0 := by
  rw [multOf, multOf, List.countP_cons]

theorem sum_map_add (f g : Nat → Nat) :
    ∀ l : List Nat,
      (l.map fun v => f v + g v).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons, List.sum_cons, sum_map_add f g l]
    omega

theorem sum_map_ite_zero {x : Nat} :
    ∀ {l : List Nat}, x ∉ l →
      (l.map fun v => if x == v then 1 else 0).sum = 0
  | [], _ => rfl
  | b :: l, h => by
    rw [List.map_cons, List.sum_cons]
    have hxb : (x == b) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      subst he
      exact h (by simp)
    rw [hxb]
    simp only [Bool.false_eq_true, ite_false]
    rw [sum_map_ite_zero (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem sum_map_ite_le {x : Nat} :
    ∀ {l : List Nat}, l.Nodup →
      (l.map fun v => if x == v then 1 else 0).sum ≤ 1
  | [], _ => by simp
  | a :: l, hnd => by
    rw [List.map_cons, List.sum_cons]
    rcases hax : (x == a) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have := sum_map_ite_le (x := x) (List.nodup_cons.mp hnd).2
      omega
    · simp only [ite_true]
      have hx : x = a := by simpa using hax
      subst hx
      rw [sum_map_ite_zero (List.nodup_cons.mp hnd).1]
      omega

theorem sum_map_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.sum_cons, sum_map_zero l]

/-- Over distinct count values, the group multiplicities sum to at most
the cell size. -/
theorem sum_multOf_le {l : List Nat} (hl : l.Nodup) :
    ∀ counts : List Nat, (l.map (multOf counts)).sum ≤ counts.length
  | [] => by
    have h0 : l.map (multOf []) = l.map fun _ => 0 :=
      List.map_congr_left fun v _ => by rw [multOf]; rfl
    rw [h0, sum_map_zero]
    exact Nat.zero_le _
  | x :: counts => by
    have hstep : l.map (multOf (x :: counts)) =
        l.map fun v => multOf counts v + if x == v then 1 else 0 :=
      List.map_congr_left fun v _ => multOf_cons x counts v
    rw [hstep, sum_map_add, List.length_cons]
    have h1 := sum_map_ite_le (x := x) hl
    have h2 := sum_multOf_le hl counts
    omega

/-! # Window-scan state invariance -/

theorem active_windowStep (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).active = st.active ∨
      (windowStep level cell1 cell2 v c1 c2 maxcell st).active =
        insert st.active c1 := by
  rw [windowStep]
  dsimp only
  repeat' first | exact Or.inl rfl | exact Or.inr rfl | split

theorem ptn_windowStep (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).ptn = st.ptn ∨
      (windowStep level cell1 cell2 v c1 c2 maxcell st).ptn =
        st.ptn.set! (c2 - 1) level := by
  rw [windowStep]
  dsimp only
  repeat' first | exact Or.inl rfl | exact Or.inr rfl | split

theorem windowStep_stOk {level cell1 cell2 v c1 c2 : Nat} {maxcell : Int}
    {st : RefineSt} (h : StOk n level st) (hc1 : c1 < n) :
    StOk n level (windowStep level cell1 cell2 v c1 c2 maxcell st) := by
  obtain ⟨hsl, hlab, hsp, hact, hend⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lab_windowStep]
    exact hsl
  · rw [lab_windowStep]
    exact hlab
  · rcases ptn_windowStep level cell1 cell2 v c1 c2 maxcell st with hp | hp <;>
      rw [hp]
    · exact hsp
    · rw [Array.size_set!]
      exact hsp
  · rcases active_windowStep level cell1 cell2 v c1 c2 maxcell st with
      ha | ha <;> rw [ha]
    · exact hact
    · exact insert_lt hact hc1
  · rcases ptn_windowStep level cell1 cell2 v c1 c2 maxcell st with hp | hp <;>
      rw [hp]
    · exact hend
    · exact ptnEnd_set! hend

theorem windowScan_stOk {level cell1 cell2 : Nat} {counts : List Nat}
    (hc2 : cell2 < n) :
    ∀ (values : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      StOk n level st →
      c1 + (values.map (multOf counts)).sum ≤ cell2 + 1 →
      StOk n level (windowScan level cell1 cell2 counts values c1 maxcell st)
  | [], _, _, _, h, _ => h
  | v :: vs, c1, maxcell, st, h, hsum => by
    rw [windowScan]
    have hsplit : (List.map (multOf counts) (v :: vs)).sum =
        multOf counts v + (vs.map (multOf counts)).sum := by
      rw [List.map_cons, List.sum_cons]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · simp only [ite_eq_left hm]
      exact windowScan_stOk hc2 vs (c1 + multOf counts v) _ _
        (windowStep_stOk h (by omega)) (by omega)
    · simp only [ite_eq_right hm]
      exact windowScan_stOk hc2 vs c1 maxcell st h (by omega)

theorem nontrivialFix_stOk {level cell1 : Nat} {st : RefineSt}
    (h : StOk n level st) (h1 : cell1 < n) :
    StOk n level (nontrivialFix cell1 st) := by
  rw [nontrivialFix]
  split
  · exact ⟨h.labSize, h.labOk, h.ptnSize,
      erase_lt (insert_lt h.activeLt h1), h.ptnEnd⟩
  · exact h

theorem nodup_range_map_add (b k : Nat) :
    ((List.range k).map fun x => b + x).Nodup := by
  refine List.Pairwise.map _ ?_ List.pairwise_lt_range
  intro a₁ a₂ hlt
  omega

theorem nontrivialCell_stOk {ctx : Ctx} {level workset cell1 cell2 : Nat}
    {st : RefineSt} (h : StOk n level st) (h1 : cell1 < n) (h2 : cell2 < n) :
    StOk n level (nontrivialCell ctx level workset cell1 cell2 st) := by
  rw [nontrivialCell]
  rcases hc : (cell1 == cell2) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    have hlen : (countsOf ctx st.lab workset cell1 cell2).length =
        cell2 + 1 - cell1 := countsOf_length ctx st.lab workset cell1 cell2
    generalize hcounts : countsOf ctx st.lab workset cell1 cell2 = counts
    rw [hcounts] at hlen
    rcases hbm : (counts.foldl Nat.min (counts.headD 0) ==
        counts.foldl Nat.max (counts.headD 0)) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have hne : cell1 ≤ cell2 := by
        rcases Decidable.em (cell1 ≤ cell2) with hle | hgt
        · exact hle
        · have h0 : counts = [] := List.length_eq_zero_iff.mp (by omega)
          rw [h0] at hbm
          simp at hbm
      have hnd : (countValues counts).Nodup := by
        rw [countValues]
        exact nodup_range_map_add _ _
      have hsum := sum_multOf_le hnd counts
      have hlsz := h.labSize
      have hW := windowScan_stOk (level := level) (cell1 := cell1)
        (counts := counts) h2 (countValues counts) cell1 (-1) st h
        (by omega)
      rw [lab_windowScan level cell1 cell2 counts]
      have hws := writeSegment_ok
        (segmentOf st.lab cell1 counts (countValues counts))
        st.lab cell1 h.labOk
        (segmentOf_mem (cell1 := cell1) (counts := counts) h.labOk
          (by omega) (countValues counts))
      exact nontrivialFix_stOk
        ⟨hws.1.trans h.labSize, hws.2, hW.ptnSize, hW.activeLt, hW.ptnEnd⟩ h1
    · simp only [ite_true]
      exact ⟨h.labSize, h.labOk, h.ptnSize, h.activeLt, h.ptnEnd⟩
  · simp only [ite_true]
    exact h

/-! # Cell starts -/

theorem cellEnd_go_ge {ptn : Array Nat} {level : Nat} :
    ∀ (fuel j : Nat), j ≤ cellEnd.go ptn level fuel j
  | 0, j => Nat.le_refl j
  | fuel + 1, j => by
    rw [cellEnd.go]
    split
    · have := cellEnd_go_ge (ptn := ptn) (level := level) fuel (j + 1)
      omega
    · exact Nat.le_refl j

theorem cellEnd_ge {ptn : Array Nat} {level i : Nat} :
    i ≤ cellEnd ptn level i := by
  rw [cellEnd]
  exact cellEnd_go_ge _ _

theorem cells_go_le {ptn : Array Nat} {level nn : Nat} :
    ∀ (fuel c1 : Nat) (p : Nat × Nat),
      p ∈ cells.go ptn level nn fuel c1 → p.1 ≤ p.2
  | 0, _, p, hp => absurd hp (by simp [cells.go])
  | fuel + 1, c1, p, hp => by
    rw [cells.go] at hp
    split at hp
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · exact cellEnd_ge
      · exact cells_go_le fuel _ p hmem
    · exact absurd hp (by simp)

/-- Every cell of the partition starts no later than it ends. -/
theorem cells_le {ptn : Array Nat} {level nn : Nat} :
    ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 := by
  intro p hp
  rw [cells] at hp
  exact cells_go_le nn 0 p hp

/-! # Splitting passes: state invariance -/

theorem refineTrivial_go_stOk {level gRow : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt), StOk n level st →
      (∀ p ∈ cs, p.1 < n ∧ p.2 < n) →
      StOk n level (refineTrivial.go level gRow cs st)
  | [], _, h, _ => h
  | (c1, c2) :: rest, st, h, hcs => by
    rw [refineTrivial.go]
    exact refineTrivial_go_stOk rest _
      (trivialCell_stOk h (hcs (c1, c2) (by simp)).1 (hcs (c1, c2) (by simp)).2)
      (fun p hp => hcs p (List.mem_cons_of_mem _ hp))

theorem refineTrivial_stOk {ctx : Ctx} {level split1 : Nat} {st : RefineSt}
    (hn : ctx.n = n) (h : StOk n level st) :
    StOk n level (refineTrivial ctx level split1 st) := by
  rw [refineTrivial]
  refine refineTrivial_go_stOk _ _ h fun p hp => ?_
  have hb := cells_bound (nn := ctx.n)
    (by have := h.ptnSize; omega) h.ptnEnd p hp
  have hl := cells_le p hp
  have := h.ptnSize
  omega

theorem refineNontrivial_go_stOk {ctx : Ctx} {level workset : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt), StOk n level st →
      (∀ p ∈ cs, p.1 < n ∧ p.2 < n) →
      StOk n level (refineNontrivial.go ctx level workset cs st)
  | [], _, h, _ => h
  | (c1, c2) :: rest, st, h, hcs => by
    rw [refineNontrivial.go]
    exact refineNontrivial_go_stOk rest _
      (nontrivialCell_stOk h (hcs (c1, c2) (by simp)).1
        (hcs (c1, c2) (by simp)).2)
      (fun p hp => hcs p (List.mem_cons_of_mem _ hp))

theorem refineNontrivial_stOk {ctx : Ctx} {level split1 split2 : Nat}
    {st : RefineSt} (hn : ctx.n = n) (h : StOk n level st) :
    StOk n level (refineNontrivial ctx level split1 split2 st) := by
  rw [refineNontrivial]
  dsimp only
  refine refineNontrivial_go_stOk _ _
    ⟨h.labSize, h.labOk, h.ptnSize, h.activeLt, h.ptnEnd⟩ fun p hp => ?_
  have hb := cells_bound (nn := ctx.n)
    (by have := h.ptnSize; omega) h.ptnEnd p hp
  have hl := cells_le p hp
  have := h.ptnSize
  omega

/-! # The nontrivial pass commutes with the transport -/

theorem refineNontrivial_go_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) (level : Nat) {workset : Nat}
    (hws : workset < 2 ^ n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt), LabOk st.lab n →
      (∀ p ∈ cs, p.2 < st.lab.size) →
      refineNontrivial.go ctx' level (image σ n workset) cs (mapSt σ st) =
        mapSt σ (refineNontrivial.go ctx level workset cs st)
  | [], _, _, _ => rfl
  | (cell1, cell2) :: rest, st, hlab, hcs => by
    rw [refineNontrivial.go, refineNontrivial.go]
    rw [nontrivialCell_map σ hg level hws cell1 cell2 st hlab
      (hcs (cell1, cell2) (by simp))]
    exact refineNontrivial_go_map σ hg level hws rest
      (nontrivialCell ctx level workset cell1 cell2 st)
      (nontrivialCell_ok (ctx := ctx) hlab (hcs (cell1, cell2) (by simp))).2
      (fun p hp => by
        rw [(nontrivialCell_ok (ctx := ctx) (level := level)
          (workset := workset) hlab (hcs (cell1, cell2) (by simp))).1]
        exact hcs p (List.mem_cons_of_mem _ hp))

/-- The nontrivial-splitter pass commutes with the labelling
transport. -/
theorem refineNontrivial_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (level split1 split2 : Nat) (st : RefineSt) (h : StOk n level st)
    (hs2 : split2 < n) :
    refineNontrivial ctx' level split1 split2 (mapSt σ st) =
      mapSt σ (refineNontrivial ctx level split1 split2 st) := by
  rw [refineNontrivial, refineNontrivial]
  dsimp only
  rw [worksetOf_map σ h.labOk (lo := split1) (hi := split2)
      (by have := h.labSize; omega), hn', hn]
  exact refineNontrivial_go_map σ hg level
    (worksetOf_lt h.labOk (lo := split1) (hi := split2)
      (by have := h.labSize; omega))
    (cells st.ptn level n)
    { st with longcode := mash st.longcode (split2 - split1 + 1) }
    h.labOk
    (fun p hp =>
      (show p.2 < st.lab.size by
        have hb := cells_bound (nn := n)
          (by have := h.ptnSize; omega) h.ptnEnd p hp
        have := h.ptnSize
        have := h.labSize
        omega))

/-! # Step, loop, and `refine` -/

theorem refineStep_stOk {ctx : Ctx} {level split1 : Nat} {st : RefineSt}
    (hn : ctx.n = n) (h : StOk n level st) :
    StOk n level (refineStep ctx level split1 st) := by
  rw [refineStep]
  dsimp only
  split
  · exact refineTrivial_stOk hn
      ⟨h.labSize, h.labOk, h.ptnSize, erase_lt h.activeLt, h.ptnEnd⟩
  · exact refineNontrivial_stOk hn
      ⟨h.labSize, h.labOk, h.ptnSize, erase_lt h.activeLt, h.ptnEnd⟩

/-- One active-cell iteration commutes with the labelling transport. -/
theorem refineStep_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (level split1 : Nat) (st : RefineSt) (h : StOk n level st)
    (hs1 : split1 < n) :
    refineStep ctx' level split1 (mapSt σ st) =
      mapSt σ (refineStep ctx level split1 st) := by
  rw [refineStep, refineStep]
  dsimp only
  rw [show (mapSt σ st).active = st.active from rfl,
    show (mapSt σ st).ptn = st.ptn from rfl,
    show (mapSt σ st).longcode = st.longcode from rfl]
  have hstep : StOk n level
      { st with
        active := erase st.active split1
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) } :=
    ⟨h.labSize, h.labOk, h.ptnSize, erase_lt h.activeLt, h.ptnEnd⟩
  rcases hsp12 : (split1 == cellEnd st.ptn level split1) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    exact refineNontrivial_map σ hn hn' hg level split1
      (cellEnd st.ptn level split1) _ hstep
      (by
        have := cellEnd_lt (ptn := st.ptn) (level := level) (i := split1)
          (by have := h.ptnSize; omega) h.ptnEnd
        have := h.ptnSize
        omega)
  · simp only [ite_true]
    exact refineTrivial_map σ hn hn' hg level split1
      { st with
        active := erase st.active split1
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) }
      h.labOk h.labSize h.ptnSize hs1 h.ptnEnd

theorem refineLoop_stOk {ctx : Ctx} {level : Nat} (hn : ctx.n = n) :
    ∀ (fuel : Nat) (st : RefineSt), StOk n level st →
      StOk n level (refineLoop ctx level fuel st)
  | 0, _, h => h
  | fuel + 1, st, h => by
    rw [refineLoop]
    split
    · rcases hps : pickSplit st.active st.hint with _ | s
      · exact h
      · exact refineLoop_stOk hn fuel _ (refineStep_stOk hn h)
    · exact h

/-- The active-cell loop commutes with the labelling transport. -/
theorem refineLoop_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (level : Nat) :
    ∀ (fuel : Nat) (st : RefineSt), StOk n level st →
      refineLoop ctx' level fuel (mapSt σ st) =
        mapSt σ (refineLoop ctx level fuel st)
  | 0, _, _ => rfl
  | fuel + 1, st, h => by
    rw [refineLoop, refineLoop]
    rw [show (mapSt σ st).numcells = st.numcells from rfl,
      show (mapSt σ st).active = st.active from rfl,
      show (mapSt σ st).hint = st.hint from rfl, hn', hn]
    rcases Decidable.em (st.numcells < n) with hlt | hlt
    · simp only [ite_eq_left hlt]
      rcases hps : pickSplit st.active st.hint with _ | s
      · rfl
      · dsimp only
        rw [refineStep_map σ hn hn' hg level s st h
          (pickSplit_lt h.activeLt hps)]
        exact refineLoop_map σ hn hn' hg level fuel _ (refineStep_stOk hn h)
    · simp only [ite_eq_right hlt]

/-- nauty's `refine` commutes with a vertex renaming: on the renamed
graph with the transported labelling it produces the transported state,
with identical partition, active set, cell structure, and refinement
code. This is the core of stage 1 of the certificate plan. -/
theorem refine_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (level : Nat) (lab ptn : Array Nat) (active numcells : Nat)
    (hsl : lab.size = n) (hlab : LabOk lab n) (hsp : ptn.size = n)
    (hact : active < 2 ^ n) (hend : ptn[ptn.size - 1]! ≤ level) :
    refine ctx' level (lab.map σ.toFun) ptn active numcells =
      mapSt σ (refine ctx level lab ptn active numcells) := by
  rw [refine, refine]
  rw [hn', hn]
  rw [refineLoop_map σ hn hn' hg level (4 * n + 8)
    { lab, ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells }
    ⟨hsl, hlab, hsp, hact, hend⟩]

/-! # Target-cell selection -/

theorem bestcellRow_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) {lab startArr : Array Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n)
    (hstart : ∀ v : Nat, startArr[v]! < n) {workset : Nat}
    (hws : workset < 2 ^ n) (v2 : Nat) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      bestcellRow ctx' (lab.map σ.toFun) startArr (image σ n workset) v2 vs
          bucket =
        bestcellRow ctx lab startArr workset v2 vs bucket
  | [], _ => rfl
  | v1 :: rest, bucket => by
    rw [bestcellRow, bestcellRow]
    rw [getElem!_map_of_lt σ.toFun lab (by have := hstart v1; omega),
      hg.2.2 lab[startArr[v1]!]! (hlab _ (by have := hstart v1; omega)),
      ← image_and σ]
    have hand : workset &&& ctx.g[lab[startArr[v1]!]!]! < 2 ^ n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hws
    have h1 : (image σ n (workset &&& ctx.g[lab[startArr[v1]!]!]!) != 0) =
        (workset &&& ctx.g[lab[startArr[v1]!]!]! != 0) := by
      rcases Decidable.em (workset &&& ctx.g[lab[startArr[v1]!]!]! = 0) with
        hz | hz
      · rw [hz, image_zero]
      · have hnz : image σ n (workset &&& ctx.g[lab[startArr[v1]!]!]!) ≠ 0 :=
          fun he => hz ((image_eq_zero_iff σ hand).mp he)
        rw [Bool.eq_iff_iff]
        simp [hz, hnz]
    have h2 : (image σ n workset !=
        image σ n (workset &&& ctx.g[lab[startArr[v1]!]!]!)) =
        (workset != workset &&& ctx.g[lab[startArr[v1]!]!]!) := by
      rcases Decidable.em (workset = workset &&& ctx.g[lab[startArr[v1]!]!]!)
        with he | he
      · rw [← he]
        simp
      · have hne : image σ n workset ≠
            image σ n (workset &&& ctx.g[lab[startArr[v1]!]!]!) :=
          fun hh => he (image_inj σ hws hand hh)
        rw [Bool.eq_iff_iff]
        simp [he, hne]
    rw [h1, h2]
    rcases Decidable.em ((workset &&& ctx.g[lab[startArr[v1]!]!]! != 0) = true ∧
        (workset != workset &&& ctx.g[lab[startArr[v1]!]!]!) = true) with
      hc | hc
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact bestcellRow_map σ hg hlab hsl hstart hws v2 rest _
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact bestcellRow_map σ hg hlab hsl hstart hws v2 rest bucket

theorem bestcellRows_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hg : RowsMap σ ctx.g ctx'.g) {lab ptn : Array Nat} {level : Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) {startArr : Array Nat}
    (hstart : ∀ v : Nat, startArr[v]! < n) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      bestcellRows ctx' (lab.map σ.toFun) ptn level startArr vs bucket =
        bestcellRows ctx lab ptn level startArr vs bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [bestcellRows, bestcellRows]
    have hce : cellEnd ptn level startArr[v2]! < n := by
      have := cellEnd_lt (ptn := ptn) (level := level) (i := startArr[v2]!)
        (by have := hstart v2; omega) hend
      omega
    rw [worksetOf_map σ hlab (lo := startArr[v2]!)
      (hi := cellEnd ptn level startArr[v2]!) (by omega)]
    rw [bestcellRow_map σ hg hlab hsl hstart
      (worksetOf_lt hlab (lo := startArr[v2]!)
        (hi := cellEnd ptn level startArr[v2]!) (by omega)) v2 (List.range v2)
      bucket]
    exact bestcellRows_map σ hg hlab hsl hsp hend hstart rest _

theorem getElem!_list_lt {l : List Nat} {m : Nat} (hml : ∀ x ∈ l, x < m)
    (hm0 : 0 < m) (v : Nat) : l.toArray[v]! < m := by
  rw [List.getElem!_toArray]
  rcases Nat.lt_or_ge v l.length with hv | hv
  · rw [getElem!_pos l v hv]
    exact hml _ (List.getElem_mem hv)
  · rw [getElem!_neg l v (by omega)]
    exact hm0

/-- nauty's `bestcell` is position-valued and invariant under a
renaming. -/
theorem bestcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level : Nat} (hend : ptn[ptn.size - 1]! ≤ level) :
    bestcell ctx' (lab.map σ.toFun) ptn level = bestcell ctx lab ptn level := by
  rw [bestcell, bestcell]
  dsimp only
  rw [hn', hn]
  have hml : ∀ x ∈ ((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map
      (·.1), x < n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hpc := List.mem_filter.mp hp
    have hb := cells_bound (nn := n) (by omega) hend p hpc.1
    have hle := cells_le p hpc.1
    omega
  rcases hnnt : ((((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map
      (·.1)).length == 0) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    have hlen0 : (((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map
        (·.1)).length ≠ 0 := by
      simpa using hnnt
    have hn0 : 0 < n := by
      have hpos : 0 < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length :=
        Nat.pos_of_ne_zero hlen0
      exact Nat.lt_of_le_of_lt (Nat.zero_le _)
        (hml _ (List.getElem_mem hpos))
    rw [bestcellRows_map σ hg hlab hsl hsp hend
      (getElem!_list_lt hml hn0)]
  · simp only [ite_true]

/-- nauty's `targetcell` is position-valued and invariant under a
renaming. -/
theorem targetcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level tcLevel : Nat} {hint : Int}
    (hend : ptn[ptn.size - 1]! ≤ level) :
    targetcell ctx' (lab.map σ.toFun) ptn level tcLevel hint =
      targetcell ctx lab ptn level tcLevel hint := by
  rw [targetcell, targetcell]
  rcases Decidable.em (hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      (hint == 0 ∨ ptn[hint.toNat - 1]! ≤ level)) with hA | hA
  · rw [ite_eq_left hA, ite_eq_left hA]
  · rw [ite_eq_right hA, ite_eq_right hA]
    rcases Decidable.em (level ≤ tcLevel) with hB | hB
    · rw [ite_eq_left hB, ite_eq_left hB]
      exact bestcell_map σ hn hn' hg hlab hsl hsp hend
    · rw [ite_eq_right hB, ite_eq_right hB, hn', hn]

/-- nauty's `maketargetcell` transports position and size unchanged and
the target-cell set to its image. -/
theorem maketargetcell_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab ptn : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n)
    (hsp : ptn.size = n) {level tcLevel : Nat} {hint : Int}
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hi : targetcell ctx lab ptn level tcLevel hint + 1 < n) :
    maketargetcell ctx' (lab.map σ.toFun) ptn level tcLevel hint =
      ((maketargetcell ctx lab ptn level tcLevel hint).1,
        image σ n (maketargetcell ctx lab ptn level tcLevel hint).2.1,
        (maketargetcell ctx lab ptn level tcLevel hint).2.2) := by
  rw [maketargetcell, maketargetcell]
  rw [targetcell_map σ hn hn' hg hlab hsl hsp hend]
  have hce : cellEnd ptn level (targetcell ctx lab ptn level tcLevel hint + 1)
      < n := by
    have := cellEnd_lt (ptn := ptn) (level := level)
      (i := targetcell ctx lab ptn level tcLevel hint + 1) (by omega) hend
    omega
  rw [worksetOf_map σ hlab
    (lo := targetcell ctx lab ptn level tcLevel hint)
    (hi := cellEnd ptn level (targetcell ctx lab ptn level tcLevel hint + 1))
    (by omega)]

/-! # Individualization -/

theorem breakout_go_map (σ : Renaming n) {tv : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev : Nat), LabOk lab n →
      prev < n →
      (∃ k, i ≤ k ∧ k < lab.size ∧ lab[k]! = tv) →
      breakout.go (σ.toFun tv) fuel (lab.map σ.toFun) i (σ.toFun prev) =
        (breakout.go tv fuel lab i prev).map σ.toFun
  | 0, lab, i, prev, _, _, _ => rfl
  | fuel + 1, lab, i, prev, hlab, hprev, ⟨k, hik, hks, hkv⟩ => by
    rw [breakout.go, breakout.go]
    have hi : i < lab.size := by omega
    rw [getElem!_map_of_lt σ.toFun lab hi, ← map_set!]
    have hbeq : (σ.toFun lab[i]! == σ.toFun tv) = (lab[i]! == tv) := by
      rcases Decidable.em (lab[i]! = tv) with he | he
      · simp [he]
      · have hne : σ.toFun lab[i]! ≠ σ.toFun tv := fun hh => he (σ.inj _ _ hh)
        rw [Bool.eq_iff_iff]
        simp [he, hne]
    rw [hbeq]
    rcases hcase : (lab[i]! == tv) with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have hkne : k ≠ i := by
        intro hh
        subst hh
        simp only [beq_eq_false_iff_ne, ne_eq] at hcase
        exact hcase hkv
      exact breakout_go_map σ fuel (lab.set! i prev) (i + 1) lab[i]!
        (labOk_set! hlab hprev i) (hlab i hi)
        ⟨k, by omega, by rw [Array.size_set!]; omega,
          by rw [Array.getElem!_set!_ne _ _ _ _ (fun hh => hkne hh.symm)]
             exact hkv⟩
    · simp only [ite_true]

/-- nauty's `breakout` commutes with a renaming: the labelling maps
through, the partition and active set are position-level. -/
theorem breakout_map (σ : Renaming n) {lab ptn : Array Nat}
    {level tc tv : Nat} (hlab : LabOk lab n)
    (hwit : ∃ k, tc ≤ k ∧ k < lab.size ∧ lab[k]! = tv) :
    breakout (lab.map σ.toFun) ptn level tc (σ.toFun tv) =
      ((breakout lab ptn level tc tv).1.map σ.toFun,
        (breakout lab ptn level tc tv).2.1,
        (breakout lab ptn level tc tv).2.2) := by
  rw [breakout, breakout]
  dsimp only
  rw [Array.size_map]
  rw [breakout_go_map σ (lab.size + 1) lab tc tv hlab
    (by
      rcases hwit with ⟨k, _, hks, hkv⟩
      rw [← hkv]
      exact hlab k hks)
    hwit]

/-! # Leaf keys -/

theorem getElem!_replicate_zero (sz i : Nat) :
    (Array.replicate sz (0 : Nat))[i]! = 0 := by
  rcases Nat.lt_or_ge i sz with hi | hi
  · rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi)]
    simp
  · rw [getElem!_neg _ _ (by rw [Array.size_replicate]; omega)]
    rfl

theorem invPerm_go_map (σ : Renaming n) {lab : Array Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n) :
    ∀ (is : List Nat) (inv inv' : Array Nat), inv'.size = n →
      inv.size = n →
      (∀ v, v < n → inv'[σ.toFun v]! = inv[v]!) →
      (∀ i ∈ is, i < lab.size) →
      ∀ v, v < n →
        (invPerm.go (lab.map σ.toFun) is inv')[σ.toFun v]! =
          (invPerm.go lab is inv)[v]!
  | [], _, _, _, _, hrel, _, v, hv => hrel v hv
  | i :: rest, inv, inv', hsz, hsz2, hrel, his, v, hv => by
    rw [invPerm.go, invPerm.go]
    have hib : i < lab.size := his i (by simp)
    rw [getElem!_map_of_lt σ.toFun lab hib]
    refine invPerm_go_map σ hlab hsl rest (inv.set! lab[i]! i)
      (inv'.set! (σ.toFun lab[i]!) i) (by rw [Array.size_set!]; exact hsz)
      (by rw [Array.size_set!]; exact hsz2)
      (fun u hu => ?_) (fun j hj => his j (by simp [hj])) v hv
    rcases Decidable.em (lab[i]! = u) with he | he
    · rw [he, Array.getElem!_set!_self _ _ _
        (by rw [hsz]; exact (σ.maps u).mp hu),
        Array.getElem!_set!_self _ _ _
          (by rw [hsz2, ← he]; exact hlab i hib)]
    · rw [Array.getElem!_set!_ne _ _ _ _
        (fun hh => he (σ.inj _ _ hh)),
        Array.getElem!_set!_ne _ _ _ _ he]
      exact hrel u hu

/-- The labelling inverse transports along a renaming. -/
theorem invPerm_map (σ : Renaming n) {lab : Array Nat}
    (hlab : LabOk lab n) (hsl : lab.size = n) :
    ∀ v, v < n →
      (invPerm (lab.map σ.toFun))[σ.toFun v]! = (invPerm lab)[v]! := by
  intro v hv
  rw [invPerm, invPerm, Array.size_map]
  exact invPerm_go_map σ hlab hsl (List.range lab.size)
    (Array.replicate lab.size 0) (Array.replicate lab.size 0)
    (by rw [Array.size_replicate]; exact hsl)
    (by rw [Array.size_replicate]; exact hsl)
    (fun u _ => by rw [getElem!_replicate_zero, getElem!_replicate_zero])
    (fun i hi => List.mem_range.mp hi) v hv

/-- `permset` of an image under the transported map recovers `permset`
of the original set. -/
theorem permset_image (σ : Renaming n) (s : Nat) {perm perm' : Array Nat}
    (hp : ∀ v, v < n → perm'[σ.toFun v]! = perm[v]!) :
    permset (image σ n s) perm' n = permset s perm n := by
  have hps : ∀ (x : Nat) (p : Array Nat),
      permset x p n = image (fun v => p[v]!) n x := fun _ _ => rfl
  rw [hps, hps]
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_image, testBit_image, Bool.eq_iff_iff, List.any_eq_true,
    List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hb⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    have himg := testBit_image σ.toFun n s v
    rw [hb.1] at himg
    rcases List.any_eq_true.mp himg.symm with ⟨u, hu, hub⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hub
    refine ⟨u, hu, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨hub.1, ?_⟩
    rw [← hp u (List.mem_range.mp hu), hub.2]
    exact hb.2
  · rintro ⟨u, hu, hub⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hub
    refine ⟨σ.toFun u,
      List.mem_range.mpr ((σ.maps u).mp (List.mem_range.mp hu)), ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨?_, ?_⟩
    · rw [testBit_image_apply σ s (List.mem_range.mp hu)]
      exact hub.1
    · rw [hp u (List.mem_range.mp hu)]
      exact hub.2

/-- The leaf key rows: `g^lab` in nauty's row order. -/
@[expose] def leafRows (ctx : Ctx) (lab : Array Nat) : List Nat :=
  (List.range ctx.n).map fun i => permset ctx.g[lab[i]!]! (invPerm lab) ctx.n

/-- The leaf key is invariant under a renaming: the transported
labelling on the renamed graph induces the same adjacency rows. -/
theorem leafRows_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    {lab : Array Nat} (hlab : LabOk lab n) (hsl : lab.size = n) :
    leafRows ctx' (lab.map σ.toFun) = leafRows ctx lab := by
  rw [leafRows, leafRows, hn', hn]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [getElem!_map_of_lt σ.toFun lab (by omega),
    hg.2.2 lab[i]! (hlab _ (by omega))]
  exact permset_image σ _ (invPerm_map σ hlab hsl)

/-! # `refine` state invariance and target-cell membership -/

theorem refine_stOk {ctx : Ctx} (hn : ctx.n = n) {level : Nat}
    {lab ptn : Array Nat} {active numcells : Nat}
    (hsl : lab.size = n) (hlab : LabOk lab n) (hsp : ptn.size = n)
    (hact : active < 2 ^ n) (hend : ptn[ptn.size - 1]! ≤ level) :
    StOk n level (refine ctx level lab ptn active numcells) := by
  rw [refine]
  have h := refineLoop_stOk hn (4 * ctx.n + 8)
    { lab, ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells } ⟨hsl, hlab, hsp, hact, hend⟩
  exact ⟨h.labSize, h.labOk, h.ptnSize, h.activeLt, h.ptnEnd⟩

theorem argmaxLoop_lt {bucket : Array Nat} {bound : Nat} :
    ∀ (is : List Nat) (v1 v2 : Nat), v1 < bound → (∀ i ∈ is, i < bound) →
      argmaxLoop bucket is v1 v2 < bound
  | [], _, _, h, _ => h
  | i :: rest, v1, v2, h, his => by
    rw [argmaxLoop]
    split
    · exact argmaxLoop_lt rest i _ (his i (by simp))
        (fun j hj => his j (by simp [hj]))
    · exact argmaxLoop_lt rest v1 v2 h (fun j hj => his j (by simp [hj]))

theorem argmax_start_mem {L : List Nat} (hlen : L.length ≠ 0)
    (B : Array Nat) (v2 : Nat) (is : List Nat)
    (his : ∀ i ∈ is, i < L.length) :
    (List.toArray L)[argmaxLoop B is 0 v2]! ∈ L := by
  rw [List.getElem!_toArray]
  have hidx : argmaxLoop B is 0 v2 < L.length :=
    argmaxLoop_lt is 0 v2 (by omega) his
  rw [getElem!_pos L (argmaxLoop B is 0 v2) hidx]
  exact List.getElem_mem hidx

/-- With a nonsingleton cell present, `bestcell` returns one of the
nonsingleton cell starts. -/
theorem bestcell_mem {ctx : Ctx} {lab ptn : Array Nat} {level : Nat}
    (hex : ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2) ≠ []) :
    bestcell ctx lab ptn level ∈
      ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2).map (·.1) := by
  have hlen : (((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length ≠ 0 := by
    rw [List.length_map]
    intro h0
    exact hex (List.length_eq_zero_iff.mp h0)
  have hcond : ((((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length == 0) = false := by
    simpa using hlen
  simp only [bestcell, hcond, Bool.false_eq_true, ite_false]
  refine argmax_start_mem (by simpa using hlen) _ _ _ ?_
  intro j hj
  have h1 := List.mem_range'_1.mp hj
  have h2 : (((cells ptn level ctx.n).filter
      fun x => decide (x.1 ≠ x.2)).map (·.1)).length ≠ 0 := by
    simpa using hlen
  omega

/-- With a nonsingleton cell present, the hint-free `targetcell` returns
a nonsingleton cell start. -/
theorem targetcell_nontrivial {ctx : Ctx} {lab ptn : Array Nat}
    {level tcLevel : Nat}
    (hex : ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2) :
    ∃ p ∈ cells ptn level ctx.n, p.1 ≠ p.2 ∧
      targetcell ctx lab ptn level tcLevel (-1) = p.1 := by
  have hfne : ((cells ptn level ctx.n).filter
      fun (c1, c2) => c1 ≠ c2) ≠ [] := by
    rcases hex with ⟨p, hpm, hpne⟩
    intro hnil
    have : p ∈ ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2) := by
      rw [List.mem_filter]
      exact ⟨hpm, by simpa using hpne⟩
    rw [hnil] at this
    cases this
  rw [targetcell]
  rw [ite_eq_right (by
    rintro ⟨h0, -⟩
    omega)]
  rcases Decidable.em (level ≤ tcLevel) with hB | hB
  · rw [ite_eq_left hB]
    have hm := bestcell_mem (lab := lab) hfne
    rcases List.mem_map.mp hm with ⟨p, hpf, hp1⟩
    have hpc := List.mem_filter.mp hpf
    exact ⟨p, hpc.1, by simpa using hpc.2, hp1.symm⟩
  · rw [ite_eq_right hB]
    rcases hf : (cells ptn level ctx.n).find? (fun (c1, c2) => c1 ≠ c2)
      with _ | q
    · rcases hex with ⟨p, hpm, hpne⟩
      have := List.find?_eq_none.mp hf p hpm
      simp [hpne] at this
    · rw [hf]
      dsimp only
      rcases q with ⟨c1, c2⟩
      refine ⟨(c1, c2), List.mem_of_find?_eq_some hf, ?_, rfl⟩
      have := List.find?_some hf
      simpa using this

/-! # Individualization state invariance -/

theorem breakout_go_ok {tv : Nat} (hn0 : 0 < n) :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev : Nat), LabOk lab n →
      prev < n →
      (breakout.go tv fuel lab i prev).size = lab.size ∧
        LabOk (breakout.go tv fuel lab i prev) n
  | 0, _, _, _, hlab, _ => ⟨rfl, hlab⟩
  | fuel + 1, lab, i, prev, hlab, hprev => by
    rw [breakout.go]
    have hnext : lab[i]! < n := by
      rcases Nat.lt_or_ge i lab.size with h | h
      · exact hlab i h
      · rw [getElem!_neg _ _ (by omega)]
        exact hn0
    split
    · exact ⟨by rw [Array.size_set!], labOk_set! hlab hprev i⟩
    · have ih := breakout_go_ok (tv := tv) hn0 fuel (lab.set! i prev)
        (i + 1) lab[i]! (labOk_set! hlab hprev i) hnext
      rw [Array.size_set!] at ih
      exact ih

theorem breakout_ok {lab ptn : Array Nat} {level tc tv : Nat}
    (hlab : LabOk lab n) (hn0 : 0 < n) (htv : tv < n) :
    (breakout lab ptn level tc tv).1.size = lab.size ∧
      LabOk (breakout lab ptn level tc tv).1 n := by
  rw [breakout]
  exact breakout_go_ok hn0 (lab.size + 1) lab tc tv hlab htv

end Hex.GraphIso.Nauty
