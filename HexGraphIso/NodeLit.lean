/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert
public import HexGraphIso.IsoLit

public section

/-!
The certificate replay over kernel-cheap list state. The trusted
`checkNode` walks `Array` labelling and partition state, and every
kernel access pays the core `getElem!`/`set!` bounds machinery on top
of the spine walk — measured ~5x the cost of a bare two-case list
accessor for reads at corpus sizes. This file clones the replay's
call tree over `List Nat` state (`atD` reads, `List.set` writes),
proves each clone equal to its original through the unconditional
`Array`/`List` correspondences, and packages `checkKeyLit`: the
negative route's kernel obligation over the tied flat literal with
list state end to end. Compiled paths are untouched; the tactic emits
`checkKeyLit`, and soundness flows through `checkKeyLit_eq` into the
existing `checkKeyFlat`/`checkKey` theorems.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Array/List access correspondences -/

theorem atD_eq_getD {α : Type} :
    ∀ (l : List α) (i : Nat) (d : α), atD l i d = l.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, i + 1, d => atD_eq_getD as i d

theorem getBang_eq_atD (a : Array Nat) (i : Nat) :
    a[i]! = atD a.toList i 0 := by
  rw [atD_eq_getD]
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getD]

theorem setBang_toList (a : Array Nat) (i v : Nat) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [Array.set!]

/-- A packed row read as a bitset is the list read of the bitset rows;
out of range both sides are empty. -/
theorem getBang_toNat_eq_atD (g : Array (VSet n)) (i : Nat) :
    (g[i]!).toNat = atD (g.toList.map VSet.toNat) i 0 := by
  rw [atD_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge i g.size with h | h
  · rw [getElem!_pos g i h, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [getElem!_neg g i (by omega), List.getElem?_eq_none (by simpa using h)]
    exact VSet.toNat_empty

/-! # The list-state context and refine state -/

/-- `Ctx` with the adjacency rows as a bare list of single-`Nat`
bitsets. -/
structure CtxL where
  /-- The number of vertices. -/
  n : Nat
  /-- Row `v` is the neighbour set of vertex `v`, as a bitset. -/
  g : List Nat

/-- The list view of a context. -/
@[expose] def Ctx.toL (ctx : Ctx n) : CtxL := ⟨n, ctx.g.toList.map VSet.toNat⟩

@[simp] theorem toL_n (ctx : Ctx n) : ctx.toL.n = n := rfl
@[simp] theorem toL_g (ctx : Ctx n) : ctx.toL.g = ctx.g.toList.map VSet.toNat := rfl

/-- `RefineSt` with list labelling and partition and a bitset active
set. -/
structure RefineStL where
  lab : List Nat
  ptn : List Nat
  active : Nat
  numcells : Nat
  hint : Nat
  maxpos : Nat
  longcode : Nat

/-- The list view of a refine state. -/
@[expose] def RefineSt.toL (st : RefineSt n) : RefineStL :=
  ⟨st.lab.toList, st.ptn.toList, st.active.toNat, st.numcells, st.hint,
    st.maxpos, st.longcode⟩

@[simp] theorem toL_lab (st : RefineSt n) : st.toL.lab = st.lab.toList := rfl
@[simp] theorem toL_ptn (st : RefineSt n) : st.toL.ptn = st.ptn.toList := rfl
@[simp] theorem toL_active (st : RefineSt n) : st.toL.active = st.active.toNat := rfl
@[simp] theorem toL_numcells (st : RefineSt n) :
    st.toL.numcells = st.numcells := rfl
@[simp] theorem toL_hint (st : RefineSt n) : st.toL.hint = st.hint := rfl
@[simp] theorem toL_maxpos (st : RefineSt n) : st.toL.maxpos = st.maxpos := rfl
@[simp] theorem toL_longcode (st : RefineSt n) :
    st.toL.longcode = st.longcode := rfl

/-! # The refine tower over list state

Each clone mirrors its original body exactly, with `atD` for reads and
`List.set` for writes; the equalities are structural inductions over
the same recursions, rewriting through the access correspondences. -/

@[expose] def cellEndGoL (ptn : List Nat) (level : Nat) :
    Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
    if atD ptn j 0 > level then cellEndGoL ptn level fuel (j + 1) else j

@[expose] def cellEndL (ptn : List Nat) (level i : Nat) : Nat :=
  cellEndGoL ptn level (ptn.length - i) i

theorem cellEndGoL_eq (ptn : Array Nat) (level : Nat) :
    ∀ (fuel j : Nat),
      cellEndGoL ptn.toList level fuel j = cellEnd.go ptn level fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [cellEndGoL, cellEnd.go, ← getBang_eq_atD]
    split <;> simp [cellEndGoL_eq ptn level fuel]

theorem cellEndL_eq (ptn : Array Nat) (level i : Nat) :
    cellEndL ptn.toList level i = cellEnd ptn level i := by
  rw [cellEndL, cellEnd, Array.length_toList, cellEndGoL_eq]

@[expose] def cellsGoL (ptn : List Nat) (level nn : Nat) :
    Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, c1 =>
    if c1 < nn then
      let c2 := cellEndL ptn level c1
      (c1, c2) :: cellsGoL ptn level nn fuel (c2 + 1)
    else
      []

@[expose] def cellsL (ptn : List Nat) (level nn : Nat) :
    List (Nat × Nat) :=
  cellsGoL ptn level nn nn 0

theorem cellsGoL_eq (ptn : Array Nat) (level nn : Nat) :
    ∀ (fuel c1 : Nat),
      cellsGoL ptn.toList level nn fuel c1 = cells.go ptn level nn fuel c1
  | 0, _ => rfl
  | fuel + 1, c1 => by
    rw [cellsGoL, cells.go]
    split
    · simp only [cellEndL_eq, cellsGoL_eq ptn level nn fuel]
    · rfl

theorem cellsL_eq (ptn : Array Nat) (level nn : Nat) :
    cellsL ptn.toList level nn = cells ptn level nn := by
  rw [cellsL, cells, cellsGoL_eq]

@[expose] def splitCellLoopL (gRow : Nat) :
    Nat → List Nat → Int → Int → (List Nat × Int × Int)
  | 0, lab, c1, c2 => (lab, c1, c2)
  | fuel + 1, lab, c1, c2 =>
    if c1 ≤ c2 then
      if gRow.testBit (atD lab c1.toNat 0) then
        splitCellLoopL gRow fuel lab (c1 + 1) c2
      else
        splitCellLoopL gRow fuel
          ((lab.set c1.toNat (atD lab c2.toNat 0)).set c2.toNat
            (atD lab c1.toNat 0))
          c1 (c2 - 1)
    else
      (lab, c1, c2)

theorem splitCellLoopL_eq (gRow : VSet n) :
    ∀ (fuel : Nat) (lab : Array Nat) (c1 c2 : Int),
      splitCellLoopL gRow.toNat fuel lab.toList c1 c2 =
        ((splitCellLoop gRow fuel lab c1 c2).1.toList,
          (splitCellLoop gRow fuel lab c1 c2).2)
  | 0, _, _, _ => rfl
  | fuel + 1, lab, c1, c2 => by
    rw [splitCellLoopL, splitCellLoop]
    simp only [← getBang_eq_atD, ← setBang_toList, VSet.testBit_toNat]
    split
    · split
      · rw [splitCellLoopL_eq gRow fuel]
      · rw [splitCellLoopL_eq gRow fuel]
    · rfl

@[expose] def trivialSplitL (nn level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineStL) : RefineStL :=
  if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
    if st.active.testBit cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat then
      if c1.toNat == cell2 then
        { st with
          ptn := st.ptn.set c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insertL nn st.active c1.toNat
          hint := c1.toNat }
      else
        { st with
          ptn := st.ptn.set c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insertL nn st.active c1.toNat }
    else
      if c2.toNat == cell1 then
        { st with
          ptn := st.ptn.set c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insertL nn st.active cell1
          hint := cell1 }
      else
        { st with
          ptn := st.ptn.set c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insertL nn st.active cell1 }
  else
    st

theorem trivialSplitL_eq (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt n) :
    trivialSplitL n level cell1 cell2 c1 c2 st.toL =
      (trivialSplit level cell1 cell2 c1 c2 st).toL := by
  simp only [trivialSplitL, trivialSplit, toL_active, VSet.testBit_toNat]
  repeat' split
  all_goals simp_all [RefineSt.toL, setBang_toList, VSet.toNat_insert]
  all_goals repeat' split
  all_goals try simp_all
  all_goals exfalso
  all_goals omega

@[expose] def trivialCellL (nn level : Nat) (gRow : Nat)
    (cell1 cell2 : Nat) (st : RefineStL) : RefineStL :=
  if cell1 == cell2 then
    st
  else
    trivialSplitL nn level cell1 cell2
      (splitCellLoopL gRow (cell2 - cell1 + 2) st.lab
        (Int.ofNat cell1) (Int.ofNat cell2)).2.1
      (splitCellLoopL gRow (cell2 - cell1 + 2) st.lab
        (Int.ofNat cell1) (Int.ofNat cell2)).2.2
      { st with
        lab := (splitCellLoopL gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1 }

theorem trivialCellL_eq (level : Nat) (gRow : VSet n)
    (cell1 cell2 : Nat) (st : RefineSt n) :
    trivialCellL n level gRow.toNat cell1 cell2 st.toL =
      (trivialCell level gRow cell1 cell2 st).toL := by
  rw [trivialCellL, trivialCell]
  split
  · rfl
  · rw [show st.toL.lab = st.lab.toList from rfl,
      splitCellLoopL_eq gRow (cell2 - cell1 + 2) st.lab]
    have : ({ st.toL with
        lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1.toList } : RefineStL) =
        ({ st with
          lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).1 } : RefineSt n).toL := rfl
    rw [this, trivialSplitL_eq]

@[expose] def refineTrivialGoL (nn level : Nat) (gRow : Nat) :
    List (Nat × Nat) → RefineStL → RefineStL
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineTrivialGoL nn level gRow rest (trivialCellL nn level gRow cell1 cell2 st)

@[expose] def refineTrivialL (ctx : CtxL) (level split1 : Nat)
    (st : RefineStL) : RefineStL :=
  refineTrivialGoL ctx.n level (atD ctx.g (atD st.lab split1 0) 0)
    (cellsL st.ptn level ctx.n) st

theorem refineTrivialGoL_eq (level : Nat) (gRow : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
      refineTrivialGoL n level gRow.toNat cs st.toL =
        (refineTrivial.go level gRow cs st).toL
  | [], _ => rfl
  | (cell1, cell2) :: rest, st => by
    rw [refineTrivialGoL, refineTrivial.go, trivialCellL_eq,
      refineTrivialGoL_eq level gRow rest]

theorem refineTrivialL_eq (ctx : Ctx n) (level split1 : Nat)
    (st : RefineSt n) :
    refineTrivialL ctx.toL level split1 st.toL =
      (refineTrivial ctx level split1 st).toL := by
  rw [refineTrivialL, refineTrivial, toL_g, toL_n,
    show st.toL.lab = st.lab.toList from rfl,
    show st.toL.ptn = st.ptn.toList from rfl,
    ← getBang_toNat_eq_atD, ← getBang_eq_atD, cellsL_eq, refineTrivialGoL_eq]

@[expose] def worksetOfL (nn : Nat) (lab : List Nat) (lo hi : Nat) : Nat :=
  (List.range (hi + 1 - lo)).foldl (fun w o => insertL nn w (atD lab (lo + o) 0)) 0

theorem worksetOfL_eq (lab : Array Nat) (lo hi : Nat) :
    worksetOfL n lab.toList lo hi = (worksetOf n lab lo hi).toNat := by
  rw [worksetOfL, worksetOf]
  simpa only [VSet.toNat_empty, getBang_eq_atD] using
    (VSet.toNat_foldl_insert (fun o => lab[lo + o]!) (List.range (hi + 1 - lo))
      VSet.empty).symm

@[expose] def countsOfL (ctx : CtxL) (lab : List Nat)
    (workset cell1 cell2 : Nat) : List Nat :=
  (List.range (cell2 + 1 - cell1)).map fun o =>
    popCount (workset &&& atD ctx.g (atD lab (cell1 + o) 0) 0)

theorem countsOfL_eq (ctx : Ctx n) (lab : Array Nat)
    (workset : VSet n) (cell1 cell2 : Nat) :
    countsOfL ctx.toL lab.toList workset.toNat cell1 cell2 =
      countsOf ctx lab workset cell1 cell2 := by
  rw [countsOfL, countsOf]
  refine List.map_congr_left fun o _ => ?_
  rw [toL_g, ← getBang_toNat_eq_atD, ← getBang_eq_atD, VSet.cardInter_eq_popCount]

@[expose] def windowStepL (nn level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineStL) : RefineStL :=
  let st := { st with longcode := mash st.longcode (v + c1) }
  let st :=
    if Int.ofNat (c2 - c1) > maxcell then { st with maxpos := c1 } else st
  let st :=
    if c1 != cell1 then
      let st := { st with
        active := insertL nn st.active c1
        numcells := st.numcells + 1 }
      if c2 - c1 == 1 then { st with hint := c1 } else st
    else
      st
  if c2 ≤ cell2 then { st with ptn := st.ptn.set (c2 - 1) level }
  else st

theorem windowStepL_eq (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt n) :
    windowStepL n level cell1 cell2 v c1 c2 maxcell st.toL =
      (windowStep level cell1 cell2 v c1 c2 maxcell st).toL := by
  simp only [windowStepL, windowStep, toL_active, toL_numcells,
    toL_longcode, toL_maxpos, toL_hint, toL_ptn]
  repeat' split
  all_goals simp [RefineSt.toL, setBang_toList, VSet.toNat_insert]

@[expose] def windowScanL (nn level cell1 cell2 : Nat) (counts : List Nat) :
    List Nat → Nat → Int → RefineStL → RefineStL
  | [], _, _, st => st
  | v :: vs, c1, maxcell, st =>
    if multOf counts v > 0 then
      windowScanL nn level cell1 cell2 counts vs (c1 + multOf counts v)
        (if Int.ofNat (multOf counts v) > maxcell then
          Int.ofNat (multOf counts v)
        else maxcell)
        (windowStepL nn level cell1 cell2 v c1 (c1 + multOf counts v) maxcell st)
    else
      windowScanL nn level cell1 cell2 counts vs c1 maxcell st

theorem windowScanL_eq (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      windowScanL n level cell1 cell2 counts vs c1 maxcell st.toL =
        (windowScan level cell1 cell2 counts vs c1 maxcell st).toL
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScanL, windowScan]
    split
    · rw [windowStepL_eq, windowScanL_eq level cell1 cell2 counts vs]
    · rw [windowScanL_eq level cell1 cell2 counts vs]

@[expose] def segmentOfL (lab : List Nat) (cell1 : Nat)
    (counts : List Nat) (values : List Nat) : List Nat :=
  values.flatMap fun v =>
    (counts.zipIdx.filter fun (c, _) => c == v).map fun (_, j) =>
      atD lab (cell1 + j) 0

theorem segmentOfL_eq (lab : Array Nat) (cell1 : Nat)
    (counts : List Nat) (values : List Nat) :
    segmentOfL lab.toList cell1 counts values =
      segmentOf lab cell1 counts values := by
  simp only [segmentOfL, segmentOf, getBang_eq_atD]

@[expose] def writeSegmentL (lab : List Nat) (cell1 : Nat) :
    List Nat → List Nat
  | [] => lab
  | x :: rest => writeSegmentL (lab.set cell1 x) (cell1 + 1) rest

theorem writeSegmentL_eq :
    ∀ (seg : List Nat) (lab : Array Nat) (cell1 : Nat),
      writeSegmentL lab.toList cell1 seg =
        (writeSegment lab cell1 seg).toList
  | [], _, _ => rfl
  | x :: rest, lab, cell1 => by
    rw [writeSegmentL, writeSegment, ← setBang_toList,
      writeSegmentL_eq rest]

@[expose] def nontrivialFixL (nn cell1 : Nat) (st : RefineStL) : RefineStL :=
  if ¬ st.active.testBit cell1 = true then
    { st with active := eraseL nn (insertL nn st.active cell1) st.maxpos }
  else
    st

theorem nontrivialFixL_eq (cell1 : Nat) (st : RefineSt n) :
    nontrivialFixL n cell1 st.toL = (nontrivialFix cell1 st).toL := by
  simp only [nontrivialFixL, nontrivialFix, toL_active, toL_maxpos, VSet.testBit_toNat]
  repeat' split
  all_goals simp_all [RefineSt.toL, VSet.toNat_insert, VSet.toNat_erase]

@[expose] def nontrivialCellL (ctx : CtxL) (level : Nat)
    (workset cell1 cell2 : Nat) (st : RefineStL) : RefineStL :=
  if cell1 == cell2 then
    st
  else if (countsOfL ctx st.lab workset cell1 cell2).foldl Nat.min
      ((countsOfL ctx st.lab workset cell1 cell2).headD 0) ==
      (countsOfL ctx st.lab workset cell1 cell2).foldl Nat.max
        ((countsOfL ctx st.lab workset cell1 cell2).headD 0) then
    { st with
      longcode := mash st.longcode
        ((countsOfL ctx st.lab workset cell1 cell2).foldl Nat.min
          ((countsOfL ctx st.lab workset cell1 cell2).headD 0) + cell1) }
  else
    nontrivialFixL ctx.n cell1
      { windowScanL ctx.n level cell1 cell2
          (countsOfL ctx st.lab workset cell1 cell2)
          (countValues (countsOfL ctx st.lab workset cell1 cell2))
          cell1 (-1) st with
        lab := writeSegmentL
            (windowScanL ctx.n level cell1 cell2
              (countsOfL ctx st.lab workset cell1 cell2)
              (countValues (countsOfL ctx st.lab workset cell1 cell2))
              cell1 (-1) st).lab cell1
            (segmentOfL
              (windowScanL ctx.n level cell1 cell2
                (countsOfL ctx st.lab workset cell1 cell2)
                (countValues (countsOfL ctx st.lab workset cell1 cell2))
                cell1 (-1) st).lab cell1
              (countsOfL ctx st.lab workset cell1 cell2)
              (countValues (countsOfL ctx st.lab workset cell1 cell2))) }

theorem nontrivialCellL_eq (ctx : Ctx n) (level : Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) :
    nontrivialCellL ctx.toL level workset.toNat cell1 cell2 st.toL =
      (nontrivialCell ctx level workset cell1 cell2 st).toL := by
  rw [nontrivialCellL, nontrivialCell, toL_lab, countsOfL_eq, toL_n]
  split
  · rfl
  · split
    · rfl
    · rw [windowScanL_eq]
      have hlab : (windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st).toL.lab =
          (windowScan level cell1 cell2
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1 cell2))
            cell1 (-1) st).lab.toList := rfl
      rw [hlab, segmentOfL_eq, writeSegmentL_eq]
      have hrec : ({ (windowScan level cell1 cell2
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1 cell2))
            cell1 (-1) st).toL with
          lab := (writeSegment
            (windowScan level cell1 cell2
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2))
              cell1 (-1) st).lab cell1
            (segmentOf
              (windowScan level cell1 cell2
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1 cell2))
                cell1 (-1) st).lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2)))).toList }
          : RefineStL) =
          ({ (windowScan level cell1 cell2
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2))
              cell1 (-1) st) with
            lab := writeSegment
              (windowScan level cell1 cell2
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1 cell2))
                cell1 (-1) st).lab cell1
              (segmentOf
                (windowScan level cell1 cell2
                  (countsOf ctx st.lab workset cell1 cell2)
                  (countValues (countsOf ctx st.lab workset cell1 cell2))
                  cell1 (-1) st).lab cell1
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1 cell2)))
            } : RefineSt n).toL := rfl
      rw [hrec, nontrivialFixL_eq]

@[expose] def refineNontrivialGoL (ctx : CtxL) (level : Nat)
    (workset : Nat) : List (Nat × Nat) → RefineStL → RefineStL
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineNontrivialGoL ctx level workset rest
      (nontrivialCellL ctx level workset cell1 cell2 st)

@[expose] def refineNontrivialL (ctx : CtxL) (level split1 split2 : Nat)
    (st : RefineStL) : RefineStL :=
  let workset := worksetOfL ctx.n st.lab split1 split2
  let st := { st with longcode := mash st.longcode (split2 - split1 + 1) }
  refineNontrivialGoL ctx level workset (cellsL st.ptn level ctx.n) st

theorem refineNontrivialGoL_eq (ctx : Ctx n) (level : Nat)
    (workset : VSet n) :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
      refineNontrivialGoL ctx.toL level workset.toNat cs st.toL =
        (refineNontrivial.go ctx level workset cs st).toL
  | [], _ => rfl
  | (cell1, cell2) :: rest, st => by
    rw [refineNontrivialGoL, refineNontrivial.go, nontrivialCellL_eq,
      refineNontrivialGoL_eq ctx level workset rest]

theorem refineNontrivialL_eq (ctx : Ctx n) (level split1 split2 : Nat)
    (st : RefineSt n) :
    refineNontrivialL ctx.toL level split1 split2 st.toL =
      (refineNontrivial ctx level split1 split2 st).toL := by
  rw [refineNontrivialL, refineNontrivial, toL_lab, toL_ptn, toL_n,
    worksetOfL_eq, cellsL_eq]
  exact refineNontrivialGoL_eq ctx level _ _
    { st with longcode := mash st.longcode (split2 - split1 + 1) }

@[expose] def refineStepL (ctx : CtxL) (level split1 : Nat)
    (st : RefineStL) : RefineStL :=
  let st := { st with active := eraseL ctx.n st.active split1 }
  let split2 := cellEndL st.ptn level split1
  let st := { st with longcode := mash st.longcode (split1 + split2) }
  if split1 == split2 then
    refineTrivialL ctx level split1 st
  else
    refineNontrivialL ctx level split1 split2 st

theorem refineStepL_eq (ctx : Ctx n) (level split1 : Nat)
    (st : RefineSt n) :
    refineStepL ctx.toL level split1 st.toL =
      (refineStep ctx level split1 st).toL := by
  simp only [refineStepL, refineStep, toL_lab, toL_ptn, toL_active,
    toL_numcells, toL_hint, toL_maxpos, toL_longcode, toL_n, cellEndL_eq,
    ← VSet.toNat_erase]
  split
  · exact refineTrivialL_eq ctx level split1
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode (split1 + cellEnd st.ptn level split1) }
  · exact refineNontrivialL_eq ctx level split1
      (cellEnd st.ptn level split1)
      { st with
        active := st.active.erase split1
        longcode := mash st.longcode (split1 + cellEnd st.ptn level split1) }

/-- `pickSplit` over a bitset active set. -/
@[expose] def pickSplitL (active hint : Nat) : Option Nat :=
  if active.testBit hint then
    some hint
  else
    match nextElemL active (some hint) with
    | some v => some v
    | none => nextElemL active none

theorem pickSplitL_eq (active : VSet n) (hint : Nat) :
    pickSplitL active.toNat hint = pickSplit active hint := by
  rw [pickSplitL, pickSplit, VSet.testBit_toNat,
    ← VSet.nextElem_eq_nextElemL (s := active) (pos := some hint),
    ← VSet.nextElem_eq_nextElemL (s := active) (pos := none)]
  rfl

@[expose] def refineLoopL (ctx : CtxL) (level : Nat) :
    Nat → RefineStL → RefineStL
  | 0, st => st
  | fuel + 1, st =>
    if st.numcells < ctx.n then
      match pickSplitL st.active st.hint with
      | some split1 =>
        refineLoopL ctx level fuel (refineStepL ctx level split1 st)
      | none => st
    else
      st

theorem refineLoopL_eq (ctx : Ctx n) (level : Nat) :
    ∀ (fuel : Nat) (st : RefineSt n),
      refineLoopL ctx.toL level fuel st.toL =
        (refineLoop ctx level fuel st).toL
  | 0, _ => rfl
  | fuel + 1, st => by
    rw [refineLoopL, refineLoop, toL_numcells, toL_active, toL_hint,
      toL_n, pickSplitL_eq]
    split
    · rcases hps : pickSplit st.active st.hint with _ | split1
      · simp only [hps]
      · simp only [hps, refineStepL_eq, refineLoopL_eq ctx level fuel]
    · rfl

@[expose] def refineL (ctx : CtxL) (level : Nat) (lab ptn : List Nat)
    (active : Nat) (numcells : Nat) : RefineStL :=
  let st : RefineStL :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0,
      longcode := numcells }
  let st := refineLoopL ctx level (4 * ctx.n + 8) st
  { st with longcode := cleanup (mash st.longcode st.numcells) }

theorem refineL_eq (ctx : Ctx n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) :
    refineL ctx.toL level lab.toList ptn.toList active.toNat numcells =
      (refine ctx level lab ptn active numcells).toL := by
  simp only [refineL, refine, toL_n]
  have h := refineLoopL_eq ctx level (4 * n + 8)
    { lab := lab
      ptn := ptn
      active := active
      numcells := numcells
      hint := 0
      maxpos := 0
      longcode := numcells }
  simp only [RefineSt.toL] at h
  rw [h]
  rfl

/-! # Target cell, breakout, and leaf machinery over list state -/

@[expose] def discreteAtL (ptn : List Nat) (level nn : Nat) : Bool :=
  (cellsL ptn level nn).all fun p => p.1 == p.2

theorem discreteAtL_eq (ptn : Array Nat) (level nn : Nat) :
    discreteAtL ptn.toList level nn = discreteAt ptn level nn := by
  rw [discreteAtL, discreteAt, cellsL_eq]

@[expose] def joinTestL (ctx : CtxL) (lab : List Nat)
    (wset c1 c2 : Nat) : Bool :=
  (countsOfL ctx lab wset c1 c2).any (fun c => decide (0 < c)) &&
    (countsOfL ctx lab wset c1 c2).any
      (fun c => decide (c < popCount wset))

theorem joinTestL_eq (ctx : Ctx n) (lab : Array Nat)
    (wset : VSet n) (c1 c2 : Nat) :
    joinTestL ctx.toL lab.toList wset.toNat c1 c2 =
      joinTest ctx lab wset c1 c2 := by
  rw [joinTestL, joinTest, countsOfL_eq, VSet.card_eq_popCount]

@[expose] def specBestcellRowL (ctx : CtxL) (lab ptn : List Nat)
    (level : Nat) (startArr : List Nat) (workset v2 : Nat) :
    List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    if joinTestL ctx lab workset (atD startArr v1 0)
        (cellEndL ptn level (atD startArr v1 0)) then
      specBestcellRowL ctx lab ptn level startArr workset v2 rest
        ((bucket.set v1 (atD bucket v1 0 + 1)).set v2 (atD bucket v2 0 + 1))
    else
      specBestcellRowL ctx lab ptn level startArr workset v2 rest bucket

theorem specBestcellRowL_eq (ctx : Ctx n) (lab ptn : Array Nat)
    (level : Nat) (startArr : Array Nat) (workset : VSet n) (v2 : Nat) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRowL ctx.toL lab.toList ptn.toList level
        startArr.toList workset.toNat v2 vs bucket.toList =
        (specBestcellRow ctx lab ptn level startArr workset v2 vs
          bucket).toList
  | [], _ => rfl
  | v1 :: rest, bucket => by
    rw [specBestcellRowL, specBestcellRow]
    simp only [← getBang_eq_atD, ← setBang_toList, cellEndL_eq,
      joinTestL_eq]
    split
    · rw [specBestcellRowL_eq ctx lab ptn level startArr workset v2 rest]
    · rw [specBestcellRowL_eq ctx lab ptn level startArr workset v2 rest]

@[expose] def specBestcellRowsL (ctx : CtxL) (lab ptn : List Nat)
    (level : Nat) (startArr : List Nat) :
    List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    specBestcellRowsL ctx lab ptn level startArr rest
      (specBestcellRowL ctx lab ptn level startArr
        (worksetOfL ctx.n lab (atD startArr v2 0)
          (cellEndL ptn level (atD startArr v2 0)))
        v2 (List.range v2) bucket)

theorem specBestcellRowsL_eq (ctx : Ctx n) (lab ptn : Array Nat)
    (level : Nat) (startArr : Array Nat) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      specBestcellRowsL ctx.toL lab.toList ptn.toList level
        startArr.toList vs bucket.toList =
        (specBestcellRows ctx lab ptn level startArr vs bucket).toList
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [specBestcellRowsL, specBestcellRows]
    simp only [← getBang_eq_atD, cellEndL_eq, toL_n, worksetOfL_eq,
      specBestcellRowL_eq, specBestcellRowsL_eq ctx lab ptn level startArr rest]

@[expose] def argmaxLoopL (bucket : List Nat) : List Nat → Nat → Nat → Nat
  | [], v1, _ => v1
  | i :: rest, v1, v2 =>
    if atD bucket i 0 > v2 then
      argmaxLoopL bucket rest i (atD bucket i 0)
    else
      argmaxLoopL bucket rest v1 v2

theorem argmaxLoopL_eq (bucket : Array Nat) :
    ∀ (vs : List Nat) (v1 v2 : Nat),
      argmaxLoopL bucket.toList vs v1 v2 = argmaxLoop bucket vs v1 v2
  | [], _, _ => rfl
  | i :: rest, v1, v2 => by
    rw [argmaxLoopL, argmaxLoop]
    simp only [← getBang_eq_atD]
    split
    · rw [argmaxLoopL_eq bucket rest]
    · rw [argmaxLoopL_eq bucket rest]

@[expose] def specBestcellL (ctx : CtxL) (lab ptn : List Nat)
    (level : Nat) : Nat :=
  let starts := ((cellsL ptn level ctx.n).filter
    fun (c1, c2) => c1 ≠ c2).map (·.1)
  let nnt := starts.length
  if nnt == 0 then
    ctx.n
  else
    let bucket := specBestcellRowsL ctx lab ptn level starts
      (List.range' 1 (nnt - 1)) (List.replicate nnt 0)
    atD starts
      (argmaxLoopL bucket (List.range' 1 (nnt - 1)) 0 (atD bucket 0 0)) 0

theorem specBestcellL_eq (ctx : Ctx n) (lab ptn : Array Nat)
    (level : Nat) :
    specBestcellL ctx.toL lab.toList ptn.toList level =
      specBestcell ctx lab ptn level := by
  rw [specBestcellL, specBestcell, toL_n,
    cellsL_eq]
  simp only []
  split
  · rfl
  · generalize ((cells ptn level n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1) = starts
    have hrows := specBestcellRowsL_eq ctx lab ptn level starts.toArray
      (List.range' 1 (starts.length - 1))
      (Array.replicate starts.length 0)
    have hrows' : specBestcellRowsL ctx.toL lab.toList ptn.toList
        level starts (List.range' 1 (starts.length - 1))
        (List.replicate starts.length 0) =
        (specBestcellRows ctx lab ptn level starts.toArray
          (List.range' 1 (starts.length - 1))
          (Array.replicate starts.length 0)).toList := hrows
    rw [hrows']
    rw [show (atD (specBestcellRows ctx lab ptn level starts.toArray
        (List.range' 1 (starts.length - 1))
        (Array.replicate starts.length 0)).toList 0 0) =
      (specBestcellRows ctx lab ptn level starts.toArray
        (List.range' 1 (starts.length - 1))
        (Array.replicate starts.length 0))[0]! from
      (getBang_eq_atD _ 0).symm]
    rw [argmaxLoopL_eq]
    rw [getBang_eq_atD (starts.toArray)]

@[expose] def specTargetcellL (ctx : CtxL) (lab ptn : List Nat)
    (level tcLevel : Nat) : Nat :=
  if level ≤ tcLevel then
    specBestcellL ctx lab ptn level
  else
    match (cellsL ptn level ctx.n).find? (fun (c1, c2) => c1 ≠ c2) with
    | some (c1, _) => c1
    | none => 0

theorem specTargetcellL_eq (ctx : Ctx n) (lab ptn : Array Nat)
    (level tcLevel : Nat) :
    specTargetcellL ctx.toL lab.toList ptn.toList level tcLevel =
      specTargetcell ctx lab ptn level tcLevel := by
  rw [specTargetcellL, specTargetcell, toL_n,
    cellsL_eq]
  split
  · rw [specBestcellL_eq]
  · rfl

@[expose] def specMaketargetcellL (ctx : CtxL) (lab ptn : List Nat)
    (level tcLevel : Nat) : Nat × Nat × Nat :=
  let i := specTargetcellL ctx lab ptn level tcLevel
  let j := cellEndL ptn level (i + 1)
  (i, worksetOfL ctx.n lab i j, j - i + 1)

theorem specMaketargetcellL_eq (ctx : Ctx n) (lab ptn : Array Nat)
    (level tcLevel : Nat) :
    specMaketargetcellL ctx.toL lab.toList ptn.toList level tcLevel =
      ((specMaketargetcell ctx lab ptn level tcLevel).1,
        (specMaketargetcell ctx lab ptn level tcLevel).2.1.toNat,
        (specMaketargetcell ctx lab ptn level tcLevel).2.2) := by
  rw [specMaketargetcellL, specMaketargetcell]
  simp only [specTargetcellL_eq, cellEndL_eq, toL_n, worksetOfL_eq]

@[expose] def breakoutGoL (tv : Nat) : Nat → List Nat → Nat → Nat → List Nat
  | 0, lab, _, _ => lab
  | fuel + 1, lab, i, prev =>
    let next := atD lab i 0
    let lab := lab.set i prev
    if next == tv then lab else breakoutGoL tv fuel lab (i + 1) next

@[expose] def breakoutL (nn : Nat) (lab ptn : List Nat) (level tc tv : Nat) :
    List Nat × List Nat × Nat :=
  let lab := breakoutGoL tv (lab.length + 1) lab tc tv
  (lab, ptn.set tc level, insertL nn 0 tc)

theorem breakoutGoL_eq (tv : Nat) :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev : Nat),
      breakoutGoL tv fuel lab.toList i prev =
        (breakout.go tv fuel lab i prev).toList
  | 0, _, _, _ => rfl
  | fuel + 1, lab, i, prev => by
    rw [breakoutGoL, breakout.go]
    simp only [← getBang_eq_atD, ← setBang_toList]
    split
    · rfl
    · rw [breakoutGoL_eq tv fuel]

theorem breakoutL_eq (lab ptn : Array Nat) (level tc tv : Nat) :
    breakoutL n lab.toList ptn.toList level tc tv =
      ((breakout n lab ptn level tc tv).1.toList,
        (breakout n lab ptn level tc tv).2.1.toList,
        (breakout n lab ptn level tc tv).2.2.toNat) := by
  rw [breakoutL, breakout]
  simp only [Array.length_toList, breakoutGoL_eq, ← setBang_toList,
    VSet.toNat_insert, VSet.toNat_empty]

@[expose] def segNL (lab : List Nat) (lo len : Nat) : List Nat :=
  (List.range len).map fun o => atD lab (lo + o) 0

theorem segNL_eq (lab : Array Nat) (lo len : Nat) :
    segNL lab.toList lo len = segN lab lo len := by
  rw [segNL, segN]
  simp only [getBang_eq_atD]

@[expose] def checkCellsPermL (ptn lab₁ lab₂' : List Nat)
    (level nn : Nat) : Bool :=
  (cellsL ptn level nn).all fun p =>
    (segNL lab₁ p.1 (p.2 + 1 - p.1)).isPerm
      (segNL lab₂' p.1 (p.2 + 1 - p.1))

theorem checkCellsPermL_eq (ptn lab₁ lab₂' : Array Nat)
    (level nn : Nat) :
    checkCellsPermL ptn.toList lab₁.toList lab₂'.toList level nn =
      checkCellsPerm ptn lab₁ lab₂' level nn := by
  rw [checkCellsPermL, checkCellsPerm, cellsL_eq]
  simp only [segNL_eq]

@[expose] def invPermGoL : List Nat → List Nat → List Nat → List Nat
  | _, [], inv => inv
  | lab, i :: rest, inv =>
    invPermGoL lab rest (inv.set (atD lab i 0) i)

@[expose] def invPermL (lab : List Nat) : List Nat :=
  invPermGoL lab (List.range lab.length) (List.replicate lab.length 0)

theorem invPermGoL_eq (lab : Array Nat) :
    ∀ (idx : List Nat) (inv : Array Nat),
      invPermGoL lab.toList idx inv.toList =
        (invPerm.go lab idx inv).toList
  | [], _ => rfl
  | i :: rest, inv => by
    rw [invPermGoL, invPerm.go]
    simp only [← getBang_eq_atD, ← setBang_toList]
    rw [invPermGoL_eq lab rest]

theorem invPermL_eq (lab : Array Nat) :
    invPermL lab.toList = (invPerm lab).toList := by
  rw [invPermL, invPerm, Array.length_toList]
  have h : (List.replicate lab.size 0 : List Nat) =
      (Array.replicate lab.size 0).toList :=
    (Array.toList_replicate ..).symm
  rw [h, invPermGoL_eq]

@[expose] def permsetL (s : Nat) (perm : List Nat) (nn : Nat) : Nat :=
  imageL nn (fun v => atD perm v 0) s

theorem permsetL_eq (s : VSet n) (perm : Array Nat) :
    permsetL s.toNat perm.toList n = (s.permset perm).toNat := by
  rw [permsetL, VSet.permset, VSet.toNat_image]
  simp only [getBang_eq_atD]

@[expose] def leafRowsL (ctx : CtxL) (lab : List Nat) : List Nat :=
  (List.range ctx.n).map fun i =>
    permsetL (atD ctx.g (atD lab i 0) 0) (invPermL lab) ctx.n

theorem leafRowsL_eq (ctx : Ctx n) (lab : Array Nat) :
    leafRowsL ctx.toL lab.toList = (leafRows ctx lab).map VSet.toNat := by
  rw [leafRowsL, leafRows, toL_n, toL_g, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show permsetL _ _ _ = (_ : VSet n).toNat
  rw [invPermL_eq, ← getBang_toNat_eq_atD, ← getBang_eq_atD, permsetL_eq]

/-! # Literal keys

The kernel replay compares keys whose rows are bitsets: `KeyL` is the
literal the tactic emits, `Key.toL` its reading of a packed key, and
`keyCmpL` mirrors `keyCmp` through `rowCmpL`. -/

/-- A canonical key with bitset rows. -/
structure KeyL where
  /-- The refinement codes along the path, ending with the sentinel. -/
  codes : List Nat
  /-- The leaf's `g^lab` rows, as bitsets, in nauty's row order. -/
  rows : List Nat
deriving Inhabited, Repr, DecidableEq

/-- The literal reading of a packed key. -/
@[expose] def Key.toL (B : Key n) : KeyL := ⟨B.codes, B.rows.map VSet.toNat⟩

/-- The packed key of a literal whose rows are bitsets over `n`
vertices. -/
@[expose] def KeyL.toKey (n : Nat) (K : KeyL) : Key n :=
  ⟨K.codes, K.rows.map VSet.ofNat⟩

theorem KeyL.toL_toKey {K : KeyL} (h : ∀ r ∈ K.rows, r < 2 ^ n) :
    (K.toKey n).toL = K := by
  rcases K with ⟨codes, rows⟩
  simp only [KeyL.toKey, Key.toL, List.map_map, KeyL.mk.injEq, true_and]
  exact (List.map_congr_left fun r hr => VSet.toNat_ofNat (h r hr)).trans (List.map_id _)

@[expose] def keyCmpL (k1 k2 : KeyL) : Ordering :=
  match listCmp compare k1.codes k2.codes with
  | .eq => listCmp rowCmpL k1.rows k2.rows
  | .lt => .lt
  | .gt => .gt

theorem listCmp_map {α β : Type} (cmp : β → β → Ordering) (f : α → β) :
    ∀ (l1 l2 : List α),
      listCmp cmp (l1.map f) (l2.map f) = listCmp (fun a b => cmp (f a) (f b)) l1 l2
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    rw [List.map_cons, List.map_cons, listCmp, listCmp, listCmp_map cmp f as bs]

theorem keyCmpL_eq (codes1 codes2 : List Nat) (rows1 rows2 : List (VSet n)) :
    keyCmpL ⟨codes1, rows1.map VSet.toNat⟩ ⟨codes2, rows2.map VSet.toNat⟩ =
      keyCmp ⟨codes1, rows1⟩ ⟨codes2, rows2⟩ := by
  simp only [keyCmpL, keyCmp, listCmp_map, ← VSet.rowCmp_eq_rowCmpL]
  rfl

theorem keyCmpL_toL (k1 k2 : Key n) : keyCmpL k1.toL k2.toL = keyCmp k1 k2 :=
  keyCmpL_eq k1.codes k2.codes k1.rows k2.rows

/-- `checkDiff` on literal keys. -/
@[expose] def checkDiffL (K1 K2 : KeyL) : Bool :=
  keyCmpL K1 K2 != Ordering.eq

theorem checkDiffL_toL (k1 k2 : Key n) : checkDiffL k1.toL k2.toL = checkDiff k1 k2 := by
  rw [checkDiffL, checkDiff, keyCmpL_toL]

/-! # Checked automorphisms over bitset rows -/

/-- `checkAutom` with bitset rows. -/
@[expose] def checkAutomL (g : List Nat) (nn : Nat) (γ : Array Nat) : Bool :=
  γ.size == nn &&
  ((List.range nn).all fun v => γ[v]! < nn) &&
  (((List.range nn).map fun v => γ[v]!).isPerm (List.range nn)) &&
  ((List.range nn).all fun v =>
    atD g γ[v]! 0 == imageL nn (fun w => γ[w]!) (atD g v 0))

theorem checkAutomL_eq (g : Array (VSet n)) (γ : Array Nat) :
    checkAutomL (g.toList.map VSet.toNat) n γ = checkAutom g γ := by
  rw [checkAutomL, checkAutom]
  congr 1
  refine congrArg _ (funext fun v => ?_)
  rw [← getBang_toNat_eq_atD, ← getBang_toNat_eq_atD, ← VSet.toNat_image, Bool.eq_iff_iff,
    beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => VSet.toNat_inj h, fun h => by rw [h]⟩

/-- `validGammas` with bitset rows. -/
@[expose] def validGammasL (g : List Nat) (nn : Nat) (cert : CertNode) :
    List (Array Nat) :=
  (certGammas (nn + 2) cert []).filter fun γ => checkAutomL g nn γ

theorem validGammasL_eq (g : Array (VSet n)) (cert : CertNode) :
    validGammasL (g.toList.map VSet.toNat) n cert = validGammas g cert := by
  rw [validGammasL, validGammas]
  exact List.filter_congr fun γ _ => checkAutomL_eq g γ

/-! # The certificate replay over list state -/

@[expose] def checkNodeL (ctx : CtxL) (tcLevel : Nat)
    (brows : List Nat) (vgens : List (Array Nat)) :
    Nat → Nat → List Nat → List Nat → Nat → Nat → CertNode →
      List Nat → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes =>
    match bcodes with
    | [] => none
    | bc :: brest =>
      let rs := refineL ctx level lab ptn active numcells
      match cert with
      | .autom _ _ => none
      | .codePrune =>
        if compare rs.longcode bc = .lt then
          some false
        else
          none
      | .leaf =>
        match compare rs.longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAtL rs.ptn level ctx.n then
            match keyCmpL
              ⟨[rs.longcode, codeSentinel], leafRowsL ctx rs.lab⟩
              ⟨bc :: brest, brows⟩ with
            | .gt => none
            | .eq => some true
            | .lt => some false
          else
            none
      | .node children =>
        match compare rs.longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAtL rs.ptn level ctx.n then
            none
          else
            let tcr := specMaketargetcellL ctx rs.lab rs.ptn level
              tcLevel
            if children.length = tcr.2.2 then
              (children.zipIdx 0).foldl
                (fun acc (co : CertNode × Nat) =>
                  match acc with
                  | none => none
                  | some a =>
                    let br := breakoutL ctx.n rs.lab rs.ptn (level + 1) tcr.1
                      (atD rs.lab (tcr.1 + co.2) 0)
                    match
                      match co.1 with
                      | .autom o' γ =>
                        if o' < co.2 &&
                            containsGamma vgens γ &&
                            checkCellsPermL br.2.1
                              (breakoutL ctx.n rs.lab rs.ptn (level + 1)
                                tcr.1 (atD rs.lab (tcr.1 + o') 0)).1
                              (br.1.map fun w => atD γ.toList w 0)
                              (level + 1) ctx.n then
                          some false
                        else
                          none
                      | _ =>
                        checkNodeL ctx tcLevel brows vgens fuel (level + 1)
                          br.1 br.2.1 br.2.2 (rs.numcells + 1) co.1 brest
                    with
                    | none => none
                    | some a' => some (a || a'))
                (some false)
            else
              none
  termination_by structural fuel => fuel

theorem checkNodeL_eq (ctx : Ctx n) (tcLevel : Nat) (brows : List (VSet n))
    (vgens : List (Array Nat)) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (cert : CertNode) (bcodes : List Nat),
      checkNodeL ctx.toL tcLevel (brows.map VSet.toNat) vgens fuel level lab.toList
        ptn.toList active.toNat numcells cert bcodes =
        checkNode ctx tcLevel brows vgens fuel level lab ptn active
          numcells cert bcodes
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes => by
    cases bcodes with
    | nil => rfl
    | cons bc brest =>
      cases cert with
      | autom o' γ => rfl
      | codePrune =>
        show (if compare (refineL ctx.toL level lab.toList ptn.toList
            active.toNat numcells).longcode bc = .lt then some false
          else none) = _
        rw [refineL_eq]
        rfl
      | leaf =>
        show (match compare (refineL ctx.toL level lab.toList
            ptn.toList active.toNat numcells).longcode bc with
          | .gt => none
          | .lt => some false
          | .eq =>
            if discreteAtL (refineL ctx.toL level lab.toList
                ptn.toList active.toNat numcells).ptn level ctx.toL.n then
              match keyCmpL
                ⟨[(refineL ctx.toL level lab.toList ptn.toList active.toNat
                    numcells).longcode, codeSentinel],
                  leafRowsL ctx.toL (refineL ctx.toL level lab.toList
                    ptn.toList active.toNat numcells).lab⟩
                ⟨bc :: brest, brows.map VSet.toNat⟩ with
              | .gt => none
              | .eq => some true
              | .lt => some false
            else
              none) = _
        rw [refineL_eq]
        show (match compare (refine ctx level lab ptn active
            numcells).longcode bc with
          | .gt => none
          | .lt => some false
          | .eq =>
            if discreteAtL (refine ctx level lab ptn active
                numcells).ptn.toList level ctx.toL.n then
              match keyCmpL
                ⟨[(refine ctx level lab ptn active
                    numcells).longcode, codeSentinel],
                  leafRowsL ctx.toL (refine ctx level lab ptn active
                    numcells).lab.toList⟩
                ⟨bc :: brest, brows.map VSet.toNat⟩ with
              | .gt => none
              | .eq => some true
              | .lt => some false
            else
              none) = _
        rw [discreteAtL_eq, leafRowsL_eq, toL_n, keyCmpL_eq]
        rfl
      | node children =>
        have hih := checkNodeL_eq ctx tcLevel brows vgens fuel
        have hfold : ∀ (rsLab rsPtn : Array Nat) (tc m : Nat)
            (cs : List (CertNode × Nat)) (acc : Option Bool),
            cs.foldl
              (fun acc (co : CertNode × Nat) =>
                match acc with
                | none => none
                | some a =>
                  match
                    match co.1 with
                    | .autom o' γ =>
                      if o' < co.2 &&
                          containsGamma vgens γ &&
                          checkCellsPermL
                            (breakoutL n rsLab.toList rsPtn.toList
                              (level + 1) tc
                              (atD rsLab.toList (tc + co.2) 0)).2.1
                            (breakoutL n rsLab.toList rsPtn.toList
                              (level + 1) tc
                              (atD rsLab.toList (tc + o') 0)).1
                            ((breakoutL n rsLab.toList rsPtn.toList
                              (level + 1) tc
                              (atD rsLab.toList (tc + co.2) 0)).1.map
                              fun w => atD γ.toList w 0)
                            (level + 1) n then
                        some false
                      else
                        none
                    | _ =>
                      checkNodeL ctx.toL tcLevel (brows.map VSet.toNat) vgens fuel
                        (level + 1)
                        (breakoutL n rsLab.toList rsPtn.toList
                          (level + 1) tc
                          (atD rsLab.toList (tc + co.2) 0)).1
                        (breakoutL n rsLab.toList rsPtn.toList
                          (level + 1) tc
                          (atD rsLab.toList (tc + co.2) 0)).2.1
                        (breakoutL n rsLab.toList rsPtn.toList
                          (level + 1) tc
                          (atD rsLab.toList (tc + co.2) 0)).2.2
                        (m + 1) co.1 brest
                  with
                  | none => none
                  | some a' => some (a || a')) acc =
            cs.foldl
              (fun acc (co : CertNode × Nat) =>
                match acc with
                | none => none
                | some a =>
                  match
                    match co.1 with
                    | .autom o' γ =>
                      if o' < co.2 &&
                          containsGamma vgens γ &&
                          checkCellsPerm
                            (breakout n rsLab rsPtn (level + 1) tc
                              rsLab[tc + co.2]!).2.1
                            (breakout n rsLab rsPtn (level + 1) tc
                              rsLab[tc + o']!).1
                            (Hex.Array.map' (fun w => γ[w]!)
                              (breakout n rsLab rsPtn (level + 1) tc
                                rsLab[tc + co.2]!).1)
                            (level + 1) n then
                        some false
                      else
                        none
                    | _ =>
                      checkNode ctx tcLevel brows vgens fuel
                        (level + 1)
                        (breakout n rsLab rsPtn (level + 1) tc
                          rsLab[tc + co.2]!).1
                        (breakout n rsLab rsPtn (level + 1) tc
                          rsLab[tc + co.2]!).2.1
                        (breakout n rsLab rsPtn (level + 1) tc
                          rsLab[tc + co.2]!).2.2
                        (m + 1) co.1 brest
                  with
                  | none => none
                  | some a' => some (a || a')) acc := by
          intro rsLab rsPtn tc m cs
          induction cs with
          | nil => intro acc; rfl
          | cons co rest ih =>
            intro acc
            rw [List.foldl_cons, List.foldl_cons]
            rcases acc with _ | a
            · rw [ih]
            · rw [ih]
              congr 1
              rcases co with ⟨c, o⟩
              rcases c with _ | _ | ⟨o', γ⟩ | ch <;>
                simp only [breakoutL_eq, ← getBang_eq_atD, hih,
                  Hex.Array.map'_eq_map, ← Array.toList_map,
                  checkCellsPermL_eq, toL_n]
        rw [checkNodeL, checkNode]
        simp only [refineL_eq, toL_lab, toL_ptn, toL_longcode,
          discreteAtL_eq, specMaketargetcellL_eq,
          toL_n]
        rcases compare (refine ctx level lab ptn active
          numcells).longcode bc with _ | _ | _
        · rfl
        · rcases hd : discreteAt (refine ctx level lab ptn active
            numcells).ptn level n with _ | _
          · simp only [hd, Bool.false_eq_true, ite_false]
            rcases Decidable.em (children.length =
                (specMaketargetcell ctx (refine ctx level lab ptn
                  active numcells).lab (refine ctx level lab ptn
                  active numcells).ptn level tcLevel).2.2) with
              hl | hl
            · simp only [hl, ite_true]
              exact hfold (refine ctx level lab ptn active
                  numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                (specMaketargetcell ctx (refine ctx level lab ptn
                  active numcells).lab (refine ctx level lab ptn
                  active numcells).ptn level tcLevel).1
                (refine ctx level lab ptn active numcells).numcells
                (children.zipIdx 0) (some false)
            · simp [hl]
          · simp only [hd, ite_true]
        · rfl
  termination_by structural fuel => fuel

/-! # The negative kernel obligation over list state -/

end Hex.GraphIso.Nauty

namespace Hex.GraphIso

open Nauty

variable {n k : Nat}

/-- `checkKeyFlat` with list state end to end: the rows are rebuilt
once from the tied flat literal as bitsets and the whole replay walks
bare lists. The negative route's kernel obligation, over a literal key
whose rows must be bitsets over `n` vertices. -/
@[expose] def checkKeyLit (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (K : KeyL) : Bool :=
  K.rows.all (fun r => r < 2 ^ n) &&
  if n == 0 then
    K.codes == [] && K.rows == []
  else
    checkNodeL ⟨n, (flatRows n flat).toList⟩ 100 K.rows
      (validGammasL (flatRows n flat).toList n cert) n 1
      (initialPartition G).1.toList
      (initPtn n (n + 2) (initialPartition G).2).toList
      (initActive n (initialPartition G).2).toNat
      (initialPartition G).2.length cert K.codes = some true

/-- The kernel's literal context is the list view of the packed one. -/
theorem ctxL_flatRows (flat : List Bool) :
    (⟨n, (flatRows n flat).toList⟩ : CtxL) = Ctx.toL { g := rowsOfFlat n flat } := by
  rw [Ctx.toL, toNat_rowsOfFlat]

theorem checkKeyLit_eq (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (K : KeyL) (h : ∀ r ∈ K.rows, r < 2 ^ n) :
    checkKeyLit G flat cert K = checkKeyFlat G flat cert (K.toKey n) := by
  have hall : K.rows.all (fun r => r < 2 ^ n) = true :=
    List.all_eq_true.mpr fun r hr => decide_eq_true (h r hr)
  rw [checkKeyLit, hall, Bool.true_and, checkKeyFlat]
  have hrows : K.rows = ((K.toKey n).rows).map VSet.toNat :=
    (congrArg KeyL.rows (KeyL.toL_toKey h)).symm
  rcases Decidable.em (n = 0) with hn | hn
  · simp only [hn, beq_self_eq_true, ite_true]
    subst hn
    rw [hrows]
    rcases (K.toKey 0).rows with _ | ⟨r, rs⟩
    · rfl
    · simp
  · simp only [show (n == 0) = false by simpa using hn, Bool.false_eq_true, ite_false]
    rw [ctxL_flatRows, hrows, ← toNat_rowsOfFlat, validGammasL_eq]
    simp only [checkNodeL_eq]
    rfl

/-- The tactic-facing certificate producer: `certifyKeyBounded?` with
its key read as a literal. -/
def certifyKeyLit? (budget : Nat) (G : Colored n k) : Option (CertNode × KeyL) :=
  (certifyKeyBounded? budget G).map fun p => (p.1, p.2.toL)

/-- Tying equalities plus two list-state key certificates with
differing keys prove non-isomorphism: `not_isomorphic_of_checkKeysFlat`
with the replay over bare lists. -/
theorem not_isomorphic_of_checkKeysL {G H : Colored n k}
    {certG certH : Nauty.CertNode} {KG KH : KeyL}
    {LA LB : List Bool}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hG : checkKeyLit G LA certG KG = true)
    (hH : checkKeyLit H LB certH KH = true)
    (hd : checkDiffL KG KH = true) : ¬Isomorphic G H := by
  have hbG : ∀ r ∈ KG.rows, r < 2 ^ n := fun r hr =>
    of_decide_eq_true (List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hG).1 r hr)
  have hbH : ∀ r ∈ KH.rows, r < 2 ^ n := fun r hr =>
    of_decide_eq_true (List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hH).1 r hr)
  rw [checkKeyLit_eq _ _ _ _ hbG] at hG
  rw [checkKeyLit_eq _ _ _ _ hbH] at hH
  rw [← KeyL.toL_toKey (n := n) hbG, ← KeyL.toL_toKey (n := n) hbH, checkDiffL_toL] at hd
  exact not_isomorphic_of_checkKeysFlat hA hB hG hH hd

end Hex.GraphIso
