/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert
public import HexGraphIso.Kernel.Packed

public section

/-!
The negative route's kernel obligation, `Kernel.checkKey`.

The trusted `Nauty.checkKey` walks `Array` labelling and partition
state, and every kernel access pays the core `getElem!`/`set!` bounds
machinery on top of a spine walk. `Kernel.checkKey` replays the same
certificate over `lab` and `ptn` packed into fixed-width fields of one
`Nat` and the adjacency rows packed with width `n`, with every
arithmetic step spelled as the raw kernel-accelerated function, so a
read is a shift and a mask, a write a handful of arithmetic steps, and
a refinement pass linear in the kernel.

The equality with `Nauty.checkKey` is threaded through two internal
layers, neither of which the kernel evaluates: the replay's call tree
over `List Nat` state, and the same tree over the rows rebuilt from the
tied flat literal. The packed clones are proven equal to the list ones
under the correspondence `Rep` between a packed number and the list it
encodes, threaded through the state by `RepSt`; the list ones are
proven equal to the `Array` originals by the unconditional
`Array`/`List` correspondences. `Kernel.checkKey_eq` composes the
chain, and `Kernel.not_isomorphic_of_checkKeys` is the theorem the
tactic applies. The compiled search and the `Array` definitions the
soundness proofs mention are untouched.
-/

namespace Hex.GraphIso.Kernel

/-- A canonical key with bitset rows: the literal reading of
`Nauty.Key` that the kernel replay produces and compares. -/
structure Key where
  /-- The refinement codes along the path, ending with the sentinel. -/
  codes : List Nat
  /-- The leaf's `g^lab` rows, as bitsets, in nauty's row order. -/
  rows : List Nat
deriving Inhabited, Repr, DecidableEq

/-- The packed key of a literal whose rows are bitsets over `n`
vertices. -/
@[expose] def Key.toKey (n : Nat) (K : Key) : Nauty.Key n :=
  ⟨K.codes, K.rows.map Nauty.VSet.ofNat⟩

end Hex.GraphIso.Kernel

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

def cellEndGoL (ptn : List Nat) (level : Nat) :
    Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
    if atD ptn j 0 > level then cellEndGoL ptn level fuel (j + 1) else j

def cellEndL (ptn : List Nat) (level i : Nat) : Nat :=
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

def cellsGoL (ptn : List Nat) (level nn : Nat) :
    Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, c1 =>
    if c1 < nn then
      let c2 := cellEndL ptn level c1
      (c1, c2) :: cellsGoL ptn level nn fuel (c2 + 1)
    else
      []

def cellsL (ptn : List Nat) (level nn : Nat) :
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

def splitCellLoopL (gRow : Nat) :
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

def trivialSplitL (nn level cell1 cell2 : Nat) (c1 c2 : Int)
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
  all_goals simp_all [RefineSt.toL, VSet.toNat_insert]
  all_goals repeat' split
  all_goals try simp_all
  all_goals exfalso
  all_goals omega

def trivialCellL (nn level : Nat) (gRow : Nat)
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

def refineTrivialGoL (nn level : Nat) (gRow : Nat) :
    List (Nat × Nat) → RefineStL → RefineStL
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineTrivialGoL nn level gRow rest (trivialCellL nn level gRow cell1 cell2 st)

def refineTrivialL (ctx : CtxL) (level split1 : Nat)
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

def worksetOfL (nn : Nat) (lab : List Nat) (lo hi : Nat) : Nat :=
  (List.range (hi + 1 - lo)).foldl (fun w o => insertL nn w (atD lab (lo + o) 0)) 0

theorem worksetOfL_eq (lab : Array Nat) (lo hi : Nat) :
    worksetOfL n lab.toList lo hi = (worksetOf n lab lo hi).toNat := by
  rw [worksetOfL, worksetOf]
  simpa only [VSet.toNat_empty, getBang_eq_atD] using
    (VSet.toNat_foldl_insert (fun o => lab[lo + o]!) (List.range (hi + 1 - lo))
      VSet.empty).symm

def countsOfL (ctx : CtxL) (lab : List Nat)
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

def windowStepL (nn level cell1 cell2 v c1 c2 : Nat)
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
  all_goals simp [RefineSt.toL, VSet.toNat_insert]

def windowScanL (nn level cell1 cell2 : Nat) (counts : List Nat) :
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

def segmentOfL (lab : List Nat) (cell1 : Nat)
    (counts : List Nat) (values : List Nat) : List Nat :=
  values.flatMap fun v =>
    (counts.zipIdx.filter fun (c, _) => c == v).map fun (_, j) =>
      atD lab (cell1 + j) 0

theorem segmentOfL_eq (lab : Array Nat) (cell1 : Nat)
    (counts : List Nat) (values : List Nat) :
    segmentOfL lab.toList cell1 counts values =
      segmentOf lab cell1 counts values := by
  simp only [segmentOfL, segmentOf, getBang_eq_atD]

def writeSegmentL (lab : List Nat) (cell1 : Nat) :
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

def nontrivialFixL (nn cell1 : Nat) (st : RefineStL) : RefineStL :=
  if ¬ st.active.testBit cell1 = true then
    { st with active := eraseL nn (insertL nn st.active cell1) st.maxpos }
  else
    st

theorem nontrivialFixL_eq (cell1 : Nat) (st : RefineSt n) :
    nontrivialFixL n cell1 st.toL = (nontrivialFix cell1 st).toL := by
  simp only [nontrivialFixL, nontrivialFix, toL_active, toL_maxpos, VSet.testBit_toNat]
  repeat' split
  all_goals simp_all [RefineSt.toL, VSet.toNat_insert, VSet.toNat_erase]

def nontrivialCellL (ctx : CtxL) (level : Nat)
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

def refineNontrivialGoL (ctx : CtxL) (level : Nat)
    (workset : Nat) : List (Nat × Nat) → RefineStL → RefineStL
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineNontrivialGoL ctx level workset rest
      (nontrivialCellL ctx level workset cell1 cell2 st)

def refineNontrivialL (ctx : CtxL) (level split1 split2 : Nat)
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

def refineStepL (ctx : CtxL) (level split1 : Nat)
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
def pickSplitL (active hint : Nat) : Option Nat :=
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

def refineLoopL (ctx : CtxL) (level : Nat) :
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
      · simp only []
      · simp only [refineStepL_eq, refineLoopL_eq ctx level fuel]
    · rfl

def refineL (ctx : CtxL) (level : Nat) (lab ptn : List Nat)
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

def discreteAtL (ptn : List Nat) (level nn : Nat) : Bool :=
  (cellsL ptn level nn).all fun p => p.1 == p.2

theorem discreteAtL_eq (ptn : Array Nat) (level nn : Nat) :
    discreteAtL ptn.toList level nn = discreteAt ptn level nn := by
  rw [discreteAtL, discreteAt, cellsL_eq]

def joinTestL (ctx : CtxL) (lab : List Nat)
    (wset c1 c2 : Nat) : Bool :=
  (countsOfL ctx lab wset c1 c2).any (fun c => decide (0 < c)) &&
    (countsOfL ctx lab wset c1 c2).any
      (fun c => decide (c < popCount wset))

theorem joinTestL_eq (ctx : Ctx n) (lab : Array Nat)
    (wset : VSet n) (c1 c2 : Nat) :
    joinTestL ctx.toL lab.toList wset.toNat c1 c2 =
      joinTest ctx lab wset c1 c2 := by
  rw [joinTestL, joinTest, countsOfL_eq, VSet.card_eq_popCount]

def specBestcellRowL (ctx : CtxL) (lab ptn : List Nat)
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

def specBestcellRowsL (ctx : CtxL) (lab ptn : List Nat)
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

def argmaxLoopL (bucket : List Nat) : List Nat → Nat → Nat → Nat
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

def specBestcellL (ctx : CtxL) (lab ptn : List Nat)
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

def specTargetcellL (ctx : CtxL) (lab ptn : List Nat)
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

def specMaketargetcellL (ctx : CtxL) (lab ptn : List Nat)
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

def breakoutGoL (tv : Nat) : Nat → List Nat → Nat → Nat → List Nat
  | 0, lab, _, _ => lab
  | fuel + 1, lab, i, prev =>
    let next := atD lab i 0
    let lab := lab.set i prev
    if next == tv then lab else breakoutGoL tv fuel lab (i + 1) next

def breakoutL (nn : Nat) (lab ptn : List Nat) (level tc tv : Nat) :
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

def segNL (lab : List Nat) (lo len : Nat) : List Nat :=
  (List.range len).map fun o => atD lab (lo + o) 0

theorem segNL_eq (lab : Array Nat) (lo len : Nat) :
    segNL lab.toList lo len = segN lab lo len := by
  rw [segNL, segN]
  simp only [getBang_eq_atD]

def checkCellsPermL (ptn lab₁ lab₂' : List Nat)
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

def invPermGoL : List Nat → List Nat → List Nat → List Nat
  | _, [], inv => inv
  | lab, i :: rest, inv =>
    invPermGoL lab rest (inv.set (atD lab i 0) i)

def invPermL (lab : List Nat) : List Nat :=
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

def permsetL (s : Nat) (perm : List Nat) (nn : Nat) : Nat :=
  imageL nn (fun v => atD perm v 0) s

theorem permsetL_eq (s : VSet n) (perm : Array Nat) :
    permsetL s.toNat perm.toList n = (s.permset perm).toNat := by
  rw [permsetL, VSet.permset, VSet.toNat_image]
  simp only [getBang_eq_atD]

def leafRowsL (ctx : CtxL) (lab : List Nat) : List Nat :=
  (List.range ctx.n).map fun i =>
    permsetL (atD ctx.g (atD lab i 0) 0) (invPermL lab) ctx.n

theorem leafRowsL_eq (ctx : Ctx n) (lab : Array Nat) :
    leafRowsL ctx.toL lab.toList = (leafRows ctx lab).map VSet.toNat := by
  rw [leafRowsL, leafRows, toL_n, toL_g, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show permsetL _ _ _ = (_ : VSet n).toNat
  rw [invPermL_eq, ← getBang_toNat_eq_atD, ← getBang_eq_atD, permsetL_eq]

/-! # Literal keys

The kernel replay compares keys whose rows are bitsets: `Kernel.Key` is
the literal the tactic emits, `Key.toL` its reading of a packed key, and
`keyCmpL` mirrors `keyCmp` through `rowCmpL`. -/

/-- The literal reading of a packed key. -/
def Key.toL (B : Key n) : Kernel.Key := ⟨B.codes, B.rows.map VSet.toNat⟩

theorem toL_toKey {K : Kernel.Key} (h : ∀ r ∈ K.rows, r < 2 ^ n) :
    (K.toKey n).toL = K := by
  rcases K with ⟨codes, rows⟩
  simp only [Kernel.Key.toKey, Key.toL, List.map_map, Kernel.Key.mk.injEq, true_and]
  exact (List.map_congr_left fun r hr => VSet.toNat_ofNat (h r hr)).trans (List.map_id _)

@[expose] def keyCmpL (k1 k2 : Kernel.Key) : Ordering :=
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
@[expose] def checkDiffL (K1 K2 : Kernel.Key) : Bool :=
  keyCmpL K1 K2 != Ordering.eq

theorem checkDiffL_toL (k1 k2 : Key n) : checkDiffL k1.toL k2.toL = checkDiff k1 k2 := by
  rw [checkDiffL, checkDiff, keyCmpL_toL]

/-! # Checked automorphisms over bitset rows -/

/-- `checkAutom` with bitset rows. -/
def checkAutomL (g : List Nat) (nn : Nat) (γ : Array Nat) : Bool :=
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
def validGammasL (g : List Nat) (nn : Nat) (cert : CertNode) :
    List (Array Nat) :=
  (certGammas (nn + 2) cert []).filter fun γ => checkAutomL g nn γ

theorem validGammasL_eq (g : Array (VSet n)) (cert : CertNode) :
    validGammasL (g.toList.map VSet.toNat) n cert = validGammas g cert := by
  rw [validGammasL, validGammas]
  exact List.filter_congr fun γ _ => checkAutomL_eq g γ

/-! # The certificate replay over list state -/

def checkNodeL (ctx : CtxL) (tcLevel : Nat)
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
                  checkCellsPermL_eq]
        rw [checkNodeL, checkNode]
        simp only [refineL_eq, toL_lab, toL_ptn, toL_longcode,
          discreteAtL_eq, specMaketargetcellL_eq,
          toL_n]
        rcases compare (refine ctx level lab ptn active
          numcells).longcode bc with _ | _ | _
        · rfl
        · rcases hd : discreteAt (refine ctx level lab ptn active
            numcells).ptn level n with _ | _
          · simp only [Bool.false_eq_true, ite_false]
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
          · simp only [ite_true]
        · rfl
  termination_by structural fuel => fuel

/-! # The negative kernel obligation over list state -/
/-! # Packed context and state -/

/-- The replay context over packed rows: `w`/`m` are the field width
and mask for positions and vertices, `g` the rows packed with width
`n`, and `rm` the row mask. -/
structure CtxP where
  /-- The number of vertices. -/
  n : Nat
  /-- The field width of packed position and vertex vectors. -/
  w : Nat
  /-- `2 ^ w - 1`. -/
  m : Nat
  /-- The adjacency rows, row `v` in bits `[n * v, n * (v + 1))`. -/
  g : Nat
  /-- `2 ^ n - 1`. -/
  rm : Nat

/-- The correspondence between a packed context and a list context. -/
structure CtxRep (ctx : CtxP) (ctxL : CtxL) : Prop where
  n : ctx.n = ctxL.n
  m : ctx.m = 2 ^ ctx.w - 1
  rm : ctx.rm = 2 ^ ctx.n - 1
  g : Rep ctx.n ctx.n ctx.g ctxL.g
  /-- Positions, vertices, the initial partition's infinity `n + 2`, and
  every level the replay's fuel of `n` reaches fit a field. -/
  nlt : ctx.n + 2 < 2 ^ ctx.w

/-- Read a packed position or vertex vector. -/
@[expose] def lget (ctx : CtxP) (a i : Nat) : Nat := pget ctx.w ctx.m a i

/-- Write a packed position or vertex vector. -/
@[expose] def lset (ctx : CtxP) (a i v : Nat) : Nat :=
  pset ctx.w ctx.m ctx.n a i v

/-- The row of vertex `v`. -/
@[expose] def rowP (ctx : CtxP) (v : Nat) : Nat := pget ctx.n ctx.rm ctx.g v

theorem lget_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) {a : Nat}
    {l : List Nat} (hr : Rep ctx.w ctx.n a l) (i : Nat) :
    lget ctx a i = atD l i 0 := by
  rw [lget, h.m, hr.get]

theorem lget_lt {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (a i : Nat) :
    lget ctx a i < 2 ^ ctx.w := by
  rw [lget, h.m]
  exact pget_lt ..

theorem lset_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) {a : Nat}
    {l : List Nat} (hr : Rep ctx.w ctx.n a l) (i : Nat) {v : Nat}
    (hv : v < 2 ^ ctx.w) : Rep ctx.w ctx.n (lset ctx a i v) (l.set i v) := by
  rw [lset, h.m]
  exact hr.set i hv

theorem rowP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (v : Nat) :
    rowP ctx v = atD ctxL.g v 0 := by
  rw [rowP, h.rm, h.g.get]

/-- `RefineSt` with packed labelling and partition. -/
structure RefineStP where
  lab : Nat
  ptn : Nat
  active : Nat
  numcells : Nat
  hint : Nat
  maxpos : Nat
  longcode : Nat

/-- The correspondence between packed and list refine states. -/
structure RepSt (w n : Nat) (st : RefineStP) (stL : RefineStL) : Prop where
  lab : Rep w n st.lab stL.lab
  ptn : Rep w n st.ptn stL.ptn
  active : st.active = stL.active
  numcells : st.numcells = stL.numcells
  hint : st.hint = stL.hint
  maxpos : st.maxpos = stL.maxpos
  longcode : st.longcode = stL.longcode

/-- `RepSt` from the two packed correspondences and the scalar field
equalities in one conjunction. -/
theorem RepSt.mk' {w n : Nat} {st : RefineStP} {stL : RefineStL}
    (hlab : Rep w n st.lab stL.lab) (hptn : Rep w n st.ptn stL.ptn)
    (hrest : st.active = stL.active ∧ st.numcells = stL.numcells ∧
      st.hint = stL.hint ∧ st.maxpos = stL.maxpos ∧ st.longcode = stL.longcode) :
    RepSt w n st stL :=
  ⟨hlab, hptn, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2⟩

/-! # Raw helpers -/

theorem cond_and {α : Type} (a b : Bool) (x y : α) :
    cond (a && b) x y = if a = true ∧ b = true then x else y := by
  cases a <;> cases b <;> simp

theorem cond_or {α : Type} (a b : Bool) (x y : α) :
    cond (a || b) x y = if a = true ∨ b = true then x else y := by
  cases a <;> cases b <;> simp

/-- `Nat.max`, raw. -/
@[expose] def maxK (a b : Nat) : Nat := cond (Nat.ble a b) b a

theorem maxK_eq (a b : Nat) : maxK a b = Nat.max a b := by
  rw [maxK, cond_ble]
  rfl

/-- `Nat.min`, raw. -/
@[expose] def minK (a b : Nat) : Nat := cond (Nat.ble a b) a b

theorem minK_eq (a b : Nat) : minK a b = Nat.min a b := by
  rw [minK, cond_ble]
  rfl

/-- `multOf`, raw. -/
@[expose] def multOfK (counts : List Nat) (v : Nat) : Nat :=
  go counts 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | c :: rest, acc => go rest (cond (Nat.beq c v) (Nat.add acc 1) acc)

theorem multOfK_go_eq (v : Nat) : ∀ (counts : List Nat) (acc : Nat),
    multOfK.go v counts acc = List.countP.go (· == v) counts acc
  | [], _ => rfl
  | c :: rest, acc => by
    rw [multOfK.go, List.countP.go, multOfK_go_eq v rest, cond_beq, add_eq]
    rcases Decidable.em (c = v) with h | h
    · simp [h]
    · simp [h]

theorem multOfK_eq (counts : List Nat) (v : Nat) :
    multOfK counts v = multOf counts v := by
  rw [multOfK, multOf, List.countP, multOfK_go_eq]

/-- `countValues`, raw. -/
@[expose] def countValuesK (counts : List Nat) : List Nat :=
  let lo := counts.foldl minK (counts.headD 0)
  mapRange (Nat.sub (Nat.add (counts.foldl maxK (counts.headD 0)) 1) lo)
    (Nat.add lo ·)

theorem countValuesK_eq (counts : List Nat) :
    countValuesK counts = countValues counts := by
  rw [countValuesK, countValues, mapRange_eq]
  simp only [add_eq, sub_eq]
  have hmax : maxK = Nat.max := funext fun a => funext fun b => maxK_eq a b
  have hmin : minK = Nat.min := funext fun a => funext fun b => minK_eq a b
  rw [hmax, hmin]

/-- `pickSplit`, raw. -/
@[expose] def pickSplitK (active hint : Nat) : Option Nat :=
  cond (elemK active hint) (some hint)
    (match nextElemK active (some hint) with
    | some v => some v
    | none => nextElemK active none)

theorem pickSplitK_eq (active hint : Nat) :
    pickSplitK active hint = pickSplitL active hint := by
  cases hn : nextElemL active (some hint) <;>
    simp [pickSplitK, pickSplitL, elemK_eq, nextElemK_eq, hn]

/-- The bound on a bit set's population. -/
theorem popCount_le_of_lt {nn s : Nat} (hs : s < 2 ^ nn) :
    popCount s ≤ nn := by
  rw [popCount_eq_bitCount nn s hs, bitCount]
  exact Nat.le_trans List.countP_le_length
    (Nat.le_of_eq (List.length_range ..))

/-! # The refine tower over packed state -/

@[expose] def cellEndGoP (ctx : CtxP) (ptn level fuel : Nat) : Nat → Nat :=
  fuelRec fuel (fun j => j) fun ih j =>
    cond (Nat.blt level (lget ctx ptn j)) (ih (Nat.add j 1)) j

theorem cellEndGoP_succ (ctx : CtxP) (ptn level fuel j : Nat) :
    cellEndGoP ctx ptn level (fuel + 1) j =
      cond (Nat.blt level (lget ctx ptn j))
        (cellEndGoP ctx ptn level fuel (Nat.add j 1)) j := rfl

@[expose] def cellEndP (ctx : CtxP) (ptn level i : Nat) : Nat :=
  cellEndGoP ctx ptn level (Nat.sub ctx.n i) i

theorem cellEndGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : ∀ (fuel j : Nat),
      cellEndGoP ctx ptnP level fuel j = cellEndGoL ptn level fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [cellEndGoP_succ, cellEndGoL, cond_blt, lget_eq h hp, add_eq]
    rcases Decidable.em (level < atD ptn j 0) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl, cellEndGoP_eq h hp level fuel]
    · rw [ite_eq_right hl, ite_eq_right hl]

theorem cellEndP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level i : Nat) : cellEndP ctx ptnP level i = cellEndL ptn level i := by
  rw [cellEndP, cellEndL, hp.len, sub_eq, cellEndGoP_eq h hp]

@[expose] def cellsGoP (ctx : CtxP) (ptn level fuel : Nat) :
    Nat → List (Nat × Nat) :=
  fuelRec fuel (fun _ => []) fun ih c1 =>
    cond (Nat.blt c1 ctx.n)
      (let c2 := cellEndP ctx ptn level c1
      (c1, c2) :: ih (Nat.add c2 1))
      []

theorem cellsGoP_succ (ctx : CtxP) (ptn level fuel c1 : Nat) :
    cellsGoP ctx ptn level (fuel + 1) c1 =
      cond (Nat.blt c1 ctx.n)
        (let c2 := cellEndP ctx ptn level c1
        (c1, c2) :: cellsGoP ctx ptn level fuel (Nat.add c2 1))
        [] := rfl

@[expose] def cellsP (ctx : CtxP) (ptn level : Nat) : List (Nat × Nat) :=
  cellsGoP ctx ptn level ctx.n 0

theorem cellsGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : ∀ (fuel c1 : Nat),
      cellsGoP ctx ptnP level fuel c1 = cellsGoL ptn level ctxL.n fuel c1
  | 0, _ => rfl
  | fuel + 1, c1 => by
    rw [cellsGoP_succ, cellsGoL, cond_blt, h.n]
    rcases Decidable.em (c1 < ctxL.n) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl]
      simp only [cellEndP_eq h hp, add_eq, cellsGoP_eq h hp level fuel]
    · rw [ite_eq_right hl, ite_eq_right hl]

theorem cellsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : cellsP ctx ptnP level = cellsL ptn level ctxL.n := by
  rw [cellsP, cellsL, cellsGoP_eq h hp, h.n]

/-- The two-pointer partition with `d = c2 + 1`, so the right pointer
stays a natural (`d = 0` is nauty's `c2 = -1`). -/
@[expose] def splitCellLoopP (ctx : CtxP) (gRow fuel : Nat) :
    Nat → Nat → Nat → (Nat × Nat × Nat) :=
  fuelRec fuel (fun lab c1 d => (lab, c1, d)) fun ih lab c1 d =>
    cond (Nat.blt c1 d)
      (cond (elemK gRow (lget ctx lab c1))
        (ih lab (Nat.add c1 1) d)
        (ih (lset ctx (lset ctx lab c1 (lget ctx lab (Nat.sub d 1)))
            (Nat.sub d 1) (lget ctx lab c1))
          c1 (Nat.sub d 1)))
      (lab, c1, d)

theorem splitCellLoopP_zero (ctx : CtxP) (gRow lab c1 d : Nat) :
    splitCellLoopP ctx gRow 0 lab c1 d = (lab, c1, d) := rfl

theorem splitCellLoopP_succ (ctx : CtxP) (gRow fuel lab c1 d : Nat) :
    splitCellLoopP ctx gRow (fuel + 1) lab c1 d =
      cond (Nat.blt c1 d)
        (cond (elemK gRow (lget ctx lab c1))
          (splitCellLoopP ctx gRow fuel lab (Nat.add c1 1) d)
          (splitCellLoopP ctx gRow fuel
            (lset ctx (lset ctx lab c1 (lget ctx lab (Nat.sub d 1)))
              (Nat.sub d 1) (lget ctx lab c1))
            c1 (Nat.sub d 1)))
        (lab, c1, d) := rfl

theorem splitCellLoopP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (gRow : Nat) : ∀ (fuel : Nat) {labP : Nat} {lab : List Nat},
      Rep ctx.w ctx.n labP lab → ∀ (c1 d : Nat),
      Rep ctx.w ctx.n (splitCellLoopP ctx gRow fuel labP c1 d).1
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).1 ∧
      ((splitCellLoopP ctx gRow fuel labP c1 d).2.1 : Int) =
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).2.1 ∧
      ((splitCellLoopP ctx gRow fuel labP c1 d).2.2 : Int) =
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).2.2 + 1
  | 0, _, _, hl, c1, d => by
    rw [splitCellLoopP_zero, splitCellLoopL]
    exact ⟨hl, rfl, by simp⟩
  | fuel + 1, labP, lab, hl, c1, d => by
    rw [splitCellLoopP_succ, splitCellLoopL, cond_blt]
    simp only [add_eq, sub_eq]
    rcases Decidable.em (c1 < d) with hlt | hlt
    · have he' : elemK gRow (lget ctx labP c1) = Nat.testBit gRow (atD lab c1 0) := by
        rw [elemK_eq, lget_eq h hl]
      rw [ite_eq_left hlt, ite_eq_left (show (c1 : Int) ≤ (d : Int) - 1 by omega),
        he', cond_beq_true, Int.toNat_natCast]
      rcases Decidable.em (Nat.testBit gRow (atD lab c1 0) = true) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        have := splitCellLoopP_eq h gRow fuel hl (c1 + 1) d
        simpa using this
      · rw [ite_eq_right he, ite_eq_right he]
        have hsub : ((d : Int) - 1).toNat = d - 1 := by omega
        have hl' : Rep ctx.w ctx.n
            (lset ctx (lset ctx labP c1 (lget ctx labP (d - 1))) (d - 1)
              (lget ctx labP c1))
            ((lab.set c1 (atD lab (d - 1) 0)).set (d - 1) (atD lab c1 0)) := by
          rw [← lget_eq h hl, ← lget_eq h hl]
          exact lset_rep h (lset_rep h hl c1 (lget_lt h _ _)) _ (lget_lt h _ _)
        have := splitCellLoopP_eq h gRow fuel hl' c1 (d - 1)
        rw [hsub]
        have hd : (((d - 1 : Nat) : Int) - 1 : Int) = (d : Int) - 1 - 1 := by omega
        rw [hd] at this
        exact this
    · rw [ite_eq_right hlt, ite_eq_right (show ¬ (c1 : Int) ≤ (d : Int) - 1 by omega)]
      exact ⟨hl, rfl, by simp⟩

@[expose] def trivialSplitP (ctx : CtxP) (level cell1 cell2 c1 d : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.ble (Nat.add cell1 1) d && Nat.ble c1 cell2)
    (cond (elemK st.active cell1 ||
        Nat.ble (Nat.sub cell2 c1) (Nat.sub (Nat.sub d 1) cell1))
      (cond (Nat.beq c1 cell2)
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK ctx.n st.active c1
          hint := c1 }
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK ctx.n st.active c1 })
      (cond (Nat.beq (Nat.sub d 1) cell1)
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK ctx.n st.active cell1
          hint := cell1 }
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK ctx.n st.active cell1 }))
    st

theorem trivialSplitP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 c1 d : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (trivialSplitP ctx level cell1 cell2 c1 d st)
      (trivialSplitL ctxL.n level cell1 cell2 (c1 : Int) ((d : Int) - 1) stL) := by
  have hsub : ((d : Int) - 1).toNat = d - 1 := by omega
  rw [trivialSplitP, trivialSplitL, cond_and, cond_or, cond_beq, cond_beq,
    hst.active, elemK_eq]
  simp only [Nat.ble_eq, add_eq, sub_eq, Int.ofNat_eq_natCast, Int.toNat_natCast, hsub,
    beq_iff_eq]
  have hlem : ∀ (i : Nat), RepSt ctx.w ctx.n
      ⟨st.lab, lset ctx st.ptn (d - 1) level, insertK ctx.n stL.active i,
        st.numcells + 1, i, st.maxpos, mashK st.longcode (d - 1)⟩
      ⟨stL.lab, stL.ptn.set (d - 1) level, insertL ctxL.n stL.active i,
        stL.numcells + 1, i, stL.maxpos, mash stL.longcode (d - 1)⟩ := fun i =>
    RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev)
      (by simp [hst.numcells, hst.maxpos, hst.longcode, mashK_eq, insertK_eq, h.n])
  have hlem' : ∀ (i : Nat), RepSt ctx.w ctx.n
      ⟨st.lab, lset ctx st.ptn (d - 1) level, insertK ctx.n stL.active i,
        st.numcells + 1, st.hint, st.maxpos, mashK st.longcode (d - 1)⟩
      ⟨stL.lab, stL.ptn.set (d - 1) level, insertL ctxL.n stL.active i,
        stL.numcells + 1, stL.hint, stL.maxpos, mash stL.longcode (d - 1)⟩ := fun i =>
    RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev)
      (by simp [hst.numcells, hst.hint, hst.maxpos, hst.longcode, mashK_eq,
        insertK_eq, h.n])
  rcases Decidable.em (cell1 + 1 ≤ d ∧ c1 ≤ cell2) with hc | hc
  · rw [ite_eq_left hc,
      ite_eq_left (show (d : Int) - 1 ≥ (cell1 : Int) ∧ (c1 : Int) ≤ (cell2 : Int) by omega)]
    rcases Decidable.em (Nat.testBit stL.active cell1 = true ∨
        cell2 - c1 ≤ d - 1 - cell1) with ho | ho
    · rw [ite_eq_left ho,
        ite_eq_left (show Nat.testBit stL.active cell1 = true ∨ d - 1 - cell1 ≥ cell2 - c1 by
          simpa using ho)]
      rcases Decidable.em (c1 = cell2) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        exact hlem c1
      · rw [ite_eq_right he, ite_eq_right he]
        exact hlem' c1
    · rw [ite_eq_right ho,
        ite_eq_right (show ¬ (Nat.testBit stL.active cell1 = true ∨ d - 1 - cell1 ≥ cell2 - c1) by
          simpa using ho)]
      rcases Decidable.em (d - 1 = cell1) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        exact hlem cell1
      · rw [ite_eq_right he, ite_eq_right he]
        exact hlem' cell1
  · rw [ite_eq_right hc,
      ite_eq_right (show ¬ ((d : Int) - 1 ≥ (cell1 : Int) ∧ (c1 : Int) ≤ (cell2 : Int)) by
        omega)]
    exact hst

@[expose] def trivialCellP (ctx : CtxP) (level gRow cell1 cell2 : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.beq cell1 cell2) st
    (let r := splitCellLoopP ctx gRow (Nat.add (Nat.sub cell2 cell1) 2) st.lab
      cell1 (Nat.add cell2 1)
    trivialSplitP ctx level cell1 cell2 r.2.1 r.2.2 { st with lab := r.1 })

theorem trivialCellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (gRow cell1 cell2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (trivialCellP ctx level gRow cell1 cell2 st)
      (trivialCellL ctxL.n level gRow cell1 cell2 stL) := by
  rw [trivialCellP, trivialCellL, cond_beq]
  rcases Decidable.em (cell1 = cell2) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    simp only [add_eq, sub_eq, Int.ofNat_eq_natCast]
    have hloop := splitCellLoopP_eq h gRow (cell2 - cell1 + 2) hst.lab cell1
      (cell2 + 1)
    have hd : (((cell2 + 1 : Nat) : Int) - 1 : Int) = (cell2 : Int) := by omega
    rw [hd] at hloop
    obtain ⟨hlab, hc1, hc2⟩ := hloop
    have hst' : RepSt ctx.w ctx.n
        { st with lab := (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab
          cell1 (cell2 + 1)).1 }
        { stL with lab := (splitCellLoopL gRow (cell2 - cell1 + 2) stL.lab
          (cell1 : Int) (cell2 : Int)).1 } :=
      ⟨hlab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
        hst.longcode⟩
    have := trivialSplitP_eq h hlev cell1 cell2
      (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab cell1 (cell2 + 1)).2.1
      (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab cell1 (cell2 + 1)).2.2
      hst'
    rw [hc1, hc2, Int.add_sub_cancel] at this
    exact this

@[expose] def refineTrivialGoP (ctx : CtxP) (level gRow : Nat) :
    List (Nat × Nat) → RefineStP → RefineStP
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineTrivialGoP ctx level gRow rest
      (trivialCellP ctx level gRow cell1 cell2 st)

@[expose] def refineTrivialP (ctx : CtxP) (level split1 : Nat)
    (st : RefineStP) : RefineStP :=
  refineTrivialGoP ctx level (rowP ctx (lget ctx st.lab split1))
    (cellsP ctx st.ptn level) st

theorem refineTrivialGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (gRow : Nat) :
    ∀ (cs : List (Nat × Nat)) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineTrivialGoP ctx level gRow cs st)
        (refineTrivialGoL ctxL.n level gRow cs stL)
  | [], _, _, hst => hst
  | (cell1, cell2) :: rest, _, _, hst => by
    rw [refineTrivialGoP, refineTrivialGoL]
    exact refineTrivialGoP_eq h hlev gRow rest
      (trivialCellP_eq h hlev gRow cell1 cell2 hst)

theorem refineTrivialP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineTrivialP ctx level split1 st)
      (refineTrivialL ctxL level split1 stL) := by
  rw [refineTrivialP, refineTrivialL, rowP_eq h, lget_eq h hst.lab,
    cellsP_eq h hst.ptn]
  exact refineTrivialGoP_eq h hlev _ _ hst

@[expose] def worksetOfP (ctx : CtxP) (lab lo hi : Nat) : Nat :=
  iterUp (Nat.sub (Nat.add hi 1) lo)
    (fun o w => insertK ctx.n w (lget ctx lab (Nat.add lo o))) 0

theorem worksetOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (lo hi : Nat) :
    worksetOfP ctx labP lo hi = worksetOfL ctxL.n lab lo hi := by
  rw [worksetOfP, worksetOfL, iterUp_eq_foldl]
  simp only [insertK_eq, lget_eq h hl, add_eq, sub_eq, h.n]

@[expose] def countsOfP (ctx : CtxP) (lab workset cell1 cell2 : Nat) :
    List Nat :=
  mapRange (Nat.sub (Nat.add cell2 1) cell1) fun o =>
    popCountK (Nat.land workset (rowP ctx (lget ctx lab (Nat.add cell1 o))))

theorem countsOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    (workset cell1 cell2 : Nat) :
    countsOfP ctx labP workset cell1 cell2 =
      countsOfL ctxL lab workset cell1 cell2 := by
  rw [countsOfP, countsOfL, mapRange_eq]
  simp only [popCountK_eq, land_eq, rowP_eq h, lget_eq h hl, add_eq, sub_eq]

/-- `windowStep` with `maxcell1 = maxcell + 1`, so nauty's `-1` seed
is `0`. -/
@[expose] def windowStepP (ctx : CtxP) (level cell1 cell2 v c1 c2 maxcell1 : Nat)
    (st : RefineStP) : RefineStP :=
  let st := { st with longcode := mashK st.longcode (Nat.add v c1) }
  let st :=
    cond (Nat.blt maxcell1 (Nat.add (Nat.sub c2 c1) 1))
      { st with maxpos := c1 } st
  let st :=
    cond (Nat.beq c1 cell1) st
      (let st := { st with
        active := insertK ctx.n st.active c1
        numcells := Nat.add st.numcells 1 }
      cond (Nat.beq (Nat.sub c2 c1) 1) { st with hint := c1 } st)
  cond (Nat.ble c2 cell2)
    { st with ptn := lset ctx st.ptn (Nat.sub c2 1) level } st

theorem windowStepP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 v c1 c2 maxcell1 : Nat)
    (maxcell : Int) (hmax : (maxcell1 : Int) = maxcell + 1)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (windowStepP ctx level cell1 cell2 v c1 c2 maxcell1 st)
      (windowStepL ctxL.n level cell1 cell2 v c1 c2 maxcell stL) := by
  rw [windowStepP, windowStepL]
  simp only [cond_blt, cond_beq, cond_ble, add_eq, sub_eq, mashK_eq,
    insertK_eq, hst.active, hst.numcells, hst.longcode, hst.maxpos, hst.hint,
    Int.ofNat_eq_natCast, bne_iff_ne, beq_iff_eq, ne_eq]
  have h1 : (((c2 - c1 : Nat) : Int) > maxcell) ↔ (maxcell1 < c2 - c1 + 1) := by
    omega
  simp only [h1]
  repeat' split
  all_goals first
    | exact RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev) (by simp [h.n])
    | exact RepSt.mk' hst.lab hst.ptn (by simp [h.n])
    | (exfalso; omega)

@[expose] def windowScanP (ctx : CtxP) (level cell1 cell2 : Nat)
    (counts : List Nat) : List Nat → Nat → Nat → RefineStP → RefineStP
  | [], _, _, st => st
  | v :: vs, c1, maxcell1, st =>
    let mult := multOfK counts v
    cond (Nat.blt 0 mult)
      (windowScanP ctx level cell1 cell2 counts vs (Nat.add c1 mult)
        (cond (Nat.blt maxcell1 (Nat.add mult 1)) (Nat.add mult 1) maxcell1)
        (windowStepP ctx level cell1 cell2 v c1 (Nat.add c1 mult) maxcell1 st))
      (windowScanP ctx level cell1 cell2 counts vs c1 maxcell1 st)

theorem windowScanP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 : Nat)
    (counts : List Nat) : ∀ (vs : List Nat) (c1 maxcell1 : Nat)
      (maxcell : Int), (maxcell1 : Int) = maxcell + 1 →
      ∀ {st : RefineStP} {stL : RefineStL}, RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (windowScanP ctx level cell1 cell2 counts vs c1 maxcell1 st)
        (windowScanL ctxL.n level cell1 cell2 counts vs c1 maxcell stL)
  | [], _, _, _, _, _, _, hst => hst
  | v :: vs, c1, maxcell1, maxcell, hmax, st, stL, hst => by
    rw [windowScanP, windowScanL]
    simp only [multOfK_eq, cond_blt, add_eq]
    rcases Decidable.em (0 < multOf counts v) with hm | hm
    · rw [ite_eq_left hm, ite_eq_left hm]
      refine windowScanP_eq h hlev cell1 cell2 counts vs _ _ _ ?_
        (windowStepP_eq h hlev cell1 cell2 v c1 _ maxcell1 maxcell hmax hst)
      simp only [Int.ofNat_eq_natCast]
      rcases Decidable.em (maxcell1 < multOf counts v + 1) with hl | hl
      · rw [ite_eq_left hl,
          ite_eq_left (show ((multOf counts v : Nat) : Int) > maxcell by omega)]
        simp
      · rw [ite_eq_right hl,
          ite_eq_right (show ¬ ((multOf counts v : Nat) : Int) > maxcell by omega)]
        exact hmax
    · rw [ite_eq_right hm, ite_eq_right hm]
      exact windowScanP_eq h hlev cell1 cell2 counts vs c1 maxcell1 maxcell hmax hst

@[expose] def segmentOfP (ctx : CtxP) (lab cell1 : Nat) (counts values : List Nat) :
    List Nat :=
  values.flatMap fun v =>
    (counts.zipIdx.filter fun p => Nat.beq p.1 v).map fun p =>
      lget ctx lab (Nat.add cell1 p.2)

theorem segmentOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (cell1 : Nat)
    (counts values : List Nat) :
    segmentOfP ctx labP cell1 counts values = segmentOfL lab cell1 counts values := by
  rw [segmentOfP, segmentOfL]
  congr 1
  funext v
  rw [List.filter_congr (fun p _ => ?_)]
  · refine List.map_congr_left fun p _ => ?_
    rcases p with ⟨c, j⟩
    simp [lget_eq h hl]
  · rcases p with ⟨c, j⟩
    exact beq_eq_beq c v

theorem segmentOfP_small {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (labP cell1 : Nat) (counts values : List Nat) :
    Small ctx.w (segmentOfP ctx labP cell1 counts values) := by
  unfold Small
  intro x hx
  rw [segmentOfP, List.mem_flatMap] at hx
  obtain ⟨v, _, hx⟩ := hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, j⟩, _, rfl⟩ := hx
  exact lget_lt h _ _

@[expose] def writeSegmentP (ctx : CtxP) (lab cell1 : Nat) : List Nat → Nat
  | [] => lab
  | x :: rest => writeSegmentP ctx (lset ctx lab cell1 x) (Nat.add cell1 1) rest

theorem writeSegmentP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) :
    ∀ (seg : List Nat), Small ctx.w seg → ∀ {labP : Nat} {lab : List Nat},
      Rep ctx.w ctx.n labP lab → ∀ (cell1 : Nat),
      Rep ctx.w ctx.n (writeSegmentP ctx labP cell1 seg)
        (writeSegmentL lab cell1 seg)
  | [], _, _, _, hl, _ => hl
  | x :: rest, hs, _, _, hl, cell1 => by
    rw [writeSegmentP, writeSegmentL, add_eq]
    exact writeSegmentP_rep h rest (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      (lset_rep h hl cell1 (hs x (List.mem_cons_self ..))) (cell1 + 1)

@[expose] def nontrivialFixP (n cell1 : Nat) (st : RefineStP) : RefineStP :=
  cond (elemK st.active cell1) st
    { st with active := eraseK n (insertK n st.active cell1) st.maxpos }

theorem nontrivialFixP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (cell1 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (nontrivialFixP ctx.n cell1 st) (nontrivialFixL ctxL.n cell1 stL) := by
  rw [nontrivialFixP, nontrivialFixL, elemK_eq, cond_beq_true, hst.active,
    hst.maxpos, eraseK_eq, insertK_eq, h.n]
  rw [h.n] at hst
  rcases Decidable.em (Nat.testBit stL.active cell1 = true) with he | he
  · rw [ite_eq_left he, ite_eq_right (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_left (by simpa using he)]
    exact RepSt.mk' hst.lab hst.ptn
      (by simp [hst.numcells, hst.hint, hst.longcode])

@[expose] def nontrivialCellP (ctx : CtxP) (level workset cell1 cell2 : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.beq cell1 cell2) st
    (let counts := countsOfP ctx st.lab workset cell1 cell2
    let lo := counts.foldl minK (counts.headD 0)
    let hi := counts.foldl maxK (counts.headD 0)
    cond (Nat.beq lo hi)
      { st with longcode := mashK st.longcode (Nat.add lo cell1) }
      (let values := countValuesK counts
      let st' := windowScanP ctx level cell1 cell2 counts values cell1 0 st
      nontrivialFixP ctx.n cell1
        { st' with
          lab := writeSegmentP ctx st'.lab cell1
            (segmentOfP ctx st'.lab cell1 counts values) }))

theorem nontrivialCellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (workset cell1 cell2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (nontrivialCellP ctx level workset cell1 cell2 st)
      (nontrivialCellL ctxL level workset cell1 cell2 stL) := by
  rw [nontrivialCellP, nontrivialCellL, cond_beq]
  rcases Decidable.em (cell1 = cell2) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    simp only [countsOfP_eq h hst.lab, cond_beq, add_eq]
    have hmax : maxK = Nat.max := funext fun a => funext fun b => maxK_eq a b
    have hmin : minK = Nat.min := funext fun a => funext fun b => minK_eq a b
    rw [hmax, hmin]
    rcases Decidable.em ((countsOfL ctxL stL.lab workset cell1 cell2).foldl
        Nat.min ((countsOfL ctxL stL.lab workset cell1 cell2).headD 0) =
        (countsOfL ctxL stL.lab workset cell1 cell2).foldl Nat.max
          ((countsOfL ctxL stL.lab workset cell1 cell2).headD 0)) with hlo | hlo
    · rw [ite_eq_left hlo, ite_eq_left (by simpa using hlo)]
      exact ⟨hst.lab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
        by simp [hst.longcode, mashK_eq]⟩
    · rw [ite_eq_right hlo, ite_eq_right (by simpa using hlo), countValuesK_eq]
      have hscan := windowScanP_eq h hlev cell1 cell2
        (countsOfL ctxL stL.lab workset cell1 cell2)
        (countValues (countsOfL ctxL stL.lab workset cell1 cell2)) cell1 0 (-1)
        (by simp) hst
      refine nontrivialFixP_eq h cell1 ⟨?_, hscan.ptn, hscan.active, hscan.numcells,
        hscan.hint, hscan.maxpos, hscan.longcode⟩
      rw [segmentOfP_eq h hscan.lab]
      exact writeSegmentP_rep h _
        (by rw [← segmentOfP_eq h hscan.lab]; exact segmentOfP_small h _ _ _ _)
        hscan.lab cell1

@[expose] def refineNontrivialGoP (ctx : CtxP) (level workset : Nat) :
    List (Nat × Nat) → RefineStP → RefineStP
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineNontrivialGoP ctx level workset rest
      (nontrivialCellP ctx level workset cell1 cell2 st)

@[expose] def refineNontrivialP (ctx : CtxP) (level split1 split2 : Nat)
    (st : RefineStP) : RefineStP :=
  let workset := worksetOfP ctx st.lab split1 split2
  let st := { st with
    longcode := mashK st.longcode (Nat.add (Nat.sub split2 split1) 1) }
  refineNontrivialGoP ctx level workset (cellsP ctx st.ptn level) st

theorem refineNontrivialGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (workset : Nat) :
    ∀ (cs : List (Nat × Nat)) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineNontrivialGoP ctx level workset cs st)
        (refineNontrivialGoL ctxL level workset cs stL)
  | [], _, _, hst => hst
  | (cell1, cell2) :: rest, _, _, hst => by
    rw [refineNontrivialGoP, refineNontrivialGoL]
    exact refineNontrivialGoP_eq h hlev workset rest
      (nontrivialCellP_eq h hlev workset cell1 cell2 hst)

theorem refineNontrivialP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 split2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineNontrivialP ctx level split1 split2 st)
      (refineNontrivialL ctxL level split1 split2 stL) := by
  rw [refineNontrivialP, refineNontrivialL, worksetOfP_eq h hst.lab]
  simp only [cellsP_eq h hst.ptn, add_eq, sub_eq, mashK_eq]
  exact refineNontrivialGoP_eq h hlev _ _
    ⟨hst.lab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
      by simp [hst.longcode]⟩

@[expose] def refineStepP (ctx : CtxP) (level split1 : Nat) (st : RefineStP) :
    RefineStP :=
  let st := { st with active := eraseK ctx.n st.active split1 }
  let split2 := cellEndP ctx st.ptn level split1
  let st := { st with longcode := mashK st.longcode (Nat.add split1 split2) }
  cond (Nat.beq split1 split2)
    (refineTrivialP ctx level split1 st)
    (refineNontrivialP ctx level split1 split2 st)

theorem refineStepP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineStepP ctx level split1 st)
      (refineStepL ctxL level split1 stL) := by
  rw [refineStepP, refineStepL]
  simp only [cellEndP_eq h hst.ptn, cond_beq, eraseK_eq, mashK_eq, add_eq,
    hst.active, hst.longcode]
  have hst' : RepSt ctx.w ctx.n
      { st with
        active := eraseL ctx.n stL.active split1
        longcode := mash stL.longcode (split1 + cellEndL stL.ptn level split1) }
      { stL with
        active := eraseL ctxL.n stL.active split1
        longcode := mash stL.longcode (split1 + cellEndL stL.ptn level split1) } :=
    ⟨hst.lab, hst.ptn, by rw [h.n], hst.numcells, hst.hint, hst.maxpos, rfl⟩
  rcases Decidable.em (split1 = cellEndL stL.ptn level split1) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact refineTrivialP_eq h hlev split1 hst'
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    exact refineNontrivialP_eq h hlev split1 _ hst'

@[expose] def refineLoopP (ctx : CtxP) (level fuel : Nat) : RefineStP → RefineStP :=
  fuelRec fuel (fun st => st) fun ih st =>
    cond (Nat.blt st.numcells ctx.n)
      (match pickSplitK st.active st.hint with
      | some split1 => ih (refineStepP ctx level split1 st)
      | none => st)
      st

theorem refineLoopP_succ (ctx : CtxP) (level fuel : Nat) (st : RefineStP) :
    refineLoopP ctx level (fuel + 1) st =
      cond (Nat.blt st.numcells ctx.n)
        (match pickSplitK st.active st.hint with
        | some split1 => refineLoopP ctx level fuel (refineStepP ctx level split1 st)
        | none => st)
        st := rfl

theorem refineLoopP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) :
    ∀ (fuel : Nat) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineLoopP ctx level fuel st)
        (refineLoopL ctxL level fuel stL)
  | 0, _, _, hst => hst
  | fuel + 1, st, stL, hst => by
    have hc : (st.numcells < ctx.n) = (stL.numcells < ctxL.n) := by
      rw [hst.numcells, h.n]
    rw [refineLoopP_succ, refineLoopL, cond_blt, pickSplitK_eq, hst.active,
      hst.hint]
    rcases Decidable.em (st.numcells < ctx.n) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left (Eq.mp hc hl)]
      rcases hps : pickSplitL stL.active stL.hint with _ | split1
      · exact hst
      · exact refineLoopP_eq h hlev fuel (refineStepP_eq h hlev split1 hst)
    · rw [ite_eq_right hl, ite_eq_right (fun h' => hl (Eq.mpr hc h'))]
      exact hst

@[expose] def refineP (ctx : CtxP) (level lab ptn active numcells : Nat) :
    RefineStP :=
  let st : RefineStP :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  let st := refineLoopP ctx level (Nat.add (Nat.mul 4 ctx.n) 8) st
  { st with longcode := cleanupK (mashK st.longcode st.numcells) }

theorem refineP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) {labP : Nat} {lab : List Nat}
    (hl : Rep ctx.w ctx.n labP lab) {ptnP : Nat} {ptn : List Nat}
    (hp : Rep ctx.w ctx.n ptnP ptn) (active numcells : Nat) :
    RepSt ctx.w ctx.n (refineP ctx level labP ptnP active numcells)
      (refineL ctxL level lab ptn active numcells) := by
  rw [refineP, refineL]
  simp only [add_eq, mul_eq, cleanupK_eq, mashK_eq]
  rw [show 4 * ctxL.n + 8 = 4 * ctx.n + 8 by rw [h.n]]
  have hloop := refineLoopP_eq h hlev (4 * ctx.n + 8)
    (st := ⟨labP, ptnP, active, numcells, 0, 0, numcells⟩)
    (stL := ⟨lab, ptn, active, numcells, 0, 0, numcells⟩)
    ⟨hl, hp, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hloop.lab, hloop.ptn, hloop.active, hloop.numcells, hloop.hint,
    hloop.maxpos, by simp [hloop.longcode, hloop.numcells]⟩


/-! # Raw list helpers -/

@[expose] def listContainsK : List Nat → Nat → Bool
  | [], _ => false
  | b :: bs, a => cond (Nat.beq a b) true (listContainsK bs a)

theorem listContainsK_eq : ∀ (l : List Nat) (a : Nat),
    listContainsK l a = l.contains a
  | [], _ => rfl
  | b :: bs, a => by
    rw [listContainsK, List.contains_cons, listContainsK_eq bs a, cond_beq]
    rcases Decidable.em (a = b) with h | h <;> simp [h]

@[expose] def listEraseK : List Nat → Nat → List Nat
  | [], _ => []
  | a :: as, b => cond (Nat.beq a b) as (a :: listEraseK as b)

theorem listEraseK_eq : ∀ (l : List Nat) (b : Nat), listEraseK l b = l.erase b
  | [], _ => rfl
  | a :: as, b => by
    rw [listEraseK, List.erase_cons, listEraseK_eq as b, cond_beq]
    rcases Decidable.em (a = b) with h | h <;> simp [h]

/-- `List.isPerm`, raw. -/
@[expose] def isPermK : List Nat → List Nat → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => listContainsK l₂ a && isPermK l₁ (listEraseK l₂ a)

theorem isPermK_eq : ∀ (l₁ l₂ : List Nat), isPermK l₁ l₂ = l₁.isPerm l₂
  | [], _ => rfl
  | a :: l₁, l₂ => by
    rw [isPermK, List.isPerm, listContainsK_eq, listEraseK_eq, isPermK_eq l₁]

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x, x ∈ l → p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..),
      find?_congr l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem map_atD_range {α : Type} (l : List Nat) (f : Nat → α) :
    (List.range l.length).map (fun i => f (atD l i 0)) = l.map f := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [atD_eq_getElem l i (by simpa using h2)]

theorem map_getBang_range {γ : Array Nat} {nn : Nat} (h : γ.size = nn) :
    (List.range nn).map (fun v => γ[v]!) = γ.toList := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, getBang_eq_atD]
  rw [atD_eq_getElem _ i (by simpa using h2)]

/-! # Target cell, breakout, and leaf machinery over packed state -/

@[expose] def discreteAtP (ctx : CtxP) (ptn level : Nat) : Bool :=
  (cellsP ctx ptn level).all fun p => Nat.beq p.1 p.2

theorem discreteAtP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn) (level : Nat) :
    discreteAtP ctx ptnP level = discreteAtL ptn level ctxL.n := by
  rw [discreteAtP, discreteAtL, cellsP_eq h hp]
  simp only [beq_eq_beq]

@[expose] def joinTestP (ctx : CtxP) (lab wset c1 c2 : Nat) : Bool :=
  let counts := countsOfP ctx lab wset c1 c2
  counts.any (fun c => Nat.blt 0 c) &&
    counts.any (fun c => Nat.blt c (popCountK wset))

theorem joinTestP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    (wset c1 c2 : Nat) :
    joinTestP ctx labP wset c1 c2 = joinTestL ctxL lab wset c1 c2 := by
  rw [joinTestP, joinTestL, countsOfP_eq h hl, popCountK_eq]
  simp only [blt_eq_decide]

@[expose] def specBestcellRowP (ctx : CtxP) (lab ptn level : Nat)
    (startArr : List Nat) (workset v2 : Nat) : List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    cond (joinTestP ctx lab workset (atD startArr v1 0)
        (cellEndP ctx ptn level (atD startArr v1 0)))
      (specBestcellRowP ctx lab ptn level startArr workset v2 rest
        ((bucket.set v1 (Nat.add (atD bucket v1 0) 1)).set v2
          (Nat.add (atD bucket v2 0) 1)))
      (specBestcellRowP ctx lab ptn level startArr workset v2 rest bucket)

theorem specBestcellRowP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) (startArr : List Nat) (workset v2 : Nat) :
    ∀ (vs bucket : List Nat),
      specBestcellRowP ctx labP ptnP level startArr workset v2 vs bucket =
        specBestcellRowL ctxL lab ptn level startArr workset v2 vs bucket
  | [], _ => rfl
  | v1 :: rest, bucket => by
    rw [specBestcellRowP, specBestcellRowL, joinTestP_eq h hl, cellEndP_eq h hp,
      cond_beq_true]
    simp only [add_eq]
    rcases Decidable.em (joinTestL ctxL lab workset (atD startArr v1 0)
        (cellEndL ptn level (atD startArr v1 0)) = true) with hj | hj
    · rw [ite_eq_left hj, ite_eq_left hj,
        specBestcellRowP_eq h hl hp level startArr workset v2 rest]
    · rw [ite_eq_right hj, ite_eq_right hj,
        specBestcellRowP_eq h hl hp level startArr workset v2 rest]

@[expose] def specBestcellRowsP (ctx : CtxP) (lab ptn level : Nat)
    (startArr : List Nat) : List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    specBestcellRowsP ctx lab ptn level startArr rest
      (specBestcellRowP ctx lab ptn level startArr
        (worksetOfP ctx lab (atD startArr v2 0)
          (cellEndP ctx ptn level (atD startArr v2 0)))
        v2 (List.range v2) bucket)

theorem specBestcellRowsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) (startArr : List Nat) : ∀ (vs bucket : List Nat),
      specBestcellRowsP ctx labP ptnP level startArr vs bucket =
        specBestcellRowsL ctxL lab ptn level startArr vs bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [specBestcellRowsP, specBestcellRowsL, worksetOfP_eq h hl, cellEndP_eq h hp,
      specBestcellRowP_eq h hl hp, specBestcellRowsP_eq h hl hp level startArr rest]

@[expose] def argmaxLoopK (bucket : List Nat) : List Nat → Nat → Nat → Nat
  | [], v1, _ => v1
  | i :: rest, v1, v2 =>
    cond (Nat.blt v2 (atD bucket i 0))
      (argmaxLoopK bucket rest i (atD bucket i 0))
      (argmaxLoopK bucket rest v1 v2)

theorem argmaxLoopK_eq (bucket : List Nat) : ∀ (vs : List Nat) (v1 v2 : Nat),
    argmaxLoopK bucket vs v1 v2 = argmaxLoopL bucket vs v1 v2
  | [], _, _ => rfl
  | i :: rest, v1, v2 => by
    rw [argmaxLoopK, argmaxLoopL, cond_blt]
    rcases Decidable.em (v2 < atD bucket i 0) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl, argmaxLoopK_eq bucket rest]
    · rw [ite_eq_right hl, ite_eq_right hl, argmaxLoopK_eq bucket rest]

@[expose] def specBestcellP (ctx : CtxP) (lab ptn level : Nat) : Nat :=
  let starts := ((cellsP ctx ptn level).filter fun p => !Nat.beq p.1 p.2).map (·.1)
  let nnt := starts.length
  cond (Nat.beq nnt 0) ctx.n
    (let bucket := specBestcellRowsP ctx lab ptn level starts
      (List.range' 1 (Nat.sub nnt 1)) (List.replicate nnt 0)
    atD starts (argmaxLoopK bucket (List.range' 1 (Nat.sub nnt 1)) 0 (atD bucket 0 0)) 0)

theorem specBestcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn) (level : Nat) :
    specBestcellP ctx labP ptnP level = specBestcellL ctxL lab ptn level := by
  rw [specBestcellP, specBestcellL, cellsP_eq h hp]
  have hf : (fun p : Nat × Nat => !Nat.beq p.1 p.2) = fun x => decide (x.1 ≠ x.2) :=
    funext fun p => by rw [beq_eq_decide, decide_not]
  simp only [cond_beq, sub_eq, specBestcellRowsP_eq h hl hp, argmaxLoopK_eq, h.n,
    beq_iff_eq, hf]

/-- The start of the first nontrivial cell, `0` if every cell is a
singleton: the target-cell rule below the `tcLevel` cutoff. -/
@[expose] def firstNontrivialP : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => cond (Nat.beq p.1 p.2) (firstNontrivialP rest) p.1

@[expose] def specTargetcellP (ctx : CtxP) (lab ptn level tcLevel : Nat) : Nat :=
  cond (Nat.ble level tcLevel) (specBestcellP ctx lab ptn level)
    (firstNontrivialP (cellsP ctx ptn level))

theorem specTargetcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level tcLevel : Nat) :
    specTargetcellP ctx labP ptnP level tcLevel =
      specTargetcellL ctxL lab ptn level tcLevel := by
  rw [specTargetcellP, specTargetcellL, cellsP_eq h hp, cond_ble]
  rcases Decidable.em (level ≤ tcLevel) with hle | hle
  · rw [ite_eq_left hle, ite_eq_left hle, specBestcellP_eq h hl hp]
  · rw [ite_eq_right hle, ite_eq_right hle]
    generalize cellsL ptn level ctxL.n = cs
    induction cs with
    | nil => rfl
    | cons p rest ih =>
      rcases p with ⟨c1, c2⟩
      rw [firstNontrivialP, List.find?_cons, cond_beq]
      rcases Decidable.em (c1 = c2) with he | he
      · rw [ite_eq_left he, ih]
        simp [he]
      · rw [ite_eq_right he]
        simp [he]

@[expose] def specMaketargetcellP (ctx : CtxP) (lab ptn level tcLevel : Nat) :
    Nat × Nat × Nat :=
  let i := specTargetcellP ctx lab ptn level tcLevel
  let j := cellEndP ctx ptn level (Nat.add i 1)
  (i, worksetOfP ctx lab i j, Nat.add (Nat.sub j i) 1)

theorem specMaketargetcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level tcLevel : Nat) :
    specMaketargetcellP ctx labP ptnP level tcLevel =
      specMaketargetcellL ctxL lab ptn level tcLevel := by
  rw [specMaketargetcellP, specMaketargetcellL]
  simp only [specTargetcellP_eq h hl hp, cellEndP_eq h hp, worksetOfP_eq h hl,
    add_eq, sub_eq]

@[expose] def breakoutGoP (ctx : CtxP) (tv fuel : Nat) : Nat → Nat → Nat → Nat :=
  fuelRec fuel (fun lab _ _ => lab) fun ih lab i prev =>
    let next := lget ctx lab i
    let lab := lset ctx lab i prev
    cond (Nat.beq next tv) lab (ih lab (Nat.add i 1) next)

theorem breakoutGoP_succ (ctx : CtxP) (tv fuel lab i prev : Nat) :
    breakoutGoP ctx tv (fuel + 1) lab i prev =
      (let next := lget ctx lab i
      let lab := lset ctx lab i prev
      cond (Nat.beq next tv) lab (breakoutGoP ctx tv fuel lab (Nat.add i 1) next)) := rfl

theorem breakoutGoP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (tv : Nat) :
    ∀ (fuel : Nat) {labP : Nat} {lab : List Nat}, Rep ctx.w ctx.n labP lab →
      ∀ (i prev : Nat), prev < 2 ^ ctx.w →
      Rep ctx.w ctx.n (breakoutGoP ctx tv fuel labP i prev)
        (breakoutGoL tv fuel lab i prev)
  | 0, _, _, hl, _, _, _ => hl
  | fuel + 1, labP, lab, hl, i, prev, hprev => by
    rw [breakoutGoP_succ, breakoutGoL]
    simp only [add_eq]
    have hn : lget ctx labP i = atD lab i 0 := lget_eq h hl i
    rw [hn, cond_beq]
    rcases Decidable.em (atD lab i 0 = tv) with he | he
    · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
      exact lset_rep h hl i hprev
    · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
      exact breakoutGoP_rep h tv fuel (lset_rep h hl i hprev) (i + 1) _ (hl.small.atD i)

@[expose] def breakoutP (ctx : CtxP) (lab ptn level tc tv : Nat) : Nat × Nat × Nat :=
  (breakoutGoP ctx tv (Nat.add ctx.n 1) lab tc tv, lset ctx ptn tc level,
    insertK ctx.n 0 tc)

theorem breakoutP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (tc : Nat) {tv : Nat}
    (htv : tv < 2 ^ ctx.w) :
    Rep ctx.w ctx.n (breakoutP ctx labP ptnP level tc tv).1
        (breakoutL ctxL.n lab ptn level tc tv).1 ∧
      Rep ctx.w ctx.n (breakoutP ctx labP ptnP level tc tv).2.1
        (breakoutL ctxL.n lab ptn level tc tv).2.1 ∧
      (breakoutP ctx labP ptnP level tc tv).2.2 =
        (breakoutL ctxL.n lab ptn level tc tv).2.2 := by
  rw [breakoutP, breakoutL]
  refine ⟨?_, lset_rep h hp tc hlev, (insertK_eq ctx.n 0 tc).trans (by rw [h.n])⟩
  rw [hl.len, add_eq]
  exact breakoutGoP_rep h tv (ctx.n + 1) hl tc tv htv

@[expose] def segNP (ctx : CtxP) (lab lo len : Nat) : List Nat :=
  mapRange len fun o => lget ctx lab (Nat.add lo o)

theorem segNP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (lo len : Nat) :
    segNP ctx labP lo len = segNL lab lo len := by
  rw [segNP, segNL, mapRange_eq]
  simp only [lget_eq h hl, add_eq]

/-- The packed image of a packed labelling under a packed permutation. -/
@[expose] def mapGammaP (ctx : CtxP) (γP lab : Nat) : Nat :=
  pack ctx.w (mapRange ctx.n fun i => lget ctx γP (lget ctx lab i))

theorem mapGammaP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {γP : Nat} {γl : List Nat} (hg : Rep ctx.w ctx.n γP γl)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    Rep ctx.w ctx.n (mapGammaP ctx γP labP) (lab.map fun v => atD γl v 0) := by
  rw [mapGammaP, mapRange_eq]
  have hs : Small ctx.w ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)) := by
    unfold Small
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact lget_lt h _ _
  have hlen : ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)).length =
      ctx.n := by simp
  have heq : ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)) =
      lab.map fun v => atD γl v 0 := by
    simp only [lget_eq h hg, lget_eq h hl]
    rw [← hl.len]
    exact map_atD_range lab fun v => atD γl v 0
  exact ⟨by rw [← heq]; exact hlen, by rw [← heq]; exact hs, by rw [heq]⟩

@[expose] def checkCellsPermP (ctx : CtxP) (ptn lab₁ lab₂' level : Nat) : Bool :=
  (cellsP ctx ptn level).all fun p =>
    isPermK (segNP ctx lab₁ p.1 (Nat.sub (Nat.add p.2 1) p.1))
      (segNP ctx lab₂' p.1 (Nat.sub (Nat.add p.2 1) p.1))

theorem checkCellsPermP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    {lab₁P : Nat} {lab₁ : List Nat} (h1 : Rep ctx.w ctx.n lab₁P lab₁)
    {lab₂P : Nat} {lab₂ : List Nat} (h2 : Rep ctx.w ctx.n lab₂P lab₂) (level : Nat) :
    checkCellsPermP ctx ptnP lab₁P lab₂P level =
      checkCellsPermL ptn lab₁ lab₂ level ctxL.n := by
  rw [checkCellsPermP, checkCellsPermL, cellsP_eq h hp]
  simp only [isPermK_eq, segNP_eq h h1, segNP_eq h h2, add_eq, sub_eq]

theorem invPermGoL_eq_foldl (lab : List Nat) : ∀ (idx inv : List Nat),
    invPermGoL lab idx inv = idx.foldl (fun inv i => inv.set (atD lab i 0) i) inv
  | [], _ => rfl
  | i :: rest, inv => by
    rw [invPermGoL, List.foldl_cons, invPermGoL_eq_foldl lab rest]

theorem invPermFold_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    ∀ (idx : List Nat), (∀ i, i ∈ idx → i < 2 ^ ctx.w) →
      ∀ {invP : Nat} {inv : List Nat}, Rep ctx.w ctx.n invP inv →
      Rep ctx.w ctx.n (idx.foldl (fun inv i => lset ctx inv (lget ctx labP i) i) invP)
        (idx.foldl (fun inv i => inv.set (atD lab i 0) i) inv)
  | [], _, _, _, hi => hi
  | i :: rest, hidx, _, _, hi => by
    rw [List.foldl_cons, List.foldl_cons, lget_eq h hl]
    exact invPermFold_rep h hl rest (fun j hj => hidx j (List.mem_cons_of_mem _ hj))
      (lset_rep h hi _ (hidx i (List.mem_cons_self ..)))

@[expose] def invPermP (ctx : CtxP) (lab : Nat) : Nat :=
  iterUp ctx.n (fun i inv => lset ctx inv (lget ctx lab i) i) 0

theorem invPermP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    Rep ctx.w ctx.n (invPermP ctx labP) (invPermL lab) := by
  rw [invPermP, invPermL, hl.len, iterUp_eq_foldl, invPermGoL_eq_foldl]
  refine invPermFold_rep h hl _ (fun i hi => ?_) (Rep.replicate ctx.w ctx.n)
  have := List.mem_range.mp hi
  have := h.nlt
  omega

@[expose] def permsetP (ctx : CtxP) (s perm : Nat) : Nat :=
  iterUp ctx.n (fun v acc => cond (elemK s v) (insertK ctx.n acc (lget ctx perm v)) acc) 0

theorem permsetP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {permP : Nat} {perm : List Nat} (hp : Rep ctx.w ctx.n permP perm) (s : Nat) :
    permsetP ctx s permP = permsetL s perm ctxL.n := by
  rw [permsetP, permsetL, h.n, iterUp_eq_foldl]
  congr 1
  funext acc v
  rw [elemK_eq, cond_beq_true, insertK_eq, lget_eq h hp]

@[expose] def leafRowsP (ctx : CtxP) (lab : Nat) : List Nat :=
  let inv := invPermP ctx lab
  mapRange ctx.n fun i => permsetP ctx (rowP ctx (lget ctx lab i)) inv

theorem leafRowsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    leafRowsP ctx labP = leafRowsL ctxL lab := by
  rw [leafRowsP, leafRowsL, mapRange_eq]
  simp only [permsetP_eq h (invPermP_rep h hl), rowP_eq h, lget_eq h hl, h.n]

/-! # Automorphism validation over packed state -/

@[expose] def imageP (σ : Nat → Nat) (n s : Nat) : Nat :=
  iterUp n (fun v t => cond (elemK s v) (insertK n t (σ v)) t) 0

theorem imageP_eq (σ : Nat → Nat) (n s : Nat) : imageP σ n s = imageL n σ s := by
  rw [imageP, imageL, iterUp_eq_foldl]
  congr 1
  funext t v
  rw [elemK_eq, cond_beq_true, insertK_eq]

/-- A candidate permutation array has `n` entries, all vertices. -/
@[expose] def gammaOkP (ctx : CtxP) (γl : List Nat) : Bool :=
  Nat.beq γl.length ctx.n && γl.all fun v => Nat.blt v ctx.n

theorem gammaOkP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {γl : List Nat} (hok : gammaOkP ctx γl = true) :
    Rep ctx.w ctx.n (pack ctx.w γl) γl := by
  rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hok
  refine ⟨hok.1, fun x hx => ?_, rfl⟩
  have := Nat.blt_eq.mp (hok.2 x hx)
  have := h.nlt
  omega

@[expose] def checkAutomP (ctx : CtxP) (γ : Array Nat) : Bool :=
  let γl := γ.toList
  gammaOkP ctx γl &&
    (let γP := pack ctx.w γl
    isPermK γl (List.range ctx.n) &&
      allRange ctx.n fun v =>
        Nat.beq (rowP ctx (lget ctx γP v))
          (imageP (fun w => lget ctx γP w) ctx.n (rowP ctx v)))

theorem gammaOkP_of_checkAutom {ctx : CtxP} {nn : Nat} {g : List Nat}
    (h : CtxRep ctx ⟨nn, g⟩) {γ : Array Nat}
    (hc : checkAutomL g nn γ = true) : gammaOkP ctx γ.toList = true := by
  rw [checkAutomL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hsize, hsmall⟩, _⟩, _⟩ := hc
  rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Array.length_toList,
    hsize, h.n]
  refine ⟨rfl, fun x hx => ?_⟩
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Array.length_toList, hsize] at hi
  have := of_decide_eq_true (hsmall i (List.mem_range.mpr hi))
  rw [getBang_eq_atD, atD_eq_getElem _ i (by simpa [hsize] using hi)] at this
  exact Nat.blt_eq.mpr this

theorem checkAutomP_eq {ctx : CtxP} {nn : Nat} {g : List Nat}
    (h : CtxRep ctx ⟨nn, g⟩) (γ : Array Nat) :
    checkAutomP ctx γ = checkAutomL g nn γ := by
  have hrow : ∀ v, rowP ctx v = atD g v 0 := fun v => rowP_eq h v
  rcases hok : gammaOkP ctx γ.toList with _ | _
  · rw [checkAutomP]
    simp only [hok, Bool.false_and]
    rcases hc : checkAutomL g nn γ with _ | _
    · rfl
    · rw [gammaOkP_of_checkAutom h hc] at hok
      cases hok
  · have hrep := gammaOkP_rep h hok
    have hok' := hok
    rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true,
      Array.length_toList] at hok'
    have hsize : γ.size = nn := by rw [hok'.1, h.n]
    have hget : ∀ v, lget ctx (pack ctx.w γ.toList) v = γ[v]! := fun v => by
      rw [lget_eq h hrep, getBang_eq_atD]
    have hbound : ∀ v, v ∈ List.range nn → (γ[v]! : Nat) < nn := fun v hv => by
      have hmem : (γ[v]! : Nat) ∈ γ.toList := by
        rw [getBang_eq_atD, atD_eq_getElem _ v (by
          rw [Array.length_toList, hsize]; exact List.mem_range.mp hv)]
        exact List.getElem_mem _
      have := Nat.blt_eq.mp (hok'.2 _ hmem)
      rw [h.n] at this
      exact this
    rw [checkAutomP, checkAutomL, Bool.eq_iff_iff]
    simp only [hok, Bool.true_and, Bool.and_eq_true, hget, hrow, isPermK_eq,
      imageP_eq, allRange_eq, h.n, map_getBang_range hsize, beq_iff_eq,
      Nat.beq_eq, List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hperm, himgs⟩
      exact ⟨⟨⟨hsize, hbound⟩, hperm⟩, himgs⟩
    · rintro ⟨⟨_, hperm⟩, himgs⟩
      exact ⟨hperm, himgs⟩

theorem validGammasL_sound {g : List Nat} {nn : Nat} {cert : CertNode} {γ : Array Nat}
    (h : γ ∈ validGammasL g nn cert) : checkAutomL g nn γ = true :=
  (List.mem_filter.mp h).2

@[expose] def validGammasP (ctx : CtxP) (cert : CertNode) : List Nat :=
  ((certGammas (Nat.add ctx.n 2) cert []).filter (checkAutomP ctx)).map
    fun γ => pack ctx.w γ.toList

theorem validGammasP_eq {ctx : CtxP} {nn : Nat} {g : List Nat}
    (h : CtxRep ctx ⟨nn, g⟩) (cert : CertNode) :
    validGammasP ctx cert = (validGammasL g nn cert).map fun γ => pack ctx.w γ.toList := by
  rw [validGammasP, validGammasL, add_eq, h.n]
  congr 1
  exact List.filter_congr fun γ _ => checkAutomP_eq h γ

/-- Membership of a certificate's permutation among the validated
generators, on packed numbers: the array must have `n` vertex entries
(so the packing is faithful) and its packing must appear. -/
@[expose] def containsGammaP (ctx : CtxP) (vgens : List Nat) (γ : Array Nat) : Bool :=
  gammaOkP ctx γ.toList && vgens.any (Nat.beq (pack ctx.w γ.toList))

theorem containsGamma_of_mem : ∀ {vgens : List (Array Nat)} {γ : Array Nat},
    γ ∈ vgens → containsGamma vgens γ = true
  | g :: rest, γ, hmem => by
    rw [containsGamma, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl (by rw [gammaEq]; exact beq_self_eq_true _)
    · exact Or.inr (containsGamma_of_mem hmem)

theorem containsGammaP_eq {ctx : CtxP} {nn : Nat} {g : List Nat}
    (h : CtxRep ctx ⟨nn, g⟩) (cert : CertNode) (γ : Array Nat) :
    containsGammaP ctx (validGammasP ctx cert) γ =
      containsGamma (validGammasL g nn cert) γ := by
  rw [Bool.eq_iff_iff, containsGammaP, validGammasP_eq h, Bool.and_eq_true,
    List.any_eq_true]
  constructor
  · rintro ⟨hok, x, hx, hbeq⟩
    rw [List.mem_map] at hx
    obtain ⟨g', hg', rfl⟩ := hx
    have hc := validGammasL_sound hg'
    have hrep := gammaOkP_rep h hok
    have hrep' := gammaOkP_rep h (gammaOkP_of_checkAutom h hc)
    have heq : γ.toList = g'.toList :=
      pack_injective ctx.w _ _ hrep.small hrep'.small (by rw [hrep.len, hrep'.len])
        (Nat.eq_of_beq_eq_true hbeq)
    rw [Array.toList_inj] at heq
    rw [heq]
    exact containsGamma_of_mem hg'
  · intro hc
    have hmem := containsGamma_mem hc
    refine ⟨gammaOkP_of_checkAutom h (validGammasL_sound hmem), pack ctx.w γ.toList,
      List.mem_map.mpr ⟨γ, hmem, rfl⟩, Nat.beq_refl _⟩

/-! # The certificate replay over packed state -/

@[expose] def checkNodeP (ctx : CtxP) (tcLevel : Nat) (brows : List Nat)
    (vgens : List Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → CertNode → List Nat → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes =>
    match bcodes with
    | [] => none
    | bc :: brest =>
      let rs := refineP ctx level lab ptn active numcells
      match cert with
      | .autom _ _ => none
      | .codePrune => cond (Nat.blt rs.longcode bc) (some false) none
      | .leaf =>
        cond (Nat.blt rs.longcode bc) (some false)
          (cond (Nat.beq rs.longcode bc)
            (cond (discreteAtP ctx rs.ptn level)
              (match keyCmpL
                ⟨[rs.longcode, codeSentinel], leafRowsP ctx rs.lab⟩
                ⟨bc :: brest, brows⟩ with
              | .gt => none
              | .eq => some true
              | .lt => some false)
              none)
            none)
      | .node children =>
        cond (Nat.blt rs.longcode bc) (some false)
          (cond (Nat.beq rs.longcode bc)
            (cond (discreteAtP ctx rs.ptn level) none
              (let tcr := specMaketargetcellP ctx rs.lab rs.ptn level tcLevel
              cond (Nat.beq children.length tcr.2.2)
                ((children.zipIdx 0).foldl
                  (fun acc (co : CertNode × Nat) =>
                    match acc with
                    | none => none
                    | some a =>
                      let br := breakoutP ctx rs.lab rs.ptn (Nat.add level 1) tcr.1
                        (lget ctx rs.lab (Nat.add tcr.1 co.2))
                      match
                        match co.1 with
                        | .autom o' γ =>
                          cond (Nat.blt o' co.2 &&
                              containsGammaP ctx vgens γ &&
                              checkCellsPermP ctx br.2.1
                                (breakoutP ctx rs.lab rs.ptn (Nat.add level 1)
                                  tcr.1 (lget ctx rs.lab (Nat.add tcr.1 o'))).1
                                (mapGammaP ctx (pack ctx.w γ.toList) br.1)
                                (Nat.add level 1))
                            (some false) none
                        | _ =>
                          checkNodeP ctx tcLevel brows vgens fuel (Nat.add level 1)
                            br.1 br.2.1 br.2.2 (Nat.add rs.numcells 1) co.1 brest
                      with
                      | none => none
                      | some a' => some (a || a'))
                  (some false))
                none))
            none)
  termination_by structural fuel => fuel

theorem checkNodeP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (tcLevel : Nat) (brows : List Nat) {vgensP : List Nat}
    {vgens : List (Array Nat)}
    (hcont : ∀ γ, containsGammaP ctx vgensP γ = containsGamma vgens γ) :
    ∀ (fuel level : Nat), level + fuel ≤ ctx.n + 1 →
      ∀ {labP : Nat} {lab : List Nat}, Rep ctx.w ctx.n labP lab →
      ∀ {ptnP : Nat} {ptn : List Nat}, Rep ctx.w ctx.n ptnP ptn →
      ∀ (active numcells : Nat) (cert : CertNode) (bcodes : List Nat),
      checkNodeP ctx tcLevel brows vgensP fuel level labP ptnP active numcells
        cert bcodes =
      checkNodeL ctxL tcLevel brows vgens fuel level lab ptn active numcells
        cert bcodes
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, level, hlev, labP, lab, hl, ptnP, ptn, hp, active, numcells, cert,
      bcodes => by
    have hlev1 : level < 2 ^ ctx.w := by have := h.nlt; omega
    have hlev2 : level + 1 < 2 ^ ctx.w := by have := h.nlt; omega
    have hrs := refineP_eq h hlev1 hl hp active numcells
    cases bcodes with
    | nil => rfl
    | cons bc brest =>
      have hcode : (refineP ctx level labP ptnP active numcells).longcode =
          (refineL ctxL level lab ptn active numcells).longcode := hrs.longcode
      have hdisc := discreteAtP_eq h hrs.ptn level
      rcases hcmp : compare (refineL ctxL level lab ptn active numcells).longcode bc
        with _ | _ | _
      · -- lt
        have hlt := Nat.compare_eq_lt.mp hcmp
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            true := by rw [blt_eq_decide, decide_eq_true hlt]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp, ite_true]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp]
        | node children =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp]
      · -- eq
        have heq := Nat.compare_eq_eq.mp hcmp
        have hnlt : ¬ (refineL ctxL level lab ptn active numcells).longcode < bc := by
          omega
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [blt_eq_decide, decide_eq_false hnlt]
        have hbeq : Nat.beq (refineL ctxL level lab ptn active numcells).longcode bc =
            true := by rw [beq_eq_decide, decide_eq_true heq]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_false, hcmp, reduceCtorEq, ite_false]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, Bool.cond_true, hcmp, hdisc,
            leafRowsP_eq h hrs.lab]
          rw [cond_beq_true]
          congr 1
        | node children =>
          have hfold : ∀ (rsLabP rsPtnP : Nat) (rsLab rsPtn : List Nat),
              Rep ctx.w ctx.n rsLabP rsLab → Rep ctx.w ctx.n rsPtnP rsPtn →
              ∀ (tc m : Nat) (cs : List (CertNode × Nat)) (acc : Option Bool),
              cs.foldl
                (fun acc (co : CertNode × Nat) =>
                  match acc with
                  | none => none
                  | some a =>
                    match
                      match co.1 with
                      | .autom o' γ =>
                        cond (Nat.blt o' co.2 &&
                            containsGammaP ctx vgensP γ &&
                            checkCellsPermP ctx
                              (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                                (lget ctx rsLabP (Nat.add tc co.2))).2.1
                              (breakoutP ctx rsLabP rsPtnP (Nat.add level 1)
                                tc (lget ctx rsLabP (Nat.add tc o'))).1
                              (mapGammaP ctx (pack ctx.w γ.toList)
                                (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                                  (lget ctx rsLabP (Nat.add tc co.2))).1)
                              (Nat.add level 1))
                          (some false) none
                      | _ =>
                        checkNodeP ctx tcLevel brows vgensP fuel (Nat.add level 1)
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).1
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).2.1
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).2.2
                          (Nat.add m 1) co.1 brest
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
                            checkCellsPermL
                              (breakoutL ctxL.n rsLab rsPtn (level + 1) tc
                                (atD rsLab (tc + co.2) 0)).2.1
                              (breakoutL ctxL.n rsLab rsPtn (level + 1)
                                tc (atD rsLab (tc + o') 0)).1
                              ((breakoutL ctxL.n rsLab rsPtn (level + 1) tc
                                (atD rsLab (tc + co.2) 0)).1.map
                                fun w => atD γ.toList w 0)
                              (level + 1) ctxL.n then
                          some false
                        else
                          none
                      | _ =>
                        checkNodeL ctxL tcLevel brows vgens fuel (level + 1)
                          (breakoutL ctxL.n rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).1
                          (breakoutL ctxL.n rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).2.1
                          (breakoutL ctxL.n rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).2.2
                          (m + 1) co.1 brest
                    with
                    | none => none
                    | some a' => some (a || a')) acc := by
            intro rsLabP rsPtnP rsLab rsPtn hrl hrp tc m cs
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
                have hbr := breakoutP_eq h hrl hrp hlev2 tc (lget_lt h rsLabP (tc + o))
                rw [lget_eq h hrl] at hbr
                obtain ⟨hbr1, hbr2, hbr3⟩ := hbr
                cases c with
                | leaf =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | codePrune =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | node ch =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | autom o' γ =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hcont γ, blt_eq_decide]
                  rcases hg : containsGamma vgens γ with _ | _
                  · simp
                  · have hok : gammaOkP ctx γ.toList = true := by
                      have := hcont γ
                      rw [hg, containsGammaP, Bool.and_eq_true] at this
                      exact this.1
                    have hγ := gammaOkP_rep h hok
                    have hbr' := breakoutP_eq h hrl hrp hlev2 tc
                      (lget_lt h rsLabP (tc + o'))
                    rw [lget_eq h hrl] at hbr'
                    rw [checkCellsPermP_eq h hbr2 hbr'.1 (mapGammaP_rep h hγ hbr1),
                      cond_beq_true]
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, Bool.cond_true, hcmp, hdisc,
            specMaketargetcellP_eq h hrs.lab hrs.ptn, hrs.numcells]
          rw [cond_beq_true]
          congr 1
          rw [cond_beq]
          congr 1
          exact hfold _ _ _ _ hrs.lab hrs.ptn _ _ (children.zipIdx 0) (some false)
      · -- gt
        have hgt := Nat.compare_eq_gt.mp hcmp
        have hnlt : ¬ (refineL ctxL level lab ptn active numcells).longcode < bc := by
          omega
        have hne : ¬ (refineL ctxL level lab ptn active numcells).longcode = bc := by
          omega
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [blt_eq_decide, decide_eq_false hnlt]
        have hbeq : Nat.beq (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [beq_eq_decide, decide_eq_false hne]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_false, hcmp, reduceCtorEq, ite_false]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, hcmp]
        | node children =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, hcmp]
  termination_by structural fuel => fuel


/-! # The negative kernel obligation over packed state -/
end Hex.GraphIso.Nauty
namespace Hex.GraphIso

open Nauty

variable {n k : Nat}

/-! # The negative kernel obligation

The obligation is stated over the rows tied as one packed number and
proven equal to `Nauty.checkKey` through two internal layers: the rows
rebuilt from the tied flat literal (`checkKeyFlat`), and the whole
replay over list state (`checkKeyLit`). -/

/-- `Nauty.checkKey` with the adjacency rows rebuilt from a flat
literal instead of forcing `rowsOf`. -/
private def checkKeyFlat (G : Colored n k) (flat : List Bool)
    (cert : Nauty.CertNode) (B : Nauty.Key n) : Bool :=
  if n == 0 then
    B.codes == [] && B.rows == []
  else
    Nauty.checkNode { g := rowsOfFlat n flat } 100 B.rows
      (Nauty.validGammas (rowsOfFlat n flat) cert) n 1
      (Nauty.initialPartition G).1
      (Nauty.initPtn n (n + 2) (Nauty.initialPartition G).2)
      (Nauty.initActive n (Nauty.initialPartition G).2)
      (Nauty.initialPartition G).2.length cert B.codes = some true

private theorem checkKeyFlat_eq (G : Colored n k) (cert : Nauty.CertNode)
    (B : Nauty.Key n) :
    checkKeyFlat G G.graph.adjMatrix.data.toList cert B =
      Nauty.checkKey G cert B := by
  rw [checkKeyFlat, Nauty.checkKey, rowsOfFlat_eq_rowsOf]

/-- `checkKeyFlat` with list state end to end: the rows are rebuilt
once from the tied flat literal as bitsets and the whole replay walks
bare lists. -/
private def checkKeyLit (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (K : Kernel.Key) : Bool :=
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
private theorem ctxL_flatRows (flat : List Bool) :
    (⟨n, (flatRows n flat).toList⟩ : CtxL) = Ctx.toL { g := rowsOfFlat n flat } := by
  rw [Ctx.toL, toNat_rowsOfFlat]

private theorem checkKeyLit_eq (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (K : Kernel.Key) (h : ∀ r ∈ K.rows, r < 2 ^ n) :
    checkKeyLit G flat cert K = checkKeyFlat G flat cert (K.toKey n) := by
  have hall : K.rows.all (fun r => r < 2 ^ n) = true :=
    List.all_eq_true.mpr fun r hr => decide_eq_true (h r hr)
  rw [checkKeyLit, hall, Bool.true_and, checkKeyFlat]
  have hrows : K.rows = ((K.toKey n).rows).map VSet.toNat :=
    (congrArg Kernel.Key.rows (toL_toKey h)).symm
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

private theorem mem_toList_lt {a : Array Nat} {b : Nat}
    (h : ∀ i, i < a.size → a[i]! < b) : ∀ x, x ∈ a.toList → x < b := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Array.length_toList] at hi
  have := h i hi
  rw [getBang_eq_atD, atD_eq_getElem _ i (by simpa using hi)] at this
  exact this

/-- The field width of the packed replay on `n` vertices: positions,
vertices, the initial partition's infinity `n + 2`, and every level
the replay fuel of `n` reaches fit a field. -/
@[expose] def initW (n : Nat) : Nat := Nat.log2 (n + 2) + 1

/-- The packed context of the replay on `n` vertices with packed rows
`rows`. -/
@[expose] def initCtx (n rows : Nat) : CtxP :=
  ⟨n, initW n, 2 ^ initW n - 1, rows, 2 ^ n - 1⟩

/-- The initial packed labelling of a coloured graph. -/
@[expose] def initLabP (G : Colored n k) : Nat :=
  pack (initW n) (initialPartition G).1.toList

/-- The initial packed partition of a coloured graph. -/
@[expose] def initPtnP (G : Colored n k) : Nat :=
  pack (initW n) (initPtn n (n + 2) (initialPartition G).2).toList

theorem initW_lt (n : Nat) : n + 2 < 2 ^ initW n := Nat.lt_log2_self

/-- The correspondences of the initial packed state with the list state
the internal replay layer uses. -/
theorem initRep (G : Colored n k) (flat : List Bool) (hn0 : 0 < n) :
    CtxRep (initCtx n (pack n (flatRows n flat).toList))
        ⟨n, (flatRows n flat).toList⟩ ∧
      Rep (initW n) n (initLabP G) (initialPartition G).1.toList ∧
      Rep (initW n) n (initPtnP G)
        (initPtn n (n + 2) (initialPartition G).2).toList := by
  have hok := initial_nodeOk G hn0
  have hw := initW_lt n
  refine ⟨{ n := rfl, m := rfl, rm := rfl, g := ?_, nlt := hw }, ?_, ?_⟩
  · refine ⟨?_, flatRows_small n flat, rfl⟩
    show (flatRows n flat).toList.length = n
    rw [Array.length_toList, size_flatRows]
  · exact ⟨by rw [Array.length_toList, hok.labSize],
      fun x hx => Nat.lt_trans (mem_toList_lt hok.labOk x hx) (by omega), rfl⟩
  · refine ⟨by rw [Array.length_toList, hok.ptnSize], fun x hx => ?_, rfl⟩
    rw [List.mem_iff_getElem] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have hv := hok.vals q
    rw [getBang_eq_atD, atD_eq_getElem _ q hq] at hv
    omega

namespace Kernel

/-- The negative route's kernel obligation: the certificate replayed
over packed state, with the rows packed once from the tied adjacency
matrix (`Kernel.packRows`) and the labelling and partition packed with
the field width `initW n`. -/
@[expose] def checkKey (G : Colored n k) (rows : Nat)
    (cert : CertNode) (K : Key) : Bool :=
  K.rows.all (fun r => r < 2 ^ n) &&
  if n == 0 then
    K.codes == [] && K.rows == []
  else
    let ctx := initCtx n rows
    checkNodeP ctx 100 K.rows (validGammasP ctx cert) n 1
      (initLabP G) (initPtnP G) (initActive n (initialPartition G).2).toNat
      (initialPartition G).2.length cert K.codes = some true

private theorem checkKey_eq_lit (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (K : Key) :
    checkKey G (packRows n flat) cert K = checkKeyLit G flat cert K := by
  rw [checkKey, checkKeyLit]
  congr 1
  rcases Decidable.em (n = 0) with hn | hn
  · rw [ite_eq_left (by simpa using hn), ite_eq_left (by simpa using hn)]
  · rw [ite_eq_right (by simpa using hn), ite_eq_right (by simpa using hn)]
    dsimp only
    rw [packRows_eq]
    obtain ⟨hctx, hlab, hptn⟩ := initRep G flat (Nat.pos_of_ne_zero hn)
    rw [checkNodeP_eq hctx 100 K.rows (containsGammaP_eq hctx cert) n 1
      (by show 1 + n ≤ n + 1; omega) hlab hptn]

/-- The kernel obligation is the trusted `Nauty.checkKey`, for a
literal key whose rows are bitsets over `n` vertices. -/
theorem checkKey_eq (G : Colored n k) (cert : CertNode) (K : Key)
    (h : ∀ r ∈ K.rows, r < 2 ^ n) :
    checkKey G (packRows n G.graph.adjMatrix.data.toList) cert K =
      Nauty.checkKey G cert (K.toKey n) := by
  rw [checkKey_eq_lit, checkKeyLit_eq _ _ _ _ h, checkKeyFlat_eq]

/-- The tactic-facing certificate producer: budgeted
`Nauty.certifyKey?` with its key read as a literal. -/
def certifyKey? (budget : Nat) (G : Colored n k) : Option (CertNode × Key) :=
  (Nauty.certifyKey? G (some budget)).map fun p => (p.1, p.2.toL)

/-- Tying equalities plus two packed-state key certificates with
differing keys prove non-isomorphism: the kernel evaluates each graph
once into its packed rows and replays one certificate per side. -/
theorem not_isomorphic_of_checkKeys {G H : Colored n k}
    {certG certH : CertNode} {BG BH : Key} {NA NB : Nat}
    (hA : packRows n G.graph.adjMatrix.data.toList = NA)
    (hB : packRows n H.graph.adjMatrix.data.toList = NB)
    (hG : checkKey G NA certG BG = true)
    (hH : checkKey H NB certH BH = true)
    (hd : checkDiffL BG BH = true) : ¬Isomorphic G H := by
  subst hA hB
  have hbG : ∀ r ∈ BG.rows, r < 2 ^ n := by
    intro r hr
    rw [checkKey, Bool.and_eq_true] at hG
    exact of_decide_eq_true (List.all_eq_true.mp hG.1 r hr)
  have hbH : ∀ r ∈ BH.rows, r < 2 ^ n := by
    intro r hr
    rw [checkKey, Bool.and_eq_true] at hH
    exact of_decide_eq_true (List.all_eq_true.mp hH.1 r hr)
  rw [checkKey_eq _ _ _ hbG] at hG
  rw [checkKey_eq _ _ _ hbH] at hH
  rw [← toL_toKey (n := n) hbG, ← toL_toKey (n := n) hbH, checkDiffL_toL] at hd
  exact Nauty.not_isomorphic_of_checkKeys hG hH hd

end Kernel

end Hex.GraphIso
