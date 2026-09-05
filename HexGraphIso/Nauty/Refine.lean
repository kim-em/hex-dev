/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module

public import HexGraphIso.Nauty.VSet

public section

/-!
Partition-level routines of the nauty-compatible search, transcribed from
the pinned nauty 2.9.3 sources (`naugraph.c`, `nautil.c`); those files are
the normative reference for every behavioural detail here, including the
splitter processing order, the refinement-code arithmetic, the two-pointer
cell partition, the stable counting redistribution, and the target-cell
rules.

The partition nest is nauty's `(lab, ptn)` pair: `lab` lists the vertices,
and position `i` ends a cell of the partition at level `l` exactly when
`ptn[i] ≤ l`. `NAUTY_INFINITY` is modelled by any value exceeding every
level in use; only comparisons with levels are observable.

Deviations that provably preserve every observable result are noted where
they occur (bucket-window initialization and the stable counting sort in
`refineStep`, both local scratch in nauty).
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- nauty's refinement-code accumulator step: `MASH(l, i)` from
`naugraph.c`. All inputs are nonnegative positions, sizes, or counts, so
`Nat` arithmetic reproduces the C `long` arithmetic exactly. -/
@[expose, inline] def mash (l i : Nat) : Nat :=
  ((l ^^^ 0o65435) + i) &&& 0o77777

/-- nauty's `CLEANUP` of an accumulated refinement code. -/
@[expose, inline] def cleanup (l : Nat) : Nat :=
  l % 0o77777

/-- The graph on `n` vertices as adjacency rows. -/
structure Ctx (n : Nat) where
  /-- Row `v` is the neighbour set of vertex `v`. -/
  g : Array (VSet n)

instance : Inhabited (Ctx n) := ⟨⟨#[]⟩⟩

/-- The end position of the cell starting at `i` in the partition at
`level`: the least `j ≥ i` with `ptn[j] ≤ level`. -/
@[expose] def cellEnd (ptn : Array Nat) (level i : Nat) : Nat :=
  go (ptn.size - i) i
where
  go : Nat → Nat → Nat
    | 0, j => j
    | fuel + 1, j => if ptn[j]! > level then go fuel (j + 1) else j

/-- The cells of the partition at `level`, as `(start, end)` position
pairs in order. -/
@[expose] def cells (ptn : Array Nat) (level n : Nat) : List (Nat × Nat) :=
  go n 0
where
  go : Nat → Nat → List (Nat × Nat)
    | 0, _ => []
    | fuel + 1, c1 =>
      if c1 < n then
        let c2 := cellEnd ptn level c1
        (c1, c2) :: go fuel (c2 + 1)
      else
        []

/-- Working state of one `refine` call on `n` vertices. -/
structure RefineSt (n : Nat) where
  lab : Array Nat
  ptn : Array Nat
  active : VSet n
  numcells : Nat
  hint : Nat
  maxpos : Nat
  longcode : Nat

/-- The next active splitting cell: nauty tries `hint` first, then the
next active position after it, then wraps to the least active position. -/
@[expose] def pickSplit (active : VSet n) (hint : Nat) : Option Nat :=
  if active.mem hint then
    some hint
  else
    match active.nextElem (some hint) with
    | some v => some v
    | none => active.nextElem none

/-- The two-pointer partition of `lab[c1..c2]` by adjacency to the trivial
splitter: adjacent vertices collect on the left in order, non-adjacent
vertices on the right in reversed order, exactly as nauty's swap loop
leaves them. Returns the final `(lab, c1, c2)`. -/
@[expose] def splitCellLoop (gRow : VSet n) :
    Nat → Array Nat → Int → Int → (Array Nat × Int × Int)
  | 0, lab, c1, c2 => (lab, c1, c2)
  | fuel + 1, lab, c1, c2 =>
    if c1 ≤ c2 then
      if gRow.mem lab[c1.toNat]! then
        splitCellLoop gRow fuel lab (c1 + 1) c2
      else
        splitCellLoop gRow fuel
          ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!)
          c1 (c2 - 1)
    else
      (lab, c1, c2)

/-- The position-level bookkeeping after a trivial split with final
pointers `c1`, `c2`: record the new cell end, code, count, active entry,
and hint. Touches no labelling data. -/
@[expose] def trivialSplit (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt n) : RefineSt n :=
  if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
    if st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat then
      if c1.toNat == cell2 then
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := st.active.insert c1.toNat
          hint := c1.toNat }
      else
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := st.active.insert c1.toNat }
    else
      if c2.toNat == cell1 then
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := st.active.insert cell1
          hint := cell1 }
      else
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := st.active.insert cell1 }
  else
    st

/-- One cell's processing in the trivial-splitter pass: two-pointer
partition by adjacency, then the split bookkeeping. -/
@[expose] def trivialCell (level : Nat) (gRow : VSet n) (cell1 cell2 : Nat)
    (st : RefineSt n) : RefineSt n :=
  if cell1 == cell2 then
    st
  else
    trivialSplit level cell1 cell2
      (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
        (Int.ofNat cell1) (Int.ofNat cell2)).2.1
      (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
        (Int.ofNat cell1) (Int.ofNat cell2)).2.2
      { st with
        lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1 }

/-- One splitting pass of `refine` for the trivial splitter cell
`{lab[split1]}`. The splitter row is captured before any cell is
processed, as in nauty. -/
@[expose] def refineTrivial (ctx : Ctx n) (level split1 : Nat)
    (st : RefineSt n) : RefineSt n :=
  go (ctx.g[st.lab[split1]!]!) (cells st.ptn level n) st
where
  go (gRow : VSet n) : List (Nat × Nat) → RefineSt n → RefineSt n
    | [], st => st
    | (cell1, cell2) :: rest, st => go gRow rest (trivialCell level gRow cell1 cell2 st)

/-- `refineTrivial` with the cell walk fused: boundaries come from a
snapshot of the partition (`ptn0`), taken before the pass writes, so
no `(start, end)` pair list is materialized. Runtime form of
`refineTrivial`. -/
@[expose] def refineTrivialFast (ctx : Ctx n) (level split1 : Nat)
    (st : RefineSt n) : RefineSt n :=
  go (ctx.g[st.lab[split1]!]!) st.ptn n 0 st
where
  go (gRow : VSet n) (ptn0 : Array Nat) :
      Nat → Nat → RefineSt n → RefineSt n
    | 0, _, st => st
    | fuel + 1, c1, st =>
      if c1 < n then
        let c2 := cellEnd ptn0 level c1
        go gRow ptn0 fuel (c2 + 1) (trivialCell level gRow c1 c2 st)
      else
        st

theorem refineTrivialFast_go_eq (ctx : Ctx n) (level : Nat) (gRow : VSet n)
    (ptn0 : Array Nat) :
    ∀ (fuel c1 : Nat) (st : RefineSt n),
      refineTrivialFast.go level gRow ptn0 fuel c1 st =
        refineTrivial.go level gRow
          (cells.go ptn0 level n fuel c1) st
  | 0, _, _ => by
    rw [refineTrivialFast.go, cells.go, refineTrivial.go]
  | fuel + 1, c1, st => by
    rw [refineTrivialFast.go, cells.go]
    rcases Decidable.em (c1 < n) with h | h
    · rw [ite_eq_left h, ite_eq_left h, refineTrivial.go]
      exact refineTrivialFast_go_eq ctx level gRow ptn0 fuel _ _
    · rw [ite_eq_right h, ite_eq_right h, refineTrivial.go]

@[csimp] theorem refineTrivial_eq_fast :
    @refineTrivial = @refineTrivialFast := by
  funext n ctx level split1 st
  rw [refineTrivial, refineTrivialFast, cells]
  exact (refineTrivialFast_go_eq ctx level _ st.ptn n 0 st).symm

/-- The splitter cell's vertex set: the members of `lab[lo..hi]`. -/
@[expose] def worksetOf (n : Nat) (lab : Array Nat) (lo hi : Nat) : VSet n :=
  (List.range (hi + 1 - lo)).foldl (fun w o => w.insert lab[lo + o]!) .empty

/-- The neighbour counts of a cell's members into the splitter set, in
cell order. -/
@[expose] def countsOf (ctx : Ctx n) (lab : Array Nat) (workset : VSet n)
    (cell1 cell2 : Nat) : List Nat :=
  (List.range (cell2 + 1 - cell1)).map fun o =>
    workset.cardInter ctx.g[lab[cell1 + o]!]!

/-- The multiplicity of count value `v` in a count list. -/
@[expose] def multOf (counts : List Nat) (v : Nat) : Nat :=
  counts.countP (· == v)

/-- One nonempty count group's bookkeeping in the window scan: code
contribution, `maxpos` of the largest group so far, the group boundary
with its active-set entry, and the new cell end. Touches no labelling
data. -/
@[expose] def windowStep (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt n) : RefineSt n :=
  let st := { st with longcode := mash st.longcode (v + c1) }
  let st :=
    if Int.ofNat (c2 - c1) > maxcell then { st with maxpos := c1 } else st
  let st :=
    if c1 != cell1 then
      let st := { st with
        active := st.active.insert c1
        numcells := st.numcells + 1 }
      if c2 - c1 == 1 then { st with hint := c1 } else st
    else
      st
  if c2 ≤ cell2 then { st with ptn := st.ptn.set! (c2 - 1) level }
  else st

/-- The position scan over the count window `[bmin, bmax]`: register each
nonempty group's boundary, code contribution, active-set entry, and the
`maxpos` of the largest group. -/
@[expose] def windowScan (level cell1 cell2 : Nat) (counts : List Nat) :
    List Nat → Nat → Int → RefineSt n → RefineSt n
  | [], _, _, st => st
  | v :: vs, c1, maxcell, st =>
    if multOf counts v > 0 then
      windowScan level cell1 cell2 counts vs (c1 + multOf counts v)
        (if Int.ofNat (multOf counts v) > maxcell then
          Int.ofNat (multOf counts v)
        else maxcell)
        (windowStep level cell1 cell2 v c1 (c1 + multOf counts v) maxcell st)
    else
      windowScan level cell1 cell2 counts vs c1 maxcell st

/-- The stable counting sort of a cell segment: members grouped by count
value in ascending value order, keeping cell order within a group. -/
@[expose] def segmentOf (lab : Array Nat) (cell1 : Nat) (counts : List Nat)
    (values : List Nat) : List Nat :=
  values.flatMap fun v =>
    (counts.zipIdx.filter fun (c, _) => c == v).map fun (_, j) =>
      lab[cell1 + j]!

/-- Write a segment back at `cell1`. -/
@[expose] def writeSegment (lab : Array Nat) (cell1 : Nat) : List Nat → Array Nat
  | [] => lab
  | x :: rest => writeSegment (lab.set! cell1 x) (cell1 + 1) rest

/-- The active-set fix after a nontrivial split: if the original cell was
not active, activate the whole boundary except the largest fragment.
Touches no labelling data. -/
@[expose] def nontrivialFix (cell1 : Nat) (st : RefineSt n) : RefineSt n :=
  if ¬ st.active.mem cell1 then
    { st with active := (st.active.insert cell1).erase st.maxpos }
  else
    st

/-- The value window scanned by the nontrivial splitter: `bmin` to
`bmax` inclusive. -/
@[expose] def countValues (counts : List Nat) : List Nat :=
  (List.range (counts.foldl Nat.max (counts.headD 0) + 1 -
    counts.foldl Nat.min (counts.headD 0))).map
    (counts.foldl Nat.min (counts.headD 0) + ·)

/-- One cell's processing in the nontrivial-splitter pass. -/
@[expose] def nontrivialCell (ctx : Ctx n) (level : Nat) (workset : VSet n)
    (cell1 cell2 : Nat) (st : RefineSt n) : RefineSt n :=
  if cell1 == cell2 then
    st
  else if (countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
      ((countsOf ctx st.lab workset cell1 cell2).headD 0) ==
      (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) then
    { st with
      longcode := mash st.longcode
        ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
          ((countsOf ctx st.lab workset cell1 cell2).headD 0) + cell1) }
  else
    nontrivialFix cell1
      { windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st with
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
              (countValues (countsOf ctx st.lab workset cell1 cell2))) }

/-! # The bucket-array counting sort

`nontrivialCellFast` computes the same `RefineSt` as `nontrivialCell`
through one counts pass, a multiplicity bucket array, a bucket-driven
window scan, and a stable single-pass placement — O(cell + window)
with no intermediate lists, where the specification's `multOf`-driven
scan and `segmentOf` redistribution are O(cell x window) with list
construction throughout. The equality `nontrivialCell_eq_fast` below
is `@[csimp]`, so every compiled call site runs the counting sort;
the specification spellings above stay the proof surface. -/

/-- The counts pass: per-member neighbour counts into the splitter
set, the members themselves, and the count extrema, in one walk. -/
@[expose] def ntcPass (ctx : Ctx n) (lab : Array Nat) (workset : VSet n)
    (cell1 : Nat) : Nat → Nat → Array Nat → Array Nat → Nat → Nat →
      Array Nat × Array Nat × Nat × Nat
  | 0, _, counts, members, bmin, bmax => (counts, members, bmin, bmax)
  | fuel + 1, o, counts, members, bmin, bmax =>
    let m := lab[cell1 + o]!
    let c := workset.cardInter ctx.g[m]!
    ntcPass ctx lab workset cell1 fuel (o + 1) (counts.push c)
      (members.push m) (Nat.min bmin c) (Nat.max bmax c)

/-- Count multiplicities into a window-sized bucket array. -/
@[expose] def ntcBucket (counts : Array Nat) (bmin : Nat) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, bucket => bucket
  | fuel + 1, i, bucket =>
    let v := counts[i]! - bmin
    ntcBucket counts bmin fuel (i + 1) (bucket.set! v (bucket[v]! + 1))

/-- The window scan driven by the bucket array: replays `windowStep`
for each nonempty count group in ascending value order. -/
@[expose] def ntcScan (level cell1 cell2 bmin : Nat) (bucket : Array Nat) :
    Nat → Nat → Nat → Int → RefineSt n → RefineSt n
  | 0, _, _, _, st => st
  | fuel + 1, j, c1, maxcell, st =>
    let m := bucket[j]!
    if m > 0 then
      ntcScan level cell1 cell2 bmin bucket fuel (j + 1) (c1 + m)
        (if Int.ofNat m > maxcell then Int.ofNat m else maxcell)
        (windowStep level cell1 cell2 (bmin + j) c1 (c1 + m) maxcell st)
    else
      ntcScan level cell1 cell2 bmin bucket fuel (j + 1) c1 maxcell st

/-- Exclusive prefix positions of the count groups, offset to the
cell start. -/
@[expose] def ntcStarts (bucket : Array Nat) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, starts => starts
  | fuel + 1, pos, starts =>
    ntcStarts bucket fuel (pos + bucket[starts.size]!) (starts.push pos)

/-- The stable placement: one ascending walk over the members, each
written at its group's next position. -/
@[expose] def ntcPlace (counts members : Array Nat) (bmin : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, lab, starts => (lab, starts)
  | fuel + 1, o, lab, starts =>
    let v := counts[o]! - bmin
    let pos := starts[v]!
    ntcPlace counts members bmin fuel (o + 1)
      (lab.set! pos members[o]!) (starts.set! v (pos + 1))

/-- `nontrivialCell` as the bucket-array counting sort. -/
@[expose] def nontrivialCellFast (ctx : Ctx n) (level : Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (st : RefineSt n) :
    RefineSt n :=
  if cell1 == cell2 then
    st
  else if cell2 < cell1 then
    -- Empty window (`cell2 + 1 - cell1 = 0`): the specification's
    -- `countsOf` is empty, so its min equals max equals `headD 0 = 0`
    -- and it emits `mash longcode (0 + cell1)`. Match it directly
    -- rather than seeding the extrema from `c0`.
    { st with longcode := mash st.longcode cell1 }
  else
    let m0 := st.lab[cell1]!
    let c0 := workset.cardInter ctx.g[m0]!
    let r := ntcPass ctx st.lab workset cell1 (cell2 - cell1) 1
      ((Array.mkEmpty (cell2 + 1 - cell1)).push c0)
      ((Array.mkEmpty (cell2 + 1 - cell1)).push m0) c0 c0
    let counts := r.1
    let members := r.2.1
    let bmin := r.2.2.1
    let bmax := r.2.2.2
    if bmin == bmax then
      { st with longcode := mash st.longcode (bmin + cell1) }
    else
      let bucket := ntcBucket counts bmin counts.size 0
        (Array.replicate (bmax + 1 - bmin) 0)
      let st' := ntcScan level cell1 cell2 bmin bucket
        (bmax + 1 - bmin) 0 cell1 (-1) st
      nontrivialFix cell1
        { st' with
          lab := (ntcPlace counts members bmin counts.size 0
            st'.lab (ntcStarts bucket (bmax + 1 - bmin) cell1 #[])).1 }

/-! Support lemmas toward `nontrivialCell = nontrivialCellFast`: the
window-scan correspondence. The counting-sort placement machinery and
the assembled `@[csimp]` equality follow below. -/

theorem windowStep_lab (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt n) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).lab = st.lab := by
  simp only [windowStep]
  repeat' split
  all_goals rfl

theorem windowScan_lab (level cell1 cell2 : Nat) (counts : List Nat) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      (windowScan level cell1 cell2 counts vs c1 maxcell st).lab = st.lab
  | [], _, _, _ => rfl
  | v :: vs, c1, maxcell, st => by
    rw [windowScan]
    split
    · rw [windowScan_lab level cell1 cell2 counts vs, windowStep_lab]
    · exact windowScan_lab level cell1 cell2 counts vs c1 maxcell st

/-- The bucket-driven scan replays `windowScan` over an ascending
value window whenever the bucket entries are the multiplicities. -/
theorem ntcScan_eq_windowScan (level cell1 cell2 bmin : Nat)
    (bucket : Array Nat) (counts : List Nat) :
    ∀ (fuel j c1 : Nat) (maxcell : Int) (st : RefineSt n),
      (∀ i, i < fuel → bucket[j + i]! = multOf counts (bmin + j + i)) →
      ntcScan level cell1 cell2 bmin bucket fuel j c1 maxcell st =
        windowScan level cell1 cell2 counts
          ((List.range fuel).map (bmin + j + ·)) c1 maxcell st
  | 0, _, _, _, _, _ => by
    rw [ntcScan]
    rfl
  | fuel + 1, j, c1, maxcell, st, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hrest : ∀ i, i < fuel → bucket[(j + 1) + i]! =
        multOf counts (bmin + (j + 1) + i) := by
      intro i hi
      have hh := h (i + 1) (by omega)
      rw [show j + (i + 1) = j + 1 + i from by omega] at hh
      rw [show bmin + j + (i + 1) = bmin + (j + 1) + i from by omega]
        at hh
      exact hh
    rw [ntcScan]
    rw [List.range_succ_eq_map, List.map_cons, windowScan, List.map_map]
    simp only [Nat.add_zero]
    have hmap : (List.map ((fun x => bmin + j + x) ∘ Nat.succ)
        (List.range fuel)) =
        (List.range fuel).map (bmin + (j + 1) + ·) :=
      List.map_congr_left fun i _ => by
        simp only [Function.comp]
        omega
    rw [hmap, ← h0]
    by_cases hm : bucket[j]! > 0
    · rw [ite_eq_left hm, ite_eq_left hm,
        ntcScan_eq_windowScan level cell1 cell2 bmin bucket counts
          fuel (j + 1) (c1 + bucket[j]!)
          (if Int.ofNat bucket[j]! > maxcell then Int.ofNat bucket[j]!
            else maxcell)
          (windowStep level cell1 cell2 (bmin + j) c1 (c1 + bucket[j]!)
            maxcell st) hrest]
    · rw [ite_eq_right hm, ite_eq_right hm,
        ntcScan_eq_windowScan level cell1 cell2 bmin bucket counts
          fuel (j + 1) c1 maxcell st hrest]

/-! # The counting-sort activation

The bucket-array counting sort `nontrivialCellFast` equals the
specification `nontrivialCell`; the proof lives here, upstream of the
`refine` drivers, so the concluding `@[csimp]` rewrites their compiled
call sites. The segment write-back lemmas sit first: they are stated
against `writeSegment` alone, and `CellPermLoop`'s `segN` lemmas
consume them downstream. -/

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

private theorem push_append_toArray {α : Type} (a : Array α) (x : α)
    (l : List α) : a.push x ++ l.toArray = a ++ (x :: l).toArray := by
  apply Array.toList_inj.mp
  simp

private theorem getElem!_push_lt {α : Type} [Inhabited α] (a : Array α)
    (x : α) (q : Nat) (h : q < a.size) : (a.push x)[q]! = a[q]! := by
  rw [getElem!_pos (a.push x) q (by rw [Array.size_push]; omega),
    getElem!_pos a q h, Array.getElem_push_lt]

/-! # The counts pass -/

/-- `ntcPass` appends the per-member counts and members over its fuel
window and folds the extrema, leaving the accumulator prefixes intact. -/
theorem ntcPass_spec (ctx : Ctx n) (lab : Array Nat) (workset : VSet n)
    (cell1 : Nat) :
    ∀ (fuel o : Nat) (counts members : Array Nat) (bmin bmax : Nat),
      ntcPass ctx lab workset cell1 fuel o counts members bmin bmax =
        (counts ++ ((List.range fuel).map fun i =>
            workset.cardInter ctx.g[lab[cell1 + o + i]!]!).toArray,
         members ++ ((List.range fuel).map fun i =>
            lab[cell1 + o + i]!).toArray,
         (List.range fuel).foldl (fun b i =>
            Nat.min b (workset.cardInter ctx.g[lab[cell1 + o + i]!]!))
            bmin,
         (List.range fuel).foldl (fun b i =>
            Nat.max b (workset.cardInter ctx.g[lab[cell1 + o + i]!]!))
            bmax)
  | 0, o, counts, members, bmin, bmax => by
    simp [ntcPass]
  | fuel + 1, o, counts, members, bmin, bmax => by
    rw [ntcPass, ntcPass_spec ctx lab workset cell1 fuel (o + 1)]
    have hshift : ∀ (i : Nat), cell1 + (o + 1) + i = cell1 + o + (i + 1) :=
      fun i => by omega
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      List.foldl_cons, List.foldl_map, Nat.add_zero, Function.comp_def,
      push_append_toArray, Nat.succ_eq_add_one, hshift]

/-! # The multiplicity bucket -/

/-- `ntcBucket` accumulates, at slot `v`, the running bucket count plus
the number of processed positions whose count value is `bmin + v`. Slots
are only ever touched in range, so out-of-window reads are preserved. -/
theorem ntcBucket_spec (counts : Array Nat) (bmin : Nat) :
    ∀ (fuel i : Nat) (bucket : Array Nat),
      i + fuel ≤ counts.size →
      (∀ q, i ≤ q → q < i + fuel → counts[q]! - bmin < bucket.size) →
      ∀ v, v < bucket.size →
        (ntcBucket counts bmin fuel i bucket)[v]! =
          bucket[v]! +
            ((List.range' i fuel).countP fun q =>
              counts[q]! - bmin == v)
  | 0, i, bucket, _, _, v, _ => by
    simp [ntcBucket]
  | fuel + 1, i, bucket, hsz, hrange, v, hv => by
    rw [ntcBucket]
    have hi : i < counts.size := by omega
    have hib : counts[i]! - bmin < bucket.size := hrange i (by omega) (by omega)
    have hsz' : (i + 1) + fuel ≤ counts.size := by omega
    have hrange' : ∀ q, i + 1 ≤ q → q < (i + 1) + fuel →
        counts[q]! - bmin < (bucket.set! (counts[i]! - bmin)
          (bucket[counts[i]! - bmin]! + 1)).size := by
      intro q hq1 hq2
      rw [Array.size_set!]
      exact hrange q (by omega) (by omega)
    have hv' : v < (bucket.set! (counts[i]! - bmin)
        (bucket[counts[i]! - bmin]! + 1)).size := by
      rw [Array.size_set!]; exact hv
    rw [ntcBucket_spec counts bmin fuel (i + 1) _ hsz' hrange' v hv']
    rw [List.range'_succ, List.countP_cons]
    by_cases hveq : (counts[i]! - bmin == v) = true
    · rw [ite_eq_left hveq]
      have hvv : counts[i]! - bmin = v := by simp only [beq_iff_eq] at hveq; exact hveq
      rw [hvv, Array.getElem!_set!_self _ _ _ (by rw [← hvv]; exact hib)]
      omega
    · rw [ite_eq_right hveq]
      rw [Array.getElem!_set!_ne _ _ _ _ (by
        intro h; exact hveq (by simp [h]))]
      omega

/-! # The group start positions -/

/-- `ntcStarts` appends one entry per fuel step. -/
theorem ntcStarts_size (bucket : Array Nat) :
    ∀ (fuel pos : Nat) (starts : Array Nat),
      (ntcStarts bucket fuel pos starts).size = starts.size + fuel
  | 0, _, starts => by simp [ntcStarts]
  | fuel + 1, pos, starts => by
    rw [ntcStarts, ntcStarts_size bucket fuel _ _, Array.size_push]
    omega

/-- Slots below the current size are untouched by `ntcStarts`. -/
theorem ntcStarts_preserve (bucket : Array Nat) :
    ∀ (fuel pos : Nat) (starts : Array Nat) (q : Nat), q < starts.size →
      (ntcStarts bucket fuel pos starts)[q]! = starts[q]!
  | 0, _, _, _, _ => by simp [ntcStarts]
  | fuel + 1, pos, starts, q, hq => by
    rw [ntcStarts, ntcStarts_preserve bucket fuel _ _ q
      (by rw [Array.size_push]; omega),
      getElem!_push_lt _ _ q hq]

private theorem getElem!_push_eq {α : Type} [Inhabited α] (a : Array α)
    (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega),
    Array.getElem_push_eq]

/-- `ntcStarts` fills each new slot with the running exclusive prefix
sum of the bucket: slot `starts.size + t` holds `pos` plus the bucket
mass over the intervening window. -/
theorem ntcStarts_value (bucket : Array Nat) :
    ∀ (fuel pos : Nat) (starts : Array Nat) (t : Nat), t < fuel →
      (ntcStarts bucket fuel pos starts)[starts.size + t]! =
        pos + ((List.range t).map
          (fun j => bucket[starts.size + j]!)).sum
  | 0, _, _, _, ht => absurd ht (by omega)
  | fuel + 1, pos, starts, t, ht => by
    rw [ntcStarts]
    cases t with
    | zero =>
      rw [Nat.add_zero,
        ntcStarts_preserve bucket fuel _ _ starts.size
          (by rw [Array.size_push]; omega),
        getElem!_push_eq]
      simp
    | succ s =>
      have hlt : s < fuel := by omega
      have hidx : starts.size + (s + 1) = (starts.push pos).size + s := by
        rw [Array.size_push]; omega
      rw [hidx, ntcStarts_value bucket fuel (pos + bucket[starts.size]!)
        (starts.push pos) s hlt, Array.size_push]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map,
        List.sum_cons, Nat.add_zero]
      have hmap : ((List.range s).map
          ((fun j => bucket[starts.size + j]!) ∘ Nat.succ)) =
          (List.range s).map (fun j => bucket[starts.size + 1 + j]!) :=
        List.map_congr_left fun j _ => by
          simp only [Function.comp]; congr 1; omega
      rw [hmap]
      generalize ((List.range s).map (fun j => bucket[starts.size + 1 + j]!)).sum = X
      simp only [Nat.add_zero]
      omega

/-- The group base positions tile the cell: the count of members below
value `v + 1` is the count below `v` plus the multiplicity of `v`. This
is what makes the group intervals `[base v, base v + mult v)` disjoint
and contiguous, hence the placement injective and size-exact. -/
theorem countP_lt_succ (c : Nat → Nat) (v : Nat) :
    ∀ l : List Nat,
      l.countP (fun o => decide (c o < v + 1)) =
        l.countP (fun o => decide (c o < v)) +
          l.countP (fun o => c o == v)
  | [] => rfl
  | x :: l => by
    simp only [List.countP_cons]
    rw [countP_lt_succ c v l]
    rcases Nat.lt_trichotomy (c x) v with h | h | h
    · rw [show decide (c x < v + 1) = true by simp; omega,
          show decide (c x < v) = true by simp; omega,
          show (c x == v) = false by simp; omega]
      simp; omega
    · rw [show decide (c x < v + 1) = true by simp; omega,
          show decide (c x < v) = false by simp; omega,
          show (c x == v) = true by simp; omega]
      simp; omega
    · rw [show decide (c x < v + 1) = false by simp; omega,
          show decide (c x < v) = false by simp; omega,
          show (c x == v) = false by simp; omega]
      simp

/-- The exclusive prefix width of the count groups below value `bmin + k`:
the number of members whose count value is strictly less than `bmin + k`,
i.e. the offset (from `cell1`) of group `k`'s base position. -/
private def baseOff (counts : Array Nat) (bmin k : Nat) : Nat :=
  (List.range counts.size).countP fun o => decide (counts[o]! - bmin < k)

/-- The number of members of group `k` already placed after the
length-`o` prefix of the cell-order walk. -/
private def placed (counts : Array Nat) (bmin o k : Nat) : Nat :=
  (List.range o).countP fun o' => counts[o']! - bmin == k

private theorem placed_zero (counts : Array Nat) (bmin k : Nat) :
    placed counts bmin 0 k = 0 := by
  simp [placed]

/-- `placed` at the full length is the group multiplicity `baseOff (k+1)
- baseOff k`, and the group base is `baseOff k`. -/
private theorem baseOff_succ (counts : Array Nat) (bmin k : Nat) :
    baseOff counts bmin (k + 1) =
      baseOff counts bmin k + placed counts bmin counts.size k := by
  rw [baseOff, baseOff, placed,
    countP_lt_succ (fun o => counts[o]! - bmin) k (List.range counts.size)]

/-- Stepping the walk past index `o` bumps `placed` for `o`'s own group,
leaving the others fixed. -/
private theorem placed_succ (counts : Array Nat) (bmin o k : Nat) :
    placed counts bmin (o + 1) k =
      placed counts bmin o k + (if counts[o]! - bmin == k then 1 else 0) := by
  rw [placed, placed, List.range_succ, List.countP_append, List.countP_cons,
    List.countP_nil]
  simp only [Nat.zero_add]

private theorem countP_lt_mono {c : Nat → Nat} {k k' : Nat} (h : k ≤ k')
    (l : List Nat) :
    l.countP (fun o => decide (c o < k)) ≤
      l.countP (fun o => decide (c o < k')) := by
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  omega

/-- `baseOff` is monotone in the group index. -/
private theorem baseOff_mono (counts : Array Nat) (bmin : Nat) {k k' : Nat}
    (h : k ≤ k') : baseOff counts bmin k ≤ baseOff counts bmin k' :=
  countP_lt_mono h _

/-- `placed` is monotone in the prefix length. -/
private theorem placed_mono (counts : Array Nat) (bmin k : Nat) {o o' : Nat}
    (h : o ≤ o') : placed counts bmin o k ≤ placed counts bmin o' k := by
  rw [placed, placed, ← Nat.add_sub_cancel' h, List.range_add,
    List.countP_append]
  omega

/-- Room: a not-yet-placed member of group `v` leaves its group cursor
below the group multiplicity. -/
private theorem placed_lt_mult (counts : Array Nat) (bmin o v : Nat)
    (ho : o < counts.size) (hv : counts[o]! - bmin == v) :
    placed counts bmin o v < placed counts bmin counts.size v := by
  have h1 : placed counts bmin (o + 1) v = placed counts bmin o v + 1 := by
    rw [placed_succ, ite_eq_left hv]
  have h2 : placed counts bmin (o + 1) v ≤ placed counts bmin counts.size v :=
    placed_mono counts bmin v (by omega)
  omega

/-- With every count in the window, `baseOff` at the window width is the
whole cell. -/
private theorem baseOff_eq_size (counts : Array Nat) (bmin W : Nat)
    (hall : ∀ o, o < counts.size → counts[o]! - bmin < W) :
    baseOff counts bmin W = counts.size := by
  rw [baseOff]
  have hlen : (List.range counts.size).countP
      (fun o => decide (counts[o]! - bmin < W)) =
      (List.range counts.size).length := by
    rw [List.countP_eq_length]
    intro o ho
    rw [List.mem_range] at ho
    simp only [decide_eq_true_eq]
    exact hall o ho
  rw [hlen, List.length_range]

/-- Group intervals are disjoint: distinct groups' base-offset windows
`[baseOff k, baseOff k + mult k)` do not overlap. -/
private theorem baseOff_disjoint (counts : Array Nat) (bmin : Nat) {k k' : Nat}
    (hne : k ≠ k') {r r' : Nat}
    (hr : r < placed counts bmin counts.size k)
    (hr' : r' < placed counts bmin counts.size k') :
    baseOff counts bmin k + r ≠ baseOff counts bmin k' + r' := by
  rcases Nat.lt_or_ge k k' with h | h
  · have hb : baseOff counts bmin (k + 1) ≤ baseOff counts bmin k' :=
      baseOff_mono counts bmin (by omega)
    rw [baseOff_succ] at hb
    omega
  · have hlt : k' < k := by omega
    have hb : baseOff counts bmin (k' + 1) ≤ baseOff counts bmin k :=
      baseOff_mono counts bmin (by omega)
    rw [baseOff_succ] at hb
    omega

/-- `baseOff` telescopes into the sum of the earlier group multiplicities:
the exclusive prefix sum the bucket start positions are built from. -/
private theorem baseOff_eq_sum (counts : Array Nat) (bmin : Nat) :
    ∀ v : Nat,
      baseOff counts bmin v =
        ((List.range v).map
          (fun j => placed counts bmin counts.size j)).sum
  | 0 => by simp [baseOff]
  | v + 1 => by
    rw [baseOff_succ, baseOff_eq_sum counts bmin v, List.range_succ,
      List.map_append, List.sum_append]
    simp

/-! # Reusable list-indexing lemmas for the placement crux -/

/-- Reading an append below the left operand's length
reads the left operand. -/
theorem getElem!_append_left {α : Type} [Inhabited α]
    {as bs : List α} {i : Nat} (h : i < as.length) :
    (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [List.length_append]; omega),
    getElem!_pos as i h, List.getElem_append_left h]

/-- Reading an append at or above the left operand's
length reads the right operand. -/
theorem getElem!_append_right {α : Type} [Inhabited α]
    {as bs : List α} {i : Nat} (h : as.length ≤ i)
    (hi : i - as.length < bs.length) :
    (as ++ bs)[i]! = bs[i - as.length]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [List.length_append]; omega),
    getElem!_pos bs (i - as.length) hi, List.getElem_append_right h]

/-- A prefix `flatMap` is no longer than the whole. -/
private theorem flatMap_take_length_le {α β : Type} (g : α → List β)
    (vs : List α) (m : Nat) :
    ((vs.take m).flatMap g).length ≤ (vs.flatMap g).length :=
  calc ((vs.take m).flatMap g).length
      ≤ ((vs.take m).flatMap g).length + ((vs.drop m).flatMap g).length :=
        by omega
    _ = (vs.flatMap g).length := by
        rw [← List.length_append, ← List.flatMap_append,
          List.take_append_drop]

/-- One more block extends the prefix `flatMap` length by that block. -/
private theorem flatMap_take_succ_length {α β : Type} [Inhabited α]
    (g : α → List β) (vs : List α) (k : Nat) (hk : k < vs.length) :
    ((vs.take (k + 1)).flatMap g).length =
      ((vs.take k).flatMap g).length + (g (vs[k]!)).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.flatMap_append, List.length_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  congr 2
  rw [getElem!_pos vs k hk]

/-- Indexing a `flatMap` inside one block: the element at
`((vs.take k).flatMap g).length + r` is the `r`-th element of the
`k`-th block `g vs[k]`, given `k` is a real index and `r` is within
that block. -/
private theorem flatMap_getElem!_block {α β : Type} [Inhabited α]
    [Inhabited β] (g : α → List β) :
    ∀ (vs : List α) (k r : Nat), k < vs.length →
      r < (g (vs[k]!)).length →
      (vs.flatMap g)[((vs.take k).flatMap g).length + r]! =
        (g (vs[k]!))[r]!
  | [], k, r, hk, _ => absurd hk (by simp)
  | x :: xs, 0, r, _, hr => by
    simp only [List.take_zero, List.flatMap_nil, List.length_nil,
      Nat.zero_add, List.getElem!_cons_zero] at hr ⊢
    rw [List.flatMap_cons, getElem!_append_left hr]
  | x :: xs, k + 1, r, hk, hr => by
    rw [List.getElem!_cons_succ] at hr
    have hk' : k < xs.length := by
      simp only [List.length_cons] at hk; omega
    have hrec := flatMap_getElem!_block g xs k r hk' hr
    have hbound : ((List.take k xs).flatMap g).length + r <
        (xs.flatMap g).length := by
      have hle := flatMap_take_succ_length g xs k hk'
      have hpref := flatMap_take_length_le g xs (k + 1)
      omega
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append,
      List.getElem!_cons_succ]
    have hge : (g x).length + ((List.take k xs).flatMap g).length + r
        ≥ (g x).length := by omega
    have hsub : (g x).length + ((List.take k xs).flatMap g).length + r
        - (g x).length = ((List.take k xs).flatMap g).length + r := by omega
    rw [getElem!_append_right hge (by rw [hsub]; exact hbound), hsub, hrec]

/-- The value-`w` group of a zipped list from start index `s`, decoded
by `dec` over the absolute positions: the segment `segmentOf` builds
for one value. -/
private def grpAt {β : Type} (cs : List Nat) (w : Nat) (dec : Nat → β)
    (s : Nat) : List β :=
  ((cs.zipIdx s).filter fun p => p.1 == w).map fun p => dec p.2

/-- Counting matches through a `zipIdx` ignores the indices. -/
private theorem zipIdx_countP_fst (w : Nat) :
    ∀ (cs : List Nat) (s : Nat),
      ((cs.zipIdx s).countP fun p => p.1 == w) = cs.countP (· == w)
  | [], _ => rfl
  | x :: xs, s => by
    rw [List.zipIdx_cons, List.countP_cons, List.countP_cons,
      zipIdx_countP_fst w xs (s + 1)]

/-- The length of a group is the multiplicity of its value. -/
private theorem grpAt_length {β : Type} (cs : List Nat) (w : Nat)
    (dec : Nat → β) (s : Nat) :
    (grpAt cs w dec s).length = cs.countP (· == w) := by
  rw [grpAt, List.length_map, ← List.countP_eq_length_filter,
    zipIdx_countP_fst]

/-- The `r`-th element of the value-`w` group, where `r` is the number
of earlier value-`w` positions, is `dec` at the absolute position. -/
private theorem grpAt_getElem! {β : Type} [Inhabited β] (w : Nat)
    (dec : Nat → β) :
    ∀ (cs : List Nat) (s o : Nat), o < cs.length → (cs[o]! == w) = true →
      (grpAt cs w dec s)[(cs.take o).countP (· == w)]! = dec (s + o)
  | [], _, o, ho, _ => absurd ho (by simp)
  | x :: xs, s, 0, _, hq => by
    simp only [List.getElem!_cons_zero] at hq
    rw [grpAt, List.zipIdx_cons, List.filter_cons_of_pos (by simpa using hq),
      List.map_cons, List.take_zero, List.countP_nil,
      List.getElem!_cons_zero, Nat.add_zero]
  | x :: xs, s, o + 1, ho, hq => by
    simp only [List.getElem!_cons_succ] at hq
    have ho' : o < xs.length := by
      simp only [List.length_cons] at ho; omega
    have hrec := grpAt_getElem! w dec xs (s + 1) o ho' hq
    rw [grpAt] at hrec
    rw [grpAt, List.zipIdx_cons, List.take_succ_cons, List.countP_cons]
    by_cases hx : (x == w) = true
    · rw [List.filter_cons_of_pos (by simpa using hx), List.map_cons,
        ite_eq_left hx, List.getElem!_cons_succ, hrec]
      congr 1; omega
    · rw [List.filter_cons_of_neg (by simpa using hx), ite_eq_right hx]
      simp only [Nat.add_zero]
      rw [hrec]; congr 1; omega

/-! # Bridging `baseOff`/`placed` to list `countP` forms -/

/-- Counting a predicate over a prefix of positions equals counting it
over the prefix list. -/
private theorem countP_range_getElem! (l : List Nat) (φ : Nat → Bool) :
    ∀ o : Nat, o ≤ l.length →
      (List.range o).countP (fun i => φ (l[i]!)) = (l.take o).countP φ
  | 0, _ => by simp
  | o + 1, ho => by
    have ho' : o < l.length := by omega
    rw [List.range_succ, List.countP_append, List.countP_singleton,
      List.take_add_one, List.getElem?_eq_getElem ho', Option.toList_some,
      List.countP_append, List.countP_singleton,
      countP_range_getElem! l φ o (by omega), getElem!_pos l o ho']

/-- `placed` counts the value-`bmin + v` positions in the length-`o`
prefix (once every entry is at least `bmin`). -/
private theorem placed_eq_take_countP (counts : Array Nat) (bmin o v : Nat)
    (ho : o ≤ counts.size)
    (hmin : ∀ q, q < counts.size → bmin ≤ counts[q]!) :
    placed counts bmin o v =
      (counts.toList.take o).countP (· == bmin + v) := by
  rw [placed]
  have hcongr : (List.range o).countP (fun o' => counts[o']! - bmin == v) =
      (List.range o).countP (fun i => counts.toList[i]! == bmin + v) := by
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    have hge : bmin ≤ counts[i]! := hmin i (by omega)
    rw [Array.getElem!_toList]
    simp only [beq_iff_eq]
    omega
  rw [hcongr,
    countP_range_getElem! counts.toList (· == bmin + v) o
      (by rw [Array.length_toList]; exact ho)]

/-- `baseOff` as a `countP` over the count list. -/
private theorem baseOff_eq_countP (counts : Array Nat) (bmin v : Nat) :
    baseOff counts bmin v =
      counts.toList.countP (fun c => decide (c - bmin < v)) := by
  rw [baseOff]
  rw [show (fun o => decide (counts[o]! - bmin < v)) =
      (fun i => (fun c => decide (c - bmin < v)) (counts.toList[i]!)) from by
    funext o; rw [Array.getElem!_toList]]
  rw [countP_range_getElem! counts.toList (fun c => decide (c - bmin < v))
    counts.size (Nat.le_of_eq Array.length_toList.symm)]
  rw [List.take_of_length_le (Nat.le_of_eq Array.length_toList)]

/-- The prefix of value groups tiles the members of value below the
threshold: the concatenated groups for `[bmin, …, bmin + v - 1]` have
length `countP (c - bmin < v)`, once every entry is at least `bmin`. -/
private theorem flatMap_grpAt_length {β : Type} (cs : List Nat)
    (dec : Nat → β) (bmin : Nat) (hmem : ∀ c ∈ cs, bmin ≤ c) :
    ∀ v : Nat,
      (((List.range v).map (bmin + ·)).flatMap
        (fun w => grpAt cs w dec 0)).length =
        cs.countP (fun c => decide (c - bmin < v))
  | 0 => by
    simp only [List.range_zero, List.map_nil, List.flatMap_nil,
      List.length_nil]
    rw [List.countP_eq_zero.mpr]
    intro c _; simp
  | v + 1 => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.flatMap_append, List.length_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, grpAt_length,
      flatMap_grpAt_length cs dec bmin hmem v]
    have hswap : cs.countP (· == bmin + v) =
        cs.countP (fun c => c - bmin == v) := by
      apply List.countP_congr
      intro c hc
      have := hmem c hc
      simp only [beq_iff_eq]; omega
    rw [hswap]
    have := countP_lt_succ (fun c => c - bmin) v cs
    omega

/-- Indexing a value-mapped range. -/
private theorem map_range_getElem! (bmin W k : Nat) (hk : k < W) :
    ((List.range W).map (bmin + ·))[k]! = bmin + k := by
  rw [getElem!_pos _ k (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

/-! # The placement crux -/

/-- The scatter destination, abstractly: the flatMap of value groups,
indexed at `(members below value bmin+v) + (earlier value-bmin+v
members)`, yields `dec o`. Independent of the array bookkeeping. -/
private theorem grouped_getElem! {β : Type} [Inhabited β] (cs : List Nat)
    (dec : Nat → β) (bmin W v o : Nat)
    (hmem : ∀ c ∈ cs, bmin ≤ c) (hv_lt : v < W)
    (ho : o < cs.length) (hqo : (cs[o]! == bmin + v) = true)
    (hr : (cs.take o).countP (· == bmin + v) < cs.countP (· == bmin + v)) :
    (((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt cs w dec 0))[
        cs.countP (fun c => decide (c - bmin < v)) +
        (cs.take o).countP (· == bmin + v)]! = dec o := by
  have htake : ((List.range W).map (bmin + ·)).take v =
      (List.range v).map (bmin + ·) := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
  have hbase : ((((List.range W).map (bmin + ·)).take v).flatMap
        (fun w => grpAt cs w dec 0)).length =
        cs.countP (fun c => decide (c - bmin < v)) := by
    rw [htake, flatMap_grpAt_length cs dec bmin hmem v]
  have hvget : ((List.range W).map (bmin + ·))[v]! = bmin + v :=
    map_range_getElem! bmin W v hv_lt
  have hglen : (grpAt cs (bmin + v) dec 0).length =
      cs.countP (· == bmin + v) := grpAt_length cs (bmin + v) dec 0
  rw [← hbase, flatMap_getElem!_block (fun w => grpAt cs w dec 0)
    ((List.range W).map (bmin + ·)) v ((cs.take o).countP (· == bmin + v))
    (by rw [List.length_map, List.length_range]; exact hv_lt)
    (by rw [hvget, hglen]; exact hr)]
  rw [hvget, grpAt_getElem! (bmin + v) dec cs 0 o ho hqo, Nat.zero_add]

/-- The placement crux: the element `segmentOf` produces at
`baseOff v + placed o v` (the counting-sort target slot for the
`o`-th member, whose count value offset is `v`) is exactly the member
`lab[cell1 + o]` the stable walk writes there. This is piece (a) of the
`nontrivialCell = nontrivialCellFast` activation: it identifies the
scatter destination with the specification's grouped output. -/
private theorem segmentOf_getElem!_placement (lab counts : Array Nat)
    (cell1 bmin W o : Nat)
    (hcv : countValues counts.toList = (List.range W).map (bmin + ·))
    (hmin : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (ho : o < counts.size) (hlt : counts[o]! - bmin < W) :
    (segmentOf lab cell1 counts.toList (countValues counts.toList))[
        baseOff counts bmin (counts[o]! - bmin) +
        placed counts bmin o (counts[o]! - bmin)]! = lab[cell1 + o]! := by
  have hmem : ∀ c ∈ counts.toList, bmin ≤ c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hsz : i < counts.size := by rw [Array.length_toList] at hi; exact hi
    rw [Array.getElem_toList, ← getElem!_pos counts i hsz]
    exact hmin i hsz
  have hbmin_o : bmin ≤ counts[o]! := hmin o ho
  have holen : o < counts.toList.length := by rw [Array.length_toList]; exact ho
  have hqo : (counts.toList[o]! == bmin + (counts[o]! - bmin)) = true := by
    rw [Array.getElem!_toList]; simp only [beq_iff_eq]; omega
  have hplaced_full : placed counts bmin counts.size (counts[o]! - bmin) =
      counts.toList.countP (· == bmin + (counts[o]! - bmin)) := by
    rw [placed_eq_take_countP counts bmin counts.size _ (Nat.le_refl _) hmin,
      List.take_of_length_le (Nat.le_of_eq Array.length_toList)]
  have hr : (counts.toList.take o).countP (· == bmin + (counts[o]! - bmin)) <
      counts.toList.countP (· == bmin + (counts[o]! - bmin)) := by
    rw [← placed_eq_take_countP counts bmin o _ (Nat.le_of_lt ho) hmin,
      ← hplaced_full]
    exact placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp)
  rw [baseOff_eq_countP,
    placed_eq_take_countP counts bmin o _ (Nat.le_of_lt ho) hmin]
  have hseg : segmentOf lab cell1 counts.toList (countValues counts.toList) =
      ((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt counts.toList w (fun j => lab[cell1 + j]!) 0) := by
    rw [hcv]; rfl
  rw [hseg]
  exact grouped_getElem! counts.toList (fun j => lab[cell1 + j]!) bmin W
    (counts[o]! - bmin) o hmem hlt holen hqo hr


/-! # The concrete `ntcPass` at the `nontrivialCellFast` call -/

/-- Prepending `f cell1` to the shifted window map reconstructs the full
`countsOf`-shaped map, when `cell1 ≤ cell2`. -/
private theorem cons_shift_map_eq {β : Type} (f : Nat → β) (cell1 cell2 : Nat)
    (h : cell1 ≤ cell2) :
    f cell1 :: (List.range (cell2 - cell1)).map (fun i => f (cell1 + 1 + i)) =
      (List.range (cell2 + 1 - cell1)).map (fun o => f (cell1 + o)) := by
  have hsucc : cell2 + 1 - cell1 = (cell2 - cell1) + 1 := by omega
  rw [hsucc, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 1
  omega

/-- The concrete counts pass reconstructs `countsOf` as its count array. -/
theorem ntcPass_concrete_counts (ctx : Ctx n) (lab : Array Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (h : cell1 ≤ cell2) :
    (ntcPass ctx lab workset cell1 (cell2 - cell1) 1
      ((Array.mkEmpty (cell2 + 1 - cell1)).push
        (workset.cardInter ctx.g[lab[cell1]!]!))
      ((Array.mkEmpty (cell2 + 1 - cell1)).push (lab[cell1]!))
      (workset.cardInter ctx.g[lab[cell1]!]!)
      (workset.cardInter ctx.g[lab[cell1]!]!)).1.toList =
      countsOf ctx lab workset cell1 cell2 := by
  have hempty : (Array.mkEmpty (cell2 + 1 - cell1) : Array Nat).toList = [] :=
    Array.toList_eq_nil_iff.mpr rfl
  rw [ntcPass_spec]
  simp only [Array.toList_append, Array.toList_push,
    hempty, List.nil_append, List.singleton_append]
  rw [countsOf]
  exact cons_shift_map_eq
    (fun o => workset.cardInter ctx.g[lab[o]!]!) cell1 cell2 h

/-- The concrete counts pass records the cell members in cell order. -/
theorem ntcPass_concrete_members (ctx : Ctx n) (lab : Array Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (h : cell1 ≤ cell2) :
    (ntcPass ctx lab workset cell1 (cell2 - cell1) 1
      ((Array.mkEmpty (cell2 + 1 - cell1)).push
        (workset.cardInter ctx.g[lab[cell1]!]!))
      ((Array.mkEmpty (cell2 + 1 - cell1)).push (lab[cell1]!))
      (workset.cardInter ctx.g[lab[cell1]!]!)
      (workset.cardInter ctx.g[lab[cell1]!]!)).2.1.toList =
      (List.range (cell2 + 1 - cell1)).map (fun o => lab[cell1 + o]!) := by
  have hempty : (Array.mkEmpty (cell2 + 1 - cell1) : Array Nat).toList = [] :=
    Array.toList_eq_nil_iff.mpr rfl
  rw [ntcPass_spec]
  simp only [Array.toList_append, Array.toList_push,
    hempty, List.nil_append, List.singleton_append]
  exact cons_shift_map_eq (fun o => lab[o]!) cell1 cell2 h

/-! # The placement against `writeSegment ∘ segmentOf`

`ntcPlace` walks the members in cell order, writing each at its
group's running position. Its stability equals the specification's
`writeSegment ∘ segmentOf` under the base-position invariant: after a
length-`o` prefix, group `v`'s cursor sits at `base v` plus the number
of already-placed value-`v` members. -/

/-- The absolute destination of the `o`-th member under the base
positions `base`: its group base plus the number of already-placed
members of its group. -/
private def dest (counts : Array Nat) (bmin : Nat) (base : Nat → Nat)
    (o : Nat) : Nat :=
  base (counts[o]! - bmin) + placed counts bmin o (counts[o]! - bmin)

/-- The scatter characterization: when the cursor array holds each
group's base plus its placed count, `ntcPlace` writes member `o` at
`dest o` for each `o` in the walked window, in order — a fold of
independent `set!`s. -/
private theorem ntcPlace_eq_fold (counts members : Array Nat) (bmin : Nat)
    (base : Nat → Nat) :
    ∀ (fuel o0 : Nat) (lab starts : Array Nat),
      (∀ w, w < starts.size →
        starts[w]! = base w + placed counts bmin o0 w) →
      (∀ o, o0 ≤ o → o < o0 + fuel → counts[o]! - bmin < starts.size) →
      (ntcPlace counts members bmin fuel o0 lab starts).1 =
        (List.range fuel).foldl
          (fun a k => a.set! (dest counts bmin base (o0 + k)) members[o0 + k]!)
          lab
  | 0, o0, lab, starts, _, _ => by simp [ntcPlace]
  | fuel + 1, o0, lab, starts, hinv, hbound => by
    rw [ntcPlace]
    have hvsz : counts[o0]! - bmin < starts.size :=
      hbound o0 (Nat.le_refl _) (by omega)
    have hpos : starts[counts[o0]! - bmin]! =
        base (counts[o0]! - bmin) + placed counts bmin o0 (counts[o0]! - bmin) :=
      hinv _ hvsz
    have hposdest : starts[counts[o0]! - bmin]! = dest counts bmin base o0 := by
      rw [hpos, dest]
    -- the recursive cursor array still satisfies the invariant at o0 + 1
    have hinv' : ∀ w, w < (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1)).size →
        (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1))[w]! =
          base w + placed counts bmin (o0 + 1) w := by
      intro w hw
      rw [Array.size_set!] at hw
      by_cases hwv : w = counts[o0]! - bmin
      · subst hwv
        rw [Array.getElem!_set!_self _ _ _ hw, hpos, placed_succ,
          ite_eq_left (by simp)]
        omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hwv h.symm), hinv w hw,
          placed_succ, ite_eq_right (by simpa using fun h => hwv h.symm)]
        omega
    have hbound' : ∀ o, o0 + 1 ≤ o → o < (o0 + 1) + fuel →
        counts[o]! - bmin < (starts.set! (counts[o0]! - bmin)
          (starts[counts[o0]! - bmin]! + 1)).size := by
      intro o ho1 ho2
      rw [Array.size_set!]
      exact hbound o (by omega) (by omega)
    rw [ntcPlace_eq_fold counts members bmin base fuel (o0 + 1)
      (lab.set! starts[counts[o0]! - bmin]! members[o0]!)
      (starts.set! (counts[o0]! - bmin) (starts[counts[o0]! - bmin]! + 1))
      hinv' hbound']
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rw [hposdest]
    have hik : ∀ k, o0 + 1 + k = o0 + (k + 1) := fun k => by omega
    simp only [hik, Nat.succ_eq_add_one, Nat.add_zero]

/-- A fold of `set!`s leaves a position it never writes to unchanged. -/
private theorem foldl_set!_not_mem {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) (p : Nat) :
    ∀ (l : List Nat) (a : Array α), (∀ o ∈ l, f o ≠ p) →
      (l.foldl (fun a o => a.set! (f o) (g o)) a)[p]! = a[p]!
  | [], _, _ => rfl
  | x :: xs, a, hne => by
    rw [List.foldl_cons,
      foldl_set!_not_mem f g p xs (a.set! (f x) (g x))
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)),
      Array.getElem!_set!_ne _ _ _ _ (hne x (List.mem_cons_self))]

/-- A fold of `set!`s at positions that are distinct on a duplicate-free
list reads back the value written at any given member. -/
private theorem foldl_set!_mem {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) :
    ∀ (l : List Nat) (a : Array α) (o0 : Nat), l.Nodup → o0 ∈ l →
      (∀ o ∈ l, o ≠ o0 → f o ≠ f o0) → f o0 < a.size →
      (l.foldl (fun a o => a.set! (f o) (g o)) a)[f o0]! = g o0
  | x :: xs, a, o0, hnd, ho0, hinj, hsz => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp ho0 with rfl | ho0'
    · rw [foldl_set!_not_mem f g (f o0) xs (a.set! (f o0) (g o0))
        (fun o ho => hinj o (List.mem_cons_of_mem _ ho)
          (fun h => hnd.1 (h ▸ ho))),
        Array.getElem!_set!_self _ _ _ hsz]
    · rw [foldl_set!_mem f g xs (a.set! (f x) (g x)) o0 hnd.2 ho0'
        (fun o ho => hinj o (List.mem_cons_of_mem _ ho))
        (by rw [Array.size_set!]; exact hsz)]

/-- `ntcPlace` preserves the labelling size (it only overwrites in
place). -/
theorem ntcPlace_size (counts members : Array Nat) (bmin : Nat) :
    ∀ (fuel o : Nat) (lab starts : Array Nat),
      (ntcPlace counts members bmin fuel o lab starts).1.size = lab.size
  | 0, _, _, _ => rfl
  | fuel + 1, o, lab, starts => by
    rw [ntcPlace, ntcPlace_size counts members bmin fuel (o + 1),
      Array.size_set!]

/-- `ntcPlace` preserves the cursor-array size. -/
theorem ntcPlace_starts_size (counts members : Array Nat) (bmin : Nat) :
    ∀ (fuel o : Nat) (lab starts : Array Nat),
      (ntcPlace counts members bmin fuel o lab starts).2.size = starts.size
  | 0, _, _, _ => rfl
  | fuel + 1, o, lab, starts => by
    rw [ntcPlace, ntcPlace_starts_size counts members bmin fuel (o + 1),
      Array.size_set!]

/-! # The initial cursor positions are the group bases -/

/-- The bucket, filled from all counts against a window-sized zero seed,
holds each group's multiplicity `placed … counts.size`. -/
private theorem ntcBucket_placed (counts : Array Nat) (bmin W : Nat)
    (hbound : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (v : Nat) (hv : v < W) :
    (ntcBucket counts bmin counts.size 0
        (Array.replicate W 0))[v]! =
      placed counts bmin counts.size v := by
  have hrange : ∀ q, 0 ≤ q → q < 0 + counts.size →
      counts[q]! - bmin < (Array.replicate W 0 : Array Nat).size := by
    intro q _ hq
    rw [Array.size_replicate]
    exact hbound q (by omega)
  rw [ntcBucket_spec counts bmin counts.size 0 (Array.replicate W 0)
    (by omega) hrange v (by rw [Array.size_replicate]; exact hv)]
  have hrep : (Array.replicate W 0 : Array Nat)[v]! = 0 := by
    rw [getElem!_pos _ v (by rw [Array.size_replicate]; exact hv),
      Array.getElem_replicate]
  rw [hrep, Nat.zero_add, placed, List.range_eq_range']

/-- The initial cursor array places group `w` at `cell1 + baseOff w`:
each start is the exclusive prefix sum of the earlier group
multiplicities, which is exactly `baseOff`. -/
private theorem ntcStarts_baseOff (counts bucket : Array Nat) (bmin W cell1 : Nat)
    (hbucket : ∀ v, v < W → bucket[v]! = placed counts bmin counts.size v)
    (w : Nat) (hw : w < W) :
    (ntcStarts bucket W cell1 #[])[w]! = cell1 + baseOff counts bmin w := by
  have hval := ntcStarts_value bucket W cell1 #[] w (by simpa using hw)
  simp only [Array.size_empty, Nat.zero_add] at hval
  rw [hval]
  have hmap : ((List.range w).map (fun j => bucket[j]!)) =
      (List.range w).map (fun j => placed counts bmin counts.size j) := by
    apply List.map_congr_left
    intro j hj
    exact hbucket j (by rw [List.mem_range] at hj; omega)
  rw [hmap, ← baseOff_eq_sum]

/-! # The scatter is a bijection onto the cell -/

/-- The offset (from `cell1`) of the `o`-th member's scatter
destination: its group base plus its within-group cursor. -/
private def destOff (counts : Array Nat) (bmin o : Nat) : Nat :=
  baseOff counts bmin (counts[o]! - bmin) +
    placed counts bmin o (counts[o]! - bmin)

/-- Every destination lands inside the cell `[0, counts.size)`. -/
private theorem destOff_lt (counts : Array Nat) (bmin W : Nat)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (o : Nat) (ho : o < counts.size) :
    destOff counts bmin o < counts.size := by
  have hv : counts[o]! - bmin < W := hbd o ho
  have hroom : placed counts bmin o (counts[o]! - bmin) <
      placed counts bmin counts.size (counts[o]! - bmin) :=
    placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp)
  have htile : baseOff counts bmin ((counts[o]! - bmin) + 1) ≤
      baseOff counts bmin W := baseOff_mono counts bmin (by omega)
  rw [baseOff_succ] at htile
  have hsize : baseOff counts bmin W = counts.size :=
    baseOff_eq_size counts bmin W hbd
  rw [destOff]
  omega

/-- The scatter is injective on the cell. -/
private theorem destOff_inj (counts : Array Nat) (bmin : Nat)
    {o o' : Nat} (ho : o < counts.size) (ho' : o' < counts.size)
    (hne : o ≠ o') : destOff counts bmin o ≠ destOff counts bmin o' := by
  by_cases hv : counts[o]! - bmin = counts[o']! - bmin
  · -- same group: within-group cursors differ
    rw [destOff, destOff, hv]
    have hne' : placed counts bmin o (counts[o']! - bmin) ≠
        placed counts bmin o' (counts[o']! - bmin) := by
      rcases Nat.lt_or_ge o o' with h | h
      · have h1 : placed counts bmin (o + 1) (counts[o']! - bmin) =
            placed counts bmin o (counts[o']! - bmin) + 1 := by
          rw [placed_succ, ite_eq_left (by rw [← hv]; simp)]
        have h2 : placed counts bmin (o + 1) (counts[o']! - bmin) ≤
            placed counts bmin o' (counts[o']! - bmin) :=
          placed_mono counts bmin _ (by omega)
        omega
      · have hlt : o' < o := by omega
        have h1 : placed counts bmin (o' + 1) (counts[o']! - bmin) =
            placed counts bmin o' (counts[o']! - bmin) + 1 := by
          rw [placed_succ, ite_eq_left (by simp)]
        have h2 : placed counts bmin (o' + 1) (counts[o']! - bmin) ≤
            placed counts bmin o (counts[o']! - bmin) :=
          placed_mono counts bmin _ (by omega)
        omega
    omega
  · -- distinct groups: disjoint base windows
    rw [destOff, destOff]
    exact baseOff_disjoint counts bmin hv
      (placed_lt_mult counts bmin o (counts[o]! - bmin) ho (by simp))
      (placed_lt_mult counts bmin o' (counts[o']! - bmin) ho' (by simp))

/-- A `Nodup` list of naturals, all below `N`, of length `N`, contains
every `k < N` — the pigeonhole surjectivity. -/
private theorem nodup_range_full (N : Nat) (l : List Nat) (hnd : l.Nodup)
    (hlen : l.length = N) (hlt : ∀ x ∈ l, x < N) :
    ∀ k, k < N → k ∈ l := by
  intro k hk
  rcases Decidable.em (k ∈ l) with h | h
  · exact h
  · exfalso
    have hsub : l ⊆ (List.range N).erase k := by
      intro x hx
      rw [List.mem_erase_of_ne (by rintro rfl; exact h hx)]
      exact List.mem_range.mpr (hlt x hx)
    have hle := List.Nodup.length_le_of_subset hnd hsub
    rw [List.length_erase, List.length_range] at hle
    simp only [List.mem_range.mpr hk, ite_true] at hle
    omega

/-- Every cell offset `j < counts.size` is some member's destination. -/
private theorem destOff_surj (counts : Array Nat) (bmin W : Nat)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (j : Nat) (hj : j < counts.size) :
    ∃ o, o < counts.size ∧ destOff counts bmin o = j := by
  have hlen : ((List.range counts.size).map
      (fun o => destOff counts bmin o)).length = counts.size := by
    rw [List.length_map, List.length_range]
  have hlt : ∀ x ∈ (List.range counts.size).map
      (fun o => destOff counts bmin o), x < counts.size := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact destOff_lt counts bmin W hbd o (List.mem_range.mp ho)
  have hnd : ((List.range counts.size).map
      (fun o => destOff counts bmin o)).Nodup := by
    show List.Pairwise (fun a b => a ≠ b)
      (List.map (fun o => destOff counts bmin o) (List.range counts.size))
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb hab heq
    exact destOff_inj counts bmin (List.mem_range.mp ha)
      (List.mem_range.mp hb) hab heq
  have hmem := nodup_range_full counts.size _ hnd hlen hlt j hj
  rw [List.mem_map] at hmem
  obtain ⟨o, ho, hoj⟩ := hmem
  exact ⟨o, List.mem_range.mp ho, hoj⟩

/-! # `ntcPlace` realises `writeSegment ∘ segmentOf` -/

/-- A fold of `set!`s preserves the array size. -/
private theorem foldl_set!_size {α : Type} [Inhabited α] (f : Nat → Nat)
    (g : Nat → α) :
    ∀ (l : List Nat) (a : Array α),
      (l.foldl (fun a k => a.set! (f k) (g k)) a).size = a.size
  | [], _ => rfl
  | x :: xs, a => by
    rw [List.foldl_cons, foldl_set!_size f g xs, Array.size_set!]

/-- Reading back one written slot: `writeSegment` puts `seg[j]` at
`lo + j` whenever that slot is inside the array, whether or not the
whole segment fits (writes past the end are `set!` no-ops). -/
private theorem writeSegment_getElem! :
    ∀ (seg : List Nat) (lab : Array Nat) (lo j : Nat), j < seg.length →
      lo + j < lab.size →
      (writeSegment lab lo seg)[lo + j]! = seg[j]!
  | [], _, _, j, hj, _ => absurd hj (by simp)
  | x :: seg, lab, lo, 0, _, hsz => by
    rw [writeSegment, List.getElem!_cons_zero]
    show (writeSegment (lab.set! lo x) (lo + 1) seg)[lo]! = x
    rw [writeSegment_outside seg _ (lo + 1) lo (Or.inl (by omega)),
      Array.getElem!_set!_self _ _ _ (by omega)]
  | x :: seg, lab, lo, j + 1, hj, hsz => by
    rw [writeSegment, List.getElem!_cons_succ,
      show lo + (j + 1) = (lo + 1) + j from by omega]
    exact writeSegment_getElem! seg (lab.set! lo x) (lo + 1) j
      (by simp only [List.length_cons] at hj; omega)
      (by rw [Array.size_set!]; omega)

private theorem array_ext! {α : Type} [Inhabited α] {A B : Array α}
    (hsize : A.size = B.size)
    (h : ∀ p, p < A.size → A[p]! = B[p]!) : A = B := by
  apply Array.ext hsize
  intro i hi1 hi2
  have hi := h i hi1
  rwa [getElem!_pos A i hi1, getElem!_pos B i hi2] at hi

/-- The scatter placement realises the specification's stable sort:
under the group-base cursor positions, `ntcPlace` writes each member
into its group slot, producing exactly `writeSegment ∘ segmentOf`. -/
private theorem ntcPlace_eq_writeSegment (lab counts members : Array Nat)
    (cell1 bmin W : Nat)
    (hmem : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (hcv : countValues counts.toList = (List.range W).map (bmin + ·))
    (hmembers : ∀ o, o < counts.size → members[o]! = lab[cell1 + o]!)
    (starts : Array Nat) (hssize : starts.size = W)
    (hs0 : ∀ w, w < W → starts[w]! = cell1 + baseOff counts bmin w) :
    (ntcPlace counts members bmin counts.size 0 lab starts).1 =
      writeSegment lab cell1
        (segmentOf lab cell1 counts.toList (countValues counts.toList)) := by
  -- the fold's destination and value functions
  have hfeq : ∀ k, dest counts bmin (fun w => cell1 + baseOff counts bmin w) k =
      cell1 + destOff counts bmin k := by
    intro k; rw [dest, destOff]; omega
  have hfrange : ∀ k, k < counts.size →
      cell1 ≤ dest counts bmin (fun w => cell1 + baseOff counts bmin w) k ∧
      dest counts bmin (fun w => cell1 + baseOff counts bmin w) k <
        cell1 + counts.size := by
    intro k hk
    rw [hfeq k]
    exact ⟨by omega, by have := destOff_lt counts bmin W hbd k hk; omega⟩
  -- ntcPlace unfolds to a scatter fold
  have hfold := ntcPlace_eq_fold counts members bmin
    (fun w => cell1 + baseOff counts bmin w) counts.size 0 lab starts
    (by intro w hw; rw [placed_zero, Nat.add_zero]
        exact hs0 w (by rw [← hssize]; exact hw))
    (by intro o _ ho; rw [hssize]; exact hbd o (by omega))
  rw [hfold]
  simp only [Nat.zero_add]
  -- name the specification segment
  obtain ⟨seg, hseg⟩ :
      ∃ seg, seg = segmentOf lab cell1 counts.toList (countValues counts.toList) :=
    ⟨_, rfl⟩
  rw [← hseg]
  have hmem' : ∀ c ∈ counts.toList, bmin ≤ c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hsz : i < counts.size := by rw [Array.length_toList] at hi; exact hi
    rw [Array.getElem_toList, ← getElem!_pos counts i hsz]
    exact hmem i hsz
  have hseglen : seg.length = counts.size := by
    have hflat : seg = ((List.range W).map (bmin + ·)).flatMap
        (fun w => grpAt counts.toList w (fun j => lab[cell1 + j]!) 0) := by
      rw [hseg, hcv]; rfl
    rw [hflat, flatMap_grpAt_length counts.toList _ bmin hmem' W,
      ← baseOff_eq_countP, baseOff_eq_size counts bmin W hbd]
  have hsz : ((List.range counts.size).foldl
      (fun a k => a.set!
        (dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
        members[k]!) lab).size = lab.size :=
    foldl_set!_size _ _ (List.range counts.size) lab
  refine array_ext! ?_ ?_
  · rw [hsz, writeSegment_size]
  · intro p hp
    rw [hsz] at hp
    by_cases hpc : cell1 ≤ p ∧ p < cell1 + counts.size
    · -- inside the cell: p = cell1 + (p - cell1)
      obtain ⟨hp1, hp2⟩ := hpc
      have hjlt : p - cell1 < counts.size := by omega
      have hpj : p = cell1 + (p - cell1) := by omega
      obtain ⟨o, ho, hoj⟩ := destOff_surj counts bmin W hbd (p - cell1) hjlt
      have hfo : dest counts bmin (fun w => cell1 + baseOff counts bmin w) o = p := by
        rw [hfeq o, hoj]; omega
      have hinj : ∀ k ∈ List.range counts.size, k ≠ o →
          dest counts bmin (fun w => cell1 + baseOff counts bmin w) k ≠
          dest counts bmin (fun w => cell1 + baseOff counts bmin w) o := by
        intro k hk hkne
        rw [hfeq k, hfeq o]
        have := destOff_inj counts bmin (List.mem_range.mp hk) ho hkne
        omega
      have hlhs := foldl_set!_mem
        (fun k => dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
        (fun k => members[k]!) (List.range counts.size) lab o
        List.nodup_range (List.mem_range.mpr ho) hinj (by rw [hfo]; omega)
      rw [hfo] at hlhs
      rw [hlhs, hmembers o ho]
      -- RHS reads seg[p - cell1]!
      have hrhs : (writeSegment lab cell1 seg)[p]! = seg[p - cell1]! := by
        have hw := writeSegment_getElem! seg lab cell1 (p - cell1)
          (by rw [hseglen]; exact hjlt) (by omega)
        rwa [← hpj] at hw
      rw [hrhs, hseg]
      have hcrux := segmentOf_getElem!_placement lab counts cell1 bmin W o
        hcv hmem ho (hbd o ho)
      rw [show p - cell1 = baseOff counts bmin (counts[o]! - bmin) +
          placed counts bmin o (counts[o]! - bmin) by
        rw [← destOff]; exact hoj.symm]
      exact hcrux.symm
    · -- outside the cell: both give lab[p]!
      have hlhs : ((List.range counts.size).foldl
          (fun a k => a.set!
            (dest counts bmin (fun w => cell1 + baseOff counts bmin w) k)
            members[k]!) lab)[p]! = lab[p]! := by
        apply foldl_set!_not_mem
        intro k hk
        have := hfrange k (List.mem_range.mp hk)
        omega
      have hrhs : (writeSegment lab cell1 seg)[p]! = lab[p]! := by
        apply writeSegment_outside
        rw [hseglen]; omega
      rw [hlhs, hrhs]

/-! # The extrema and multiplicity transports -/

private theorem foldl_min_le_init :
    ∀ (l : List Nat) (a : Nat), l.foldl Nat.min a ≤ a
  | [], a => Nat.le_refl a
  | x :: l, a =>
    Nat.le_trans (foldl_min_le_init l (Nat.min a x)) (Nat.min_le_left a x)

private theorem foldl_min_le_mem :
    ∀ (l : List Nat) (a x : Nat), x ∈ l → l.foldl Nat.min a ≤ x
  | [], _, _, hx => absurd hx (by simp)
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (foldl_min_le_init l (Nat.min a x))
        (Nat.min_le_right a x)
    · exact foldl_min_le_mem l (Nat.min a y) x hx'

private theorem le_foldl_max_init :
    ∀ (l : List Nat) (a : Nat), a ≤ l.foldl Nat.max a
  | [], a => Nat.le_refl a
  | x :: l, a =>
    Nat.le_trans (Nat.le_max_left a x) (le_foldl_max_init l (Nat.max a x))

private theorem le_foldl_max_mem :
    ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl Nat.max a
  | [], _, _, hx => absurd hx (by simp)
  | y :: l, a, x, hx => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (Nat.le_max_right a x)
        (le_foldl_max_init l (Nat.max a x))
    · exact le_foldl_max_mem l (Nat.max a y) x hx'

/-- The head-seeded extremum fold over the shifted window equals the
specification's `headD`-seeded fold over the whole count list: one
idempotence step strips the doubled head. -/
private theorem foldl_extremum_shift (op : Nat → Nat → Nat)
    (hidem : ∀ a, op a a = a) (f : Nat → Nat) (cell1 cell2 : Nat)
    (h : cell1 ≤ cell2) :
    (List.range (cell2 - cell1)).foldl
        (fun b i => op b (f (cell1 + 1 + i))) (f cell1) =
      ((List.range (cell2 + 1 - cell1)).map (fun o => f (cell1 + o))).foldl op
        (((List.range (cell2 + 1 - cell1)).map
          (fun o => f (cell1 + o))).headD 0) := by
  rw [← cons_shift_map_eq f cell1 cell2 h, List.headD_cons, List.foldl_cons,
    hidem, List.foldl_map]

/-- The concrete counts pass folds the specification's count minimum. -/
theorem ntcPass_concrete_bmin (ctx : Ctx n) (lab : Array Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (h : cell1 ≤ cell2) :
    (ntcPass ctx lab workset cell1 (cell2 - cell1) 1
      ((Array.mkEmpty (cell2 + 1 - cell1)).push
        (workset.cardInter ctx.g[lab[cell1]!]!))
      ((Array.mkEmpty (cell2 + 1 - cell1)).push (lab[cell1]!))
      (workset.cardInter ctx.g[lab[cell1]!]!)
      (workset.cardInter ctx.g[lab[cell1]!]!)).2.2.1 =
      (countsOf ctx lab workset cell1 cell2).foldl Nat.min
        ((countsOf ctx lab workset cell1 cell2).headD 0) := by
  rw [ntcPass_spec, countsOf]
  exact foldl_extremum_shift Nat.min Nat.min_self
    (fun o => workset.cardInter ctx.g[lab[o]!]!) cell1 cell2 h

/-- The concrete counts pass folds the specification's count maximum. -/
theorem ntcPass_concrete_bmax (ctx : Ctx n) (lab : Array Nat)
    (workset : VSet n) (cell1 cell2 : Nat) (h : cell1 ≤ cell2) :
    (ntcPass ctx lab workset cell1 (cell2 - cell1) 1
      ((Array.mkEmpty (cell2 + 1 - cell1)).push
        (workset.cardInter ctx.g[lab[cell1]!]!))
      ((Array.mkEmpty (cell2 + 1 - cell1)).push (lab[cell1]!))
      (workset.cardInter ctx.g[lab[cell1]!]!)
      (workset.cardInter ctx.g[lab[cell1]!]!)).2.2.2 =
      (countsOf ctx lab workset cell1 cell2).foldl Nat.max
        ((countsOf ctx lab workset cell1 cell2).headD 0) := by
  rw [ntcPass_spec, countsOf]
  exact foldl_extremum_shift Nat.max Nat.max_self
    (fun o => workset.cardInter ctx.g[lab[o]!]!) cell1 cell2 h

/-- The bucket over the full count window holds the specification
multiplicities. -/
private theorem ntcBucket_multOf (counts : Array Nat) (bmin W : Nat)
    (hmin : ∀ q, q < counts.size → bmin ≤ counts[q]!)
    (hbd : ∀ q, q < counts.size → counts[q]! - bmin < W)
    (v : Nat) (hv : v < W) :
    (ntcBucket counts bmin counts.size 0 (Array.replicate W 0))[v]! =
      multOf counts.toList (bmin + v) := by
  rw [ntcBucket_placed counts bmin W hbd v hv,
    placed_eq_take_countP counts bmin counts.size v (Nat.le_refl _) hmin,
    List.take_of_length_le (Nat.le_of_eq Array.length_toList), multOf]

/-- The bucket-array counting sort computes the specification's cell
processing: one counts pass, the multiplicity bucket, the bucket-driven
window scan, and the stable placement replay `nontrivialCell` exactly.
The `@[csimp]` makes every compiled call site run the O(cell + window)
fast path in place of the O(cell x window) `multOf` scan and
`segmentOf` redistribution. -/
@[csimp] theorem nontrivialCell_eq_fast :
    @nontrivialCell = @nontrivialCellFast := by
  funext n ctx level workset cell1 cell2 st
  rw [nontrivialCell, nontrivialCellFast]
  rcases Decidable.em ((cell1 == cell2) = true) with h12 | h12
  · rw [ite_eq_left h12, ite_eq_left h12]
  · rw [ite_eq_right h12, ite_eq_right h12]
    rcases Decidable.em (cell2 < cell1) with h21 | h21
    · -- empty window: the specification's extrema collapse to 0
      rw [ite_eq_left h21]
      have hempty : countsOf ctx st.lab workset cell1 cell2 = [] := by
        rw [countsOf, show cell2 + 1 - cell1 = 0 from by omega,
          List.range_zero, List.map_nil]
      rw [hempty]
      simp
    · rw [ite_eq_right h21]
      have hle : cell1 ≤ cell2 := by omega
      dsimp only
      generalize hr : ntcPass ctx st.lab workset cell1 (cell2 - cell1) 1
        ((Array.mkEmpty (cell2 + 1 - cell1)).push
          (workset.cardInter ctx.g[st.lab[cell1]!]!))
        ((Array.mkEmpty (cell2 + 1 - cell1)).push st.lab[cell1]!)
        (workset.cardInter ctx.g[st.lab[cell1]!]!)
        (workset.cardInter ctx.g[st.lab[cell1]!]!) = r
      obtain ⟨counts, members, bmin, bmax⟩ := r
      dsimp only
      have hcounts : counts.toList = countsOf ctx st.lab workset cell1 cell2 := by
        have h := ntcPass_concrete_counts ctx st.lab workset cell1 cell2 hle
        rw [hr] at h
        exact h
      have hbminE : bmin =
          (countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
            ((countsOf ctx st.lab workset cell1 cell2).headD 0) := by
        have h := ntcPass_concrete_bmin ctx st.lab workset cell1 cell2 hle
        rw [hr] at h
        exact h
      have hbmaxE : bmax =
          (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
            ((countsOf ctx st.lab workset cell1 cell2).headD 0) := by
        have h := ntcPass_concrete_bmax ctx st.lab workset cell1 cell2 hle
        rw [hr] at h
        exact h
      rw [← hbminE, ← hbmaxE]
      rcases Decidable.em ((bmin == bmax) = true) with heq | heq
      · rw [ite_eq_left heq, ite_eq_left heq]
      · rw [ite_eq_right heq, ite_eq_right heq]
        have hmemL : ∀ q, q < counts.size →
            counts[q]! ∈ countsOf ctx st.lab workset cell1 cell2 := by
          intro q hq
          have hql : q < (countsOf ctx st.lab workset cell1 cell2).length := by
            rw [← hcounts, Array.length_toList]
            exact hq
          have hgq : counts[q]! =
              (countsOf ctx st.lab workset cell1 cell2)[q]! := by
            rw [← hcounts, Array.getElem!_toList]
          rw [hgq, getElem!_pos _ q hql]
          exact List.getElem_mem hql
        have hmin : ∀ q, q < counts.size → bmin ≤ counts[q]! := by
          intro q hq
          rw [hbminE]
          exact foldl_min_le_mem _ _ _ (hmemL q hq)
        have hbd : ∀ q, q < counts.size →
            counts[q]! - bmin < bmax + 1 - bmin := by
          intro q hq
          have h1 := hmin q hq
          have h2 : counts[q]! ≤ bmax := by
            rw [hbmaxE]
            exact le_foldl_max_mem _ _ _ (hmemL q hq)
          omega
        have hcv : countValues counts.toList =
            (List.range (bmax + 1 - bmin)).map (bmin + ·) := by
          rw [hcounts, countValues, ← hbminE, ← hbmaxE]
        -- the scan half
        have hscan := ntcScan_eq_windowScan level cell1 cell2 bmin
          (ntcBucket counts bmin counts.size 0
            (Array.replicate (bmax + 1 - bmin) 0))
          (countsOf ctx st.lab workset cell1 cell2)
          (bmax + 1 - bmin) 0 cell1 (-1) st
          (by
            intro i hi
            rw [Nat.zero_add, show bmin + 0 + i = bmin + i from by omega,
              ← hcounts]
            exact ntcBucket_multOf counts bmin (bmax + 1 - bmin) hmin hbd i hi)
        simp only [Nat.add_zero] at hscan
        rw [← hcv, hcounts] at hscan
        rw [hscan, windowScan_lab]
        -- the placement half
        have hcsize : counts.size = cell2 + 1 - cell1 := by
          rw [← Array.length_toList, hcounts, countsOf, List.length_map,
            List.length_range]
        have hmembers : ∀ o, o < counts.size →
            members[o]! = st.lab[cell1 + o]! := by
          intro o ho
          have hmlist := ntcPass_concrete_members ctx st.lab workset cell1
            cell2 hle
          rw [hr] at hmlist
          have hlen : o < ((List.range (cell2 + 1 - cell1)).map
              (fun o => st.lab[cell1 + o]!)).length := by
            rw [List.length_map, List.length_range, ← hcsize]
            exact ho
          rw [← Array.getElem!_toList, hmlist, getElem!_pos _ o hlen,
            List.getElem_map, List.getElem_range]
        have hssize : (ntcStarts (ntcBucket counts bmin counts.size 0
            (Array.replicate (bmax + 1 - bmin) 0)) (bmax + 1 - bmin) cell1
            #[]).size = bmax + 1 - bmin := by
          rw [ntcStarts_size]
          simp
        have hs0 := ntcStarts_baseOff counts
          (ntcBucket counts bmin counts.size 0
            (Array.replicate (bmax + 1 - bmin) 0))
          bmin (bmax + 1 - bmin) cell1
          (fun v hv => ntcBucket_placed counts bmin (bmax + 1 - bmin) hbd v hv)
        have hplace := ntcPlace_eq_writeSegment st.lab counts members cell1
          bmin (bmax + 1 - bmin) hmin hbd hcv hmembers _ hssize hs0
        rw [hcounts] at hplace
        rw [hplace]

/-- One splitting pass of `refine` for a nontrivial splitter cell
`lab[split1..split2]`.

nauty's `bucket` scratch is reproduced semantically: the multiplicity
window over `[bmin, bmax]` and the stable counting redistribution give
exactly the array contents nauty's incremental window zeroing and
placement loop produce. -/
@[expose] def refineNontrivial (ctx : Ctx n) (level split1 split2 : Nat)
    (st : RefineSt n) : RefineSt n :=
  let workset := worksetOf n st.lab split1 split2
  let st := { st with longcode := mash st.longcode (split2 - split1 + 1) }
  go workset (cells st.ptn level n) st
where
  go (workset : VSet n) : List (Nat × Nat) → RefineSt n → RefineSt n
    | [], st => st
    | (cell1, cell2) :: rest, st =>
      go workset rest (nontrivialCell ctx level workset cell1 cell2 st)

/-- `refineNontrivial` with the cell walk fused over a partition
snapshot, mirroring `refineTrivialFast`. Runtime form of
`refineNontrivial`. -/
@[expose] def refineNontrivialFast (ctx : Ctx n) (level split1 split2 : Nat)
    (st : RefineSt n) : RefineSt n :=
  let workset := worksetOf n st.lab split1 split2
  let st := { st with longcode := mash st.longcode (split2 - split1 + 1) }
  go workset st.ptn n 0 st
where
  go (workset : VSet n) (ptn0 : Array Nat) :
      Nat → Nat → RefineSt n → RefineSt n
    | 0, _, st => st
    | fuel + 1, c1, st =>
      if c1 < n then
        let c2 := cellEnd ptn0 level c1
        go workset ptn0 fuel (c2 + 1)
          (nontrivialCell ctx level workset c1 c2 st)
      else
        st

theorem refineNontrivialFast_go_eq (ctx : Ctx n) (level : Nat)
    (workset : VSet n) (ptn0 : Array Nat) :
    ∀ (fuel c1 : Nat) (st : RefineSt n),
      refineNontrivialFast.go ctx level workset ptn0 fuel c1 st =
        refineNontrivial.go ctx level workset
          (cells.go ptn0 level n fuel c1) st
  | 0, _, _ => by
    rw [refineNontrivialFast.go, cells.go, refineNontrivial.go]
  | fuel + 1, c1, st => by
    rw [refineNontrivialFast.go, cells.go]
    rcases Decidable.em (c1 < n) with h | h
    · rw [ite_eq_left h, ite_eq_left h, refineNontrivial.go]
      exact refineNontrivialFast_go_eq ctx level workset ptn0 fuel _ _
    · rw [ite_eq_right h, ite_eq_right h, refineNontrivial.go]

@[csimp] theorem refineNontrivial_eq_fast :
    @refineNontrivial = @refineNontrivialFast := by
  funext n ctx level split1 split2 st
  rw [refineNontrivial, refineNontrivialFast, cells]
  exact (refineNontrivialFast_go_eq ctx level _ _ n 0 _).symm

/-- One iteration of `refine`'s active-cell loop: remove the chosen
splitter from the active set and perform its splitting pass. -/
@[expose] def refineStep (ctx : Ctx n) (level split1 : Nat) (st : RefineSt n) :
    RefineSt n :=
  let st := { st with active := st.active.erase split1 }
  let split2 := cellEnd st.ptn level split1
  let st := { st with longcode := mash st.longcode (split1 + split2) }
  if split1 == split2 then
    refineTrivial ctx level split1 st
  else
    refineNontrivial ctx level split1 split2 st

@[expose] def refineLoop (ctx : Ctx n) (level : Nat) :
    Nat → RefineSt n → RefineSt n
  | 0, st => st
  | fuel + 1, st =>
    if st.numcells < n then
      match pickSplit st.active st.hint with
      | some split1 => refineLoop ctx level fuel (refineStep ctx level split1 st)
      | none => st
    else
      st

/-- nauty's `refine`: make the partition at `level` equitable with respect
to the active cells, producing the refinement code. With the pinned
options (`invarproc = NULL`) this is also the whole of `doref`. -/
@[expose] def refine (ctx : Ctx n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) : RefineSt n :=
  let st : RefineSt n :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  let st := refineLoop ctx level (4 * n + 8) st
  { st with longcode := cleanup (mash st.longcode st.numcells) }

/-- nauty's `cheapautom`: a cheap sufficient condition for the partition
to have automorphisms rearranging only its nontrivial cells. -/
@[expose] def cheapautom (ptn : Array Nat) (level n : Nat) : Bool :=
  let (k, nnt) := go n 0 n 0
  k ≤ nnt + 1 ∨ k ≤ 4
where
  go : Nat → Nat → Nat → Nat → (Nat × Nat)
    | 0, _, k, nnt => (k, nnt)
    | fuel + 1, i, k, nnt =>
      if i < ptn.size then
        let k := k - 1
        if ptn[i]! > level then
          let j := cellEnd ptn level (i + 1)
          go fuel (j + 1) k (nnt + 1)
        else
          go fuel (i + 1) k nnt
      else
        (k, nnt)

/-- One `v2` round of `bestcell`'s joined-cell count: bump the counts of
`v2` and each earlier nonsingleton cell nontrivially joined to it. -/
@[expose] def bestcellRow (ctx : Ctx n) (lab startArr : Array Nat)
    (workset : VSet n) (v2 : Nat) : List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    -- nauty tests `workset & gp ≠ 0` and `workset & ~gp ≠ 0`; the second
    -- says `workset` is not contained in the row.
    if ¬ workset.interIsEmpty ctx.g[lab[startArr[v1]!]!]! ∧
        ¬ workset.subset ctx.g[lab[startArr[v1]!]!]! then
      bestcellRow ctx lab startArr workset v2 rest
        ((bucket.set! v1 (bucket[v1]! + 1)).set! v2 (bucket[v2]! + 1))
    else
      bestcellRow ctx lab startArr workset v2 rest bucket

@[expose] def bestcellRows (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat)
    (startArr : Array Nat) : List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    bestcellRows ctx lab ptn level startArr rest
      (bestcellRow ctx lab startArr
        (worksetOf n lab startArr[v2]! (cellEnd ptn level startArr[v2]!))
        v2 (List.range v2) bucket)

/-- The position of the greatest count, first maximum winning. -/
@[expose] def argmaxLoop (bucket : Array Nat) : List Nat → Nat → Nat → Nat
  | [], v1, _ => v1
  | i :: rest, v1, v2 =>
    if bucket[i]! > v2 then
      argmaxLoop bucket rest i bucket[i]!
    else
      argmaxLoop bucket rest v1 v2

/-- nauty's `bestcell`: the first cell nontrivially joined to the greatest
number of other nonsingleton cells, as a `lab` position; `n` when every
cell is a singleton. -/
@[expose] def bestcell (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat) : Nat :=
  let starts := ((cells ptn level n).filter fun (c1, c2) => c1 ≠ c2).map (·.1)
  let nnt := starts.length
  if nnt == 0 then
    n
  else
    let startArr := starts.toArray
    let bucket := bestcellRows ctx lab ptn level startArr
      (List.range' 1 (nnt - 1)) (Array.replicate nnt 0)
    startArr[argmaxLoop bucket (List.range' 1 (nnt - 1)) 0 bucket[0]!]!

/-- nauty's `targetcell` for the pinned undirected configuration. -/
@[expose] def targetcell (ctx : Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) : Nat :=
  if hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      (hint == 0 ∨ ptn[hint.toNat - 1]! ≤ level) then
    hint.toNat
  else if level ≤ tcLevel then
    bestcell ctx lab ptn level
  else
    let i := (cells ptn level n).find? (fun (c1, c2) => c1 ≠ c2)
    match i with
    | some (c1, _) => c1
    | none => 0

/-- nauty's `maketargetcell`: the chosen cell's position, contents, and
size. -/
@[expose] def maketargetcell (ctx : Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) : Nat × VSet n × Nat :=
  let i := targetcell ctx lab ptn level tcLevel hint
  let j := cellEnd ptn level (i + 1)
  (i, worksetOf n lab i j, j - i + 1)

/-- nauty's `breakout`: split `{tv}` off the front of the cell starting at
`tc`, shifting the displaced vertices one place right, and make `tc` the
only active position. -/
@[expose] def breakout (n : Nat) (lab ptn : Array Nat) (level tc tv : Nat) :
    Array Nat × Array Nat × VSet n :=
  let lab := go (lab.size + 1) lab tc tv
  (lab, ptn.set! tc level, VSet.empty.insert tc)
where
  go : Nat → Array Nat → Nat → Nat → Array Nat
    | 0, lab, _, _ => lab
    | fuel + 1, lab, i, prev =>
      let next := lab[i]!
      let lab := lab.set! i prev
      if next == tv then lab else go fuel lab (i + 1) next

/-- nauty's `isautom` for undirected graphs: `perm` maps edges to edges,
checking each edge from its lesser endpoint. -/
@[expose] def isautom (ctx : Ctx n) (perm : Array Nat) : Bool := Id.run do
  for i in [0 : n] do
    let row := ctx.g[i]!
    for pos in row.toList do
      if pos > i then
        if ¬ ctx.g[perm[i]!]!.mem perm[pos]! then
          return false
  return true

/-- The inverse of a vertex list: `inv[lab[i]] = i`. -/
@[expose] def invPerm (lab : Array Nat) : Array Nat :=
  go (List.range lab.size) (Array.replicate lab.size 0)
where
  go : List Nat → Array Nat → Array Nat
    | [], inv => inv
    | i :: rest, inv => go rest (inv.set! lab[i]! i)

/-- nauty's `testcanlab`: compare `g^lab` with `canong` row by row in
nauty's setword order. Returns the comparison and the number of leading
equal rows. -/
@[expose] def testcanlab (ctx : Ctx n) (canong : Array (VSet n))
    (lab : Array Nat) : Int × Nat := Id.run do
  let w := invPerm lab
  for i in [0 : n] do
    let row := ctx.g[lab[i]!]!.permset w
    match row.rowCmp canong[i]! with
    | .lt => return (-1, i)
    | .gt => return (1, i)
    | .eq => pure ()
  return (0, n)

/-- nauty's `updatecan`: overwrite rows `samerows..n-1` of `canong` with
the corresponding rows of `g^lab`. -/
@[expose] def updatecan (ctx : Ctx n) (canong : Array (VSet n))
    (lab : Array Nat) (samerows : Nat) : Array (VSet n) := Id.run do
  let w := invPerm lab
  let mut canong := canong
  for i in [samerows : n] do
    canong := canong.set! i (ctx.g[lab[i]!]!.permset w)
  return canong

/-- nauty's `fmperm`: the fixed points of a permutation and the least
point of each cycle. -/
@[expose] def fmperm (perm : Array Nat) (n : Nat) : VSet n × VSet n := Id.run do
  let mut fix : VSet n := .empty
  let mut mcr : VSet n := .empty
  let mut seen : Array Bool := .replicate n false
  for i in [0 : n] do
    if perm[i]! == i then
      fix := fix.insert i
      mcr := mcr.insert i
    else if ¬ seen[i]! then
      let mut l := i
      for _ in [0 : n] do
        seen := seen.set! l true
        l := perm[l]!
        if l == i then
          break
      mcr := mcr.insert i
  return (fix, mcr)

/-- nauty's `fmptn`: the vertices in singleton cells of the partition at
`level`, and the least vertex of each cell. -/
@[expose] def fmptn (lab ptn : Array Nat) (level n : Nat) : VSet n × VSet n :=
    Id.run do
  let mut fix : VSet n := .empty
  let mut mcr : VSet n := .empty
  for (c1, c2) in cells ptn level n do
    if c1 == c2 then
      fix := fix.insert lab[c1]!
      mcr := mcr.insert lab[c1]!
    else
      let mut lmin := lab[c1]!
      for i in [c1 + 1 : c2 + 1] do
        if lab[i]! < lmin then
          lmin := lab[i]!
      mcr := mcr.insert lmin
  return (fix, mcr)

/-- nauty's `orbjoin`: join the orbit cells so that `i` and `map[i]` are
equivalent, returning the new orbit array and count. -/
@[expose] def orbjoin (orbits : Array Nat) (map : Array Nat) (n : Nat) :
    Array Nat × Nat := Id.run do
  let mut orbits := orbits
  for i in [0 : n] do
    if map[i]! != i then
      let mut j1 := orbits[i]!
      for _ in [0 : n] do
        if orbits[j1]! == j1 then break
        j1 := orbits[j1]!
      let mut j2 := orbits[map[i]!]!
      for _ in [0 : n] do
        if orbits[j2]! == j2 then break
        j2 := orbits[j2]!
      if j1 < j2 then
        orbits := orbits.set! j2 j1
      else if j1 > j2 then
        orbits := orbits.set! j1 j2
  let mut count := 0
  for i in [0 : n] do
    orbits := orbits.set! i orbits[orbits[i]!]!
    if orbits[i]! == i then
      count := count + 1
  return (orbits, count)

end Hex.GraphIso.Nauty
