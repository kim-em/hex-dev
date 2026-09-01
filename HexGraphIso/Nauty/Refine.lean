/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Bits

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

/-- nauty's refinement-code accumulator step: `MASH(l, i)` from
`naugraph.c`. All inputs are nonnegative positions, sizes, or counts, so
`Nat` arithmetic reproduces the C `long` arithmetic exactly. -/
@[inline] def mash (l i : Nat) : Nat :=
  ((l ^^^ 0o65435) + i) &&& 0o77777

/-- nauty's `CLEANUP` of an accumulated refinement code. -/
@[inline] def cleanup (l : Nat) : Nat :=
  l % 0o77777

/-- The graph as adjacency bitset rows, with the vertex count. -/
structure Ctx where
  /-- The number of vertices. -/
  n : Nat
  /-- Row `v` is the neighbour set of vertex `v`. -/
  g : Array Nat
deriving Inhabited

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

/-- Working state of one `refine` call. -/
structure RefineSt where
  lab : Array Nat
  ptn : Array Nat
  active : Nat
  numcells : Nat
  hint : Nat
  maxpos : Nat
  longcode : Nat

/-- The next active splitting cell: nauty tries `hint` first, then the
next active position after it, then wraps to the least active position. -/
@[expose] def pickSplit (active hint : Nat) : Option Nat :=
  if elem active hint then
    some hint
  else
    match nextElem active (some hint) with
    | some v => some v
    | none => nextElem active none

/-- The two-pointer partition of `lab[c1..c2]` by adjacency to the trivial
splitter: adjacent vertices collect on the left in order, non-adjacent
vertices on the right in reversed order, exactly as nauty's swap loop
leaves them. Returns the final `(lab, c1, c2)`. -/
@[expose] def splitCellLoop (gRow : Nat) : Nat → Array Nat → Int → Int → (Array Nat × Int × Int)
  | 0, lab, c1, c2 => (lab, c1, c2)
  | fuel + 1, lab, c1, c2 =>
    if c1 ≤ c2 then
      if elem gRow lab[c1.toNat]! then
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
    (st : RefineSt) : RefineSt :=
  if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
    if elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat then
      if c1.toNat == cell2 then
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insert st.active c1.toNat
          hint := c1.toNat }
      else
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insert st.active c1.toNat }
    else
      if c2.toNat == cell1 then
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insert st.active cell1
          hint := cell1 }
      else
        { st with
          ptn := st.ptn.set! c2.toNat level
          longcode := mash st.longcode c2.toNat
          numcells := st.numcells + 1
          active := insert st.active cell1 }
  else
    st

/-- One cell's processing in the trivial-splitter pass: two-pointer
partition by adjacency, then the split bookkeeping. -/
@[expose] def trivialCell (level : Nat) (gRow : Nat) (cell1 cell2 : Nat)
    (st : RefineSt) : RefineSt :=
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
@[expose] def refineTrivial (ctx : Ctx) (level split1 : Nat) (st : RefineSt) : RefineSt :=
  go (ctx.g[st.lab[split1]!]!) (cells st.ptn level ctx.n) st
where
  go (gRow : Nat) : List (Nat × Nat) → RefineSt → RefineSt
    | [], st => st
    | (cell1, cell2) :: rest, st => go gRow rest (trivialCell level gRow cell1 cell2 st)

/-- The splitter cell's vertex set: the members of `lab[lo..hi]`. -/
@[expose] def worksetOf (lab : Array Nat) (lo hi : Nat) : Nat :=
  (List.range (hi + 1 - lo)).foldl (fun w o => insert w lab[lo + o]!) 0

/-- The neighbour counts of a cell's members into the splitter set, in
cell order. -/
@[expose] def countsOf (ctx : Ctx) (lab : Array Nat) (workset cell1 cell2 : Nat) :
    List Nat :=
  (List.range (cell2 + 1 - cell1)).map fun o =>
    popCount (workset &&& ctx.g[lab[cell1 + o]!]!)

/-- The multiplicity of count value `v` in a count list. -/
@[expose] def multOf (counts : List Nat) (v : Nat) : Nat :=
  counts.countP (· == v)

/-- One nonempty count group's bookkeeping in the window scan: code
contribution, `maxpos` of the largest group so far, the group boundary
with its active-set entry, and the new cell end. Touches no labelling
data. -/
@[expose] def windowStep (level cell1 cell2 v c1 c2 : Nat) (maxcell : Int)
    (st : RefineSt) : RefineSt :=
  let st := { st with longcode := mash st.longcode (v + c1) }
  let st :=
    if Int.ofNat (c2 - c1) > maxcell then { st with maxpos := c1 } else st
  let st :=
    if c1 != cell1 then
      let st := { st with
        active := insert st.active c1
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
    List Nat → Nat → Int → RefineSt → RefineSt
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
@[expose] def nontrivialFix (cell1 : Nat) (st : RefineSt) : RefineSt :=
  if ¬ elem st.active cell1 then
    { st with active := erase (insert st.active cell1) st.maxpos }
  else
    st

/-- One cell's processing in the nontrivial-splitter pass. -/
@[expose] def nontrivialCell (ctx : Ctx) (level : Nat) (workset cell1 cell2 : Nat)
    (st : RefineSt) : RefineSt :=
  if cell1 == cell2 then
    st
  else
    let counts := countsOf ctx st.lab workset cell1 cell2
    let bmin := counts.foldl Nat.min (counts.headD 0)
    let bmax := counts.foldl Nat.max (counts.headD 0)
    if bmin == bmax then
      { st with longcode := mash st.longcode (bmin + cell1) }
    else
      let values := (List.range (bmax + 1 - bmin)).map (bmin + ·)
      let st := windowScan level cell1 cell2 counts values cell1 (-1) st
      nontrivialFix cell1
        { st with
          lab := writeSegment st.lab cell1 (segmentOf st.lab cell1 counts values) }

/-- One splitting pass of `refine` for a nontrivial splitter cell
`lab[split1..split2]`.

nauty's `bucket` scratch is reproduced semantically: the multiplicity
window over `[bmin, bmax]` and the stable counting redistribution give
exactly the array contents nauty's incremental window zeroing and
placement loop produce. -/
@[expose] def refineNontrivial (ctx : Ctx) (level split1 split2 : Nat) (st : RefineSt) :
    RefineSt :=
  let workset := worksetOf st.lab split1 split2
  let st := { st with longcode := mash st.longcode (split2 - split1 + 1) }
  go workset (cells st.ptn level ctx.n) st
where
  go (workset : Nat) : List (Nat × Nat) → RefineSt → RefineSt
    | [], st => st
    | (cell1, cell2) :: rest, st =>
      go workset rest (nontrivialCell ctx level workset cell1 cell2 st)

/-- One iteration of `refine`'s active-cell loop: remove the chosen
splitter from the active set and perform its splitting pass. -/
@[expose] def refineStep (ctx : Ctx) (level split1 : Nat) (st : RefineSt) : RefineSt :=
  let st := { st with active := erase st.active split1 }
  let split2 := cellEnd st.ptn level split1
  let st := { st with longcode := mash st.longcode (split1 + split2) }
  if split1 == split2 then
    refineTrivial ctx level split1 st
  else
    refineNontrivial ctx level split1 split2 st

@[expose] def refineLoop (ctx : Ctx) (level : Nat) : Nat → RefineSt → RefineSt
  | 0, st => st
  | fuel + 1, st =>
    if st.numcells < ctx.n then
      match pickSplit st.active st.hint with
      | some split1 => refineLoop ctx level fuel (refineStep ctx level split1 st)
      | none => st
    else
      st

/-- nauty's `refine`: make the partition at `level` equitable with respect
to the active cells, producing the refinement code. With the pinned
options (`invarproc = NULL`) this is also the whole of `doref`. -/
@[expose] def refine (ctx : Ctx) (level : Nat) (lab ptn : Array Nat) (active : Nat)
    (numcells : Nat) : RefineSt :=
  let st : RefineSt :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  let st := refineLoop ctx level (4 * ctx.n + 8) st
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
@[expose] def bestcellRow (ctx : Ctx) (lab startArr : Array Nat)
    (workset v2 : Nat) : List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    -- `workset & ~gp ≠ 0` in nauty; `workset` holds only vertices, so
    -- this equals `workset ≠ workset & gp`.
    if workset &&& ctx.g[lab[startArr[v1]!]!]! != 0 ∧
        workset != workset &&& ctx.g[lab[startArr[v1]!]!]! then
      bestcellRow ctx lab startArr workset v2 rest
        ((bucket.set! v1 (bucket[v1]! + 1)).set! v2 (bucket[v2]! + 1))
    else
      bestcellRow ctx lab startArr workset v2 rest bucket

@[expose] def bestcellRows (ctx : Ctx) (lab ptn : Array Nat) (level : Nat)
    (startArr : Array Nat) : List Nat → Array Nat → Array Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    bestcellRows ctx lab ptn level startArr rest
      (bestcellRow ctx lab startArr
        (worksetOf lab startArr[v2]! (cellEnd ptn level startArr[v2]!))
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
@[expose] def bestcell (ctx : Ctx) (lab ptn : Array Nat) (level : Nat) : Nat :=
  let starts := ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2).map (·.1)
  let nnt := starts.length
  if nnt == 0 then
    ctx.n
  else
    let startArr := starts.toArray
    let bucket := bestcellRows ctx lab ptn level startArr
      (List.range' 1 (nnt - 1)) (Array.replicate nnt 0)
    startArr[argmaxLoop bucket (List.range' 1 (nnt - 1)) 0 bucket[0]!]!

/-- nauty's `targetcell` for the pinned undirected configuration. -/
@[expose] def targetcell (ctx : Ctx) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) : Nat :=
  if hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      (hint == 0 ∨ ptn[hint.toNat - 1]! ≤ level) then
    hint.toNat
  else if level ≤ tcLevel then
    bestcell ctx lab ptn level
  else
    let i := (cells ptn level ctx.n).find? (fun (c1, c2) => c1 ≠ c2)
    match i with
    | some (c1, _) => c1
    | none => 0

/-- nauty's `maketargetcell`: the chosen cell's position, contents, and
size. -/
@[expose] def maketargetcell (ctx : Ctx) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) : Nat × Nat × Nat :=
  let i := targetcell ctx lab ptn level tcLevel hint
  let j := cellEnd ptn level (i + 1)
  (i, worksetOf lab i j, j - i + 1)

/-- nauty's `breakout`: split `{tv}` off the front of the cell starting at
`tc`, shifting the displaced vertices one place right, and make `tc` the
only active position. -/
@[expose] def breakout (lab ptn : Array Nat) (level tc tv : Nat) :
    Array Nat × Array Nat × Nat :=
  let lab := go (lab.size + 1) lab tc tv
  (lab, ptn.set! tc level, insert 0 tc)
where
  go : Nat → Array Nat → Nat → Nat → Array Nat
    | 0, lab, _, _ => lab
    | fuel + 1, lab, i, prev =>
      let next := lab[i]!
      let lab := lab.set! i prev
      if next == tv then lab else go fuel lab (i + 1) next

/-- nauty's `isautom` for undirected graphs: `perm` maps edges to edges,
checking each edge from its lesser endpoint. -/
@[expose] def isautom (ctx : Ctx) (perm : Array Nat) : Bool := Id.run do
  for i in [0 : ctx.n] do
    let row := ctx.g[i]!
    for pos in toList row ctx.n do
      if pos > i then
        if ¬ elem ctx.g[perm[i]!]! perm[pos]! then
          return false
  return true

/-- The inverse of a vertex list: `inv[lab[i]] = i`. -/
@[expose] def invPerm (lab : Array Nat) : Array Nat := Id.run do
  let mut inv : Array Nat := .replicate lab.size 0
  for i in [0 : lab.size] do
    inv := inv.set! lab[i]! i
  return inv

/-- nauty's `testcanlab`: compare `g^lab` with `canong` row by row in
nauty's setword order. Returns the comparison and the number of leading
equal rows. -/
@[expose] def testcanlab (ctx : Ctx) (canong : Array Nat) (lab : Array Nat) :
    Int × Nat := Id.run do
  let w := invPerm lab
  for i in [0 : ctx.n] do
    let row := permset ctx.g[lab[i]!]! w ctx.n
    match rowCmp row canong[i]! with
    | .lt => return (-1, i)
    | .gt => return (1, i)
    | .eq => pure ()
  return (0, ctx.n)

/-- nauty's `updatecan`: overwrite rows `samerows..n-1` of `canong` with
the corresponding rows of `g^lab`. -/
@[expose] def updatecan (ctx : Ctx) (canong : Array Nat) (lab : Array Nat)
    (samerows : Nat) : Array Nat := Id.run do
  let w := invPerm lab
  let mut canong := canong
  for i in [samerows : ctx.n] do
    canong := canong.set! i (permset ctx.g[lab[i]!]! w ctx.n)
  return canong

/-- nauty's `fmperm`: the fixed points of a permutation and the least
point of each cycle. -/
@[expose] def fmperm (perm : Array Nat) (n : Nat) : Nat × Nat := Id.run do
  let mut fix := 0
  let mut mcr := 0
  let mut seen : Array Bool := .replicate n false
  for i in [0 : n] do
    if perm[i]! == i then
      fix := insert fix i
      mcr := insert mcr i
    else if ¬ seen[i]! then
      let mut l := i
      for _ in [0 : n] do
        seen := seen.set! l true
        l := perm[l]!
        if l == i then
          break
      mcr := insert mcr i
  return (fix, mcr)

/-- nauty's `fmptn`: the vertices in singleton cells of the partition at
`level`, and the least vertex of each cell. -/
@[expose] def fmptn (lab ptn : Array Nat) (level n : Nat) : Nat × Nat := Id.run do
  let mut fix := 0
  let mut mcr := 0
  for (c1, c2) in cells ptn level n do
    if c1 == c2 then
      fix := insert fix lab[c1]!
      mcr := insert mcr lab[c1]!
    else
      let mut lmin := lab[c1]!
      for i in [c1 + 1 : c2 + 1] do
        if lab[i]! < lmin then
          lmin := lab[i]!
      mcr := insert mcr lmin
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
