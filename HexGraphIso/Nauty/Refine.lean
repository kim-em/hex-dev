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
def cellEnd (ptn : Array Nat) (level i : Nat) : Nat :=
  go (ptn.size - i) i
where
  go : Nat → Nat → Nat
    | 0, j => j
    | fuel + 1, j => if ptn[j]! > level then go fuel (j + 1) else j

/-- The cells of the partition at `level`, as `(start, end)` position
pairs in order. -/
def cells (ptn : Array Nat) (level n : Nat) : List (Nat × Nat) :=
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
def pickSplit (active hint : Nat) : Option Nat :=
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
def splitCellLoop (gRow : Nat) : Nat → Array Nat → Int → Int → (Array Nat × Int × Int)
  | 0, lab, c1, c2 => (lab, c1, c2)
  | fuel + 1, lab, c1, c2 =>
    if c1 ≤ c2 then
      let labc1 := lab[c1.toNat]!
      if elem gRow labc1 then
        splitCellLoop gRow fuel lab (c1 + 1) c2
      else
        let lab := (lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat labc1
        splitCellLoop gRow fuel lab c1 (c2 - 1)
    else
      (lab, c1, c2)

/-- One splitting pass of `refine` for the trivial splitter cell
`{lab[split1]}`. -/
def refineTrivial (ctx : Ctx) (level split1 : Nat) (st : RefineSt) : RefineSt := Id.run do
  let gRow := ctx.g[st.lab[split1]!]!
  let mut st := st
  for (cell1, cell2) in cells st.ptn level ctx.n do
    if cell1 == cell2 then
      continue
    let (lab, c1, c2) :=
      splitCellLoop gRow (cell2 - cell1 + 2) st.lab (Int.ofNat cell1) (Int.ofNat cell2)
    st := { st with lab }
    if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
      let c1 := c1.toNat
      let c2 := c2.toNat
      st := { st with
        ptn := st.ptn.set! c2 level
        longcode := mash st.longcode c2
        numcells := st.numcells + 1 }
      if elem st.active cell1 ∨ c2 - cell1 ≥ cell2 - c1 then
        st := { st with active := insert st.active c1 }
        if c1 == cell2 then
          st := { st with hint := c1 }
      else
        st := { st with active := insert st.active cell1 }
        if c2 == cell1 then
          st := { st with hint := cell1 }
  return st

/-- One splitting pass of `refine` for a nontrivial splitter cell
`lab[split1..split2]`.

nauty's `bucket` scratch is reproduced semantically: the multiplicity
window over `[bmin, bmax]` and the stable counting redistribution below
give exactly the array contents nauty's incremental window zeroing and
placement loop produce. -/
def refineNontrivial (ctx : Ctx) (level split1 split2 : Nat) (st : RefineSt) :
    RefineSt := Id.run do
  let mut st := st
  let mut workset := 0
  for i in [split1 : split2 + 1] do
    workset := insert workset st.lab[i]!
  st := { st with longcode := mash st.longcode (split2 - split1 + 1) }
  for (cell1, cell2) in cells st.ptn level ctx.n do
    if cell1 == cell2 then
      continue
    -- neighbour counts into the splitter, per cell position
    let mut counts : Array Nat := #[]
    for i in [cell1 : cell2 + 1] do
      counts := counts.push (popCount (workset &&& ctx.g[st.lab[i]!]!))
    let bmin := counts.foldl Nat.min counts[0]!
    let bmax := counts.foldl Nat.max counts[0]!
    if bmin == bmax then
      st := { st with longcode := mash st.longcode (bmin + cell1) }
      continue
    -- multiplicity of each count value in the window
    let mult := fun v => counts.foldl (fun a c => if c == v then a + 1 else a) 0
    let mut c1 := cell1
    let mut maxcell : Int := -1
    for i in [bmin : bmax + 1] do
      if mult i > 0 then
        let c2 := c1 + mult i
        st := { st with longcode := mash st.longcode (i + c1) }
        if Int.ofNat (c2 - c1) > maxcell then
          maxcell := Int.ofNat (c2 - c1)
          st := { st with maxpos := c1 }
        if c1 != cell1 then
          st := { st with active := insert st.active c1, numcells := st.numcells + 1 }
          if c2 - c1 == 1 then
            st := { st with hint := c1 }
        if c2 ≤ cell2 then
          st := { st with ptn := st.ptn.set! (c2 - 1) level }
        c1 := c2
    -- stable counting sort of the cell segment by count value
    let mut segment : Array Nat := #[]
    for v in [bmin : bmax + 1] do
      for j in [0 : counts.size] do
        if counts[j]! == v then
          segment := segment.push st.lab[cell1 + j]!
    for j in [0 : segment.size] do
      st := { st with lab := st.lab.set! (cell1 + j) segment[j]! }
    if ¬ elem st.active cell1 then
      st := { st with
        active := erase (insert st.active cell1) st.maxpos }
  return st

/-- One iteration of `refine`'s active-cell loop: remove the chosen
splitter from the active set and perform its splitting pass. -/
def refineStep (ctx : Ctx) (level split1 : Nat) (st : RefineSt) : RefineSt :=
  let st := { st with active := erase st.active split1 }
  let split2 := cellEnd st.ptn level split1
  let st := { st with longcode := mash st.longcode (split1 + split2) }
  if split1 == split2 then
    refineTrivial ctx level split1 st
  else
    refineNontrivial ctx level split1 split2 st

def refineLoop (ctx : Ctx) (level : Nat) : Nat → RefineSt → RefineSt
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
def refine (ctx : Ctx) (level : Nat) (lab ptn : Array Nat) (active : Nat)
    (numcells : Nat) : RefineSt :=
  let st : RefineSt :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  let st := refineLoop ctx level (4 * ctx.n + 8) st
  { st with longcode := cleanup (mash st.longcode st.numcells) }

/-- nauty's `cheapautom`: a cheap sufficient condition for the partition
to have automorphisms rearranging only its nontrivial cells. -/
def cheapautom (ptn : Array Nat) (level n : Nat) : Bool :=
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

/-- nauty's `bestcell`: the first cell nontrivially joined to the greatest
number of other nonsingleton cells, as a `lab` position; `n` when every
cell is a singleton. -/
def bestcell (ctx : Ctx) (lab ptn : Array Nat) (level : Nat) : Nat := Id.run do
  let starts := ((cells ptn level ctx.n).filter fun (c1, c2) => c1 ≠ c2).map (·.1)
  let nnt := starts.length
  if nnt == 0 then
    return ctx.n
  let startArr := starts.toArray
  let mut bucket : Array Nat := .replicate nnt 0
  for v2 in [1 : nnt] do
    let mut workset := 0
    let c1 := startArr[v2]!
    let c2 := cellEnd ptn level c1
    for i in [c1 : c2 + 1] do
      workset := insert workset lab[i]!
    for v1 in [0 : v2] do
      let gp := ctx.g[lab[startArr[v1]!]!]!
      -- `workset & ~gp ≠ 0` in nauty; `workset` holds only vertices, so
      -- this equals `workset ≠ workset & gp`.
      if workset &&& gp != 0 ∧ workset != workset &&& gp then
        bucket := bucket.set! v1 (bucket[v1]! + 1)
        bucket := bucket.set! v2 (bucket[v2]! + 1)
  let mut v1 := 0
  let mut v2 := bucket[0]!
  for i in [1 : nnt] do
    if bucket[i]! > v2 then
      v1 := i
      v2 := bucket[i]!
  return startArr[v1]!

/-- nauty's `targetcell` for the pinned undirected configuration. -/
def targetcell (ctx : Ctx) (lab ptn : Array Nat) (level tcLevel : Nat)
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
def maketargetcell (ctx : Ctx) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) : Nat × Nat × Nat := Id.run do
  let i := targetcell ctx lab ptn level tcLevel hint
  let j := cellEnd ptn level (i + 1)
  let mut tcell := 0
  for p in [i : j + 1] do
    tcell := insert tcell lab[p]!
  return (i, tcell, j - i + 1)

/-- nauty's `breakout`: split `{tv}` off the front of the cell starting at
`tc`, shifting the displaced vertices one place right, and make `tc` the
only active position. -/
def breakout (lab ptn : Array Nat) (level tc tv : Nat) :
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
def isautom (ctx : Ctx) (perm : Array Nat) : Bool := Id.run do
  for i in [0 : ctx.n] do
    let row := ctx.g[i]!
    for pos in toList row ctx.n do
      if pos > i then
        if ¬ elem ctx.g[perm[i]!]! perm[pos]! then
          return false
  return true

/-- The inverse of a vertex list: `inv[lab[i]] = i`. -/
def invPerm (lab : Array Nat) : Array Nat := Id.run do
  let mut inv : Array Nat := .replicate lab.size 0
  for i in [0 : lab.size] do
    inv := inv.set! lab[i]! i
  return inv

/-- nauty's `testcanlab`: compare `g^lab` with `canong` row by row in
nauty's setword order. Returns the comparison and the number of leading
equal rows. -/
def testcanlab (ctx : Ctx) (canong : Array Nat) (lab : Array Nat) :
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
def updatecan (ctx : Ctx) (canong : Array Nat) (lab : Array Nat)
    (samerows : Nat) : Array Nat := Id.run do
  let w := invPerm lab
  let mut canong := canong
  for i in [samerows : ctx.n] do
    canong := canong.set! i (permset ctx.g[lab[i]!]! w ctx.n)
  return canong

/-- nauty's `fmperm`: the fixed points of a permutation and the least
point of each cycle. -/
def fmperm (perm : Array Nat) (n : Nat) : Nat × Nat := Id.run do
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
def fmptn (lab ptn : Array Nat) (level n : Nat) : Nat × Nat := Id.run do
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
def orbjoin (orbits : Array Nat) (map : Array Nat) (n : Nat) :
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
