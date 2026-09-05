/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGraphIso

/-!
The `HexGraphIso` conformance corpus and the searches a record is read
off, shared by the fixture emitter (`HexGraphIso.EmitFixtures`), the
campaign emitter (`HexGraphIso.EmitCampaign`) and the twin runner
(`HexGraphIso.EngineTwin`).

A `Case` is a coloured graph as the emitters describe it: a name, the
vertex count, the colour count, the colour vector and the edge list.
`eachFixture` generates the canonical-record part of the committed
fixture corpus, `eachAutos` its automorphism-record part and
`eachCampaign` the extended campaign, all in emission order, so every
driver runs the same cases in the same sequence.

`Runner` is the search a record is read off. `canonAnswer` reads the
label and canonical upper-triangle bits off the public `canonicalize`,
and the node and generator counts off `Nauty.runColored`.
`engineAnswer` reads all of them off `engine`, the second search the
drivers compare against. As it stands `engine` calls
`Nauty.runColoredTraced`, so the twin compares the literal port with
itself and the emitters' `--engine` mode emits the same records as
their default mode.
-/

namespace Hex.GraphIsoCases

open Hex.Conformance.Emit
open Hex.GraphIso
open Hex.GraphIso.Nauty

private def lib : String := "HexGraphIso"

/-- One corpus case: a coloured graph as the emitted record describes
it. Colours are one per vertex, edges are unordered pairs. -/
structure Case where
  /-- The case identifier carried by the emitted record. -/
  name : String
  /-- The number of vertices. -/
  n : Nat
  /-- The number of colours. -/
  k : Nat
  /-- The colour of each vertex. -/
  colors : Array Nat
  /-- The edges, as unordered vertex pairs. -/
  edges : List (Nat × Nat)

/-- The vertex pairs `(i, j)`, `i < j`, in lexicographic order. -/
private def pairList (n : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : n] do
    for j in [i + 1 : n] do
      out := (i, j) :: out
  return out.reverse

private def edgesOfMask (n mask : Nat) : List (Nat × Nat) :=
  ((pairList n).zipIdx.filter fun (_, t) => mask.testBit t).map (·.1)

/-- Build the coloured graph through the public checked constructors. -/
def coloredOf? (n k : Nat) (colors : Array Nat)
    (edges : List (Nat × Nat)) : Option (Colored n k) := do
  let g ← Graph.ofEdges? n edges
  if h : colors.size = n ∧ ∀ v ∈ colors, v < k then
    let c ← Coloring.ofVector?
      ⟨colors.attach.map fun v => (⟨v.val, h.2 v.val v.property⟩ : Fin k),
        by simp [h.1]⟩
    some { graph := g, coloring := c }
  else
    none

/-- The upper-triangle adjacency bits of a coloured graph in row-major
order. -/
private def triBits {n k : Nat} (G : Colored n k) : String :=
  String.ofList <| (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i.val < j.val)).map fun j =>
      if G.graph.adj i j then '1' else '0'

/-- The upper-triangle adjacency bits of dense rows in row-major order,
for reading the canonical form off a search's `canong`. -/
private def triRows {n : Nat} (rows : Array (VSet n)) : String :=
  String.ofList <| (List.range n).flatMap fun i =>
    ((List.range n).filter fun j => decide (i < j)).map fun j =>
      if rows[i]!.mem j then '1' else '0'

/-! # Searches -/

/-- The search the twin runner and the `--engine` emitter modes measure
against the literal port. It calls `Nauty.runColoredTraced`, so as it
stands both sides run the same search. Point this definition at another
search to compare that one instead. -/
def engine {n k : Nat} (G : Colored n k) : TraceRun n :=
  runColoredTraced G

/-- What a search contributes to a fixture record: the canonical label,
the canonical upper-triangle adjacency bits, the visited-node count and
the number of accepted generators. -/
structure Answer where
  /-- The canonical label, as the image of each vertex. -/
  label : List Nat
  /-- The canonical upper-triangle adjacency bits. -/
  tri : String
  /-- The number of search-tree nodes visited. -/
  numnodes : Nat
  /-- The number of accepted automorphism generators. -/
  numgens : Nat

/-- A search a fixture record is read off; `none` when the search
returns a label the checked constructor rejects. -/
abbrev Runner := (n k : Nat) → Colored n k → Option Answer

/-- The public pipeline: the label and canonical form come from
`canonicalize`, the node and generator counts from the transcribed
search. -/
def canonAnswer : Runner := fun n _k G =>
  let res := canonicalize G
  let r := runColored G
  some
    { label := (List.finRange n).map fun i => (res.label.get i).val
      tri := triBits res.form
      numnodes := r.numnodes
      numgens := r.numgenerators }

/-- The second search: the label, canonical form and both counts come
from `engine`, so an external oracle pins that search independently of
the public pipeline. -/
def engineAnswer : Runner := fun n _k G =>
  let r := (engine G).result
  (Label.ofArray? n r.canonlab).map fun l =>
    { label := (List.finRange n).map fun i => (l.get i).val
      tri := triRows r.canong
      numnodes := r.numnodes
      numgens := r.numgenerators }

/-- The number of vertices of each colour, in colour order. -/
private def cellSizes (case : Case) : Array Nat := Id.run do
  let mut sizes : Array Nat := .replicate case.k 0
  for v in [0 : case.n] do
    let c := case.colors[v]!
    sizes := sizes.set! c (sizes[c]! + 1)
  return sizes

private def edgeList (case : Case) : List (Int × Int) :=
  case.edges.map fun (a, b) => (Int.ofNat (Nat.min a b), Int.ofNat (Nat.max a b))

/-- Emit one fixture record for `case`, reading the canonical label,
the canonical upper-triangle bits and the node count off `runner`. -/
def emit (runner : Runner) (case : Case) : IO Unit := do
  let some G := coloredOf? case.n case.k case.colors case.edges
    | throw (IO.userError s!"emit: case {case.name} rejected by the builders")
  let some a := runner case.n case.k G
    | throw (IO.userError s!"emit: case {case.name} has no checked label")
  emitGraphIsoFixture lib case.name case.n case.k
    (case.colors.toList.map Int.ofNat)
    (edgeList case)
    (a.label.map Int.ofNat)
    a.tri
    ((cellSizes case).toList.map Int.ofNat)
    a.numnodes

/-- Emit one automorphism-group record: the canonical answer a
`graphiso` record carries, so the stream stays readable end to end by a
consumer that only knows canonical forms, together with the generator
list, orbits, orbit count, generator count and group order the public
`autos` surface reports. -/
def emitAutos (runner : Runner) (case : Case) : IO Unit := do
  let some G := coloredOf? case.n case.k case.colors case.edges
    | throw (IO.userError s!"emit: case {case.name} rejected by the builders")
  let some a := runner case.n case.k G
    | throw (IO.userError s!"emit: case {case.name} has no checked label")
  let aut := autos G
  emitGraphIsoAutosFixture lib case.name case.n case.k
    (case.colors.toList.map Int.ofNat)
    (edgeList case)
    (a.label.map Int.ofNat)
    a.tri
    ((cellSizes case).toList.map Int.ofNat)
    a.numnodes
    (aut.gens.map fun p =>
      (List.finRange case.n).map fun i => Int.ofNat (p.get i).val)
    a.numgens
    (aut.orbits.toList.map Int.ofNat)
    aut.numOrbits
    aut.order

/-- All base-`k` colour vectors of length `n`, vertex `0` most
significant, in ascending numeral order. -/
private def colorVectors (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | m + 1 => (List.range k).flatMap fun d => (colorVectors k m).map (d :: ·)

private def isOnto (k : Nat) (v : List Nat) : Bool :=
  (List.range k).all fun c => v.contains c

/-! # Named examples -/

private def petersen : List (Nat × Nat) :=
  (List.range 5).map (fun i => (i, (i + 1) % 5))
    ++ (List.range 5).map (fun i => (5 + i, 5 + ((i + 2) % 5)))
    ++ (List.range 5).map (fun i => (i, 5 + i))

/-- The Kneser presentation `K(5, 2)`: the two-element subsets of `Fin 5`
in lexicographic order, joined when disjoint. -/
private def kneser52 : List (Nat × Nat) := Id.run do
  let subsets := pairList 5
  let mut out := []
  for (s, i) in subsets.zipIdx do
    for (t, j) in subsets.zipIdx do
      if i < j then
        if s.1 ≠ t.1 ∧ s.1 ≠ t.2 ∧ s.2 ≠ t.1 ∧ s.2 ≠ t.2 then
          out := (i, j) :: out
  return out.reverse

private def prism5 : List (Nat × Nat) :=
  (List.range 5).map (fun i => (i, (i + 1) % 5))
    ++ (List.range 5).map (fun i => (5 + i, 5 + ((i + 1) % 5)))
    ++ (List.range 5).map (fun i => (i, 5 + i))

private def hypercube (d : Nat) : List (Nat × Nat) := Id.run do
  let n := 2 ^ d
  let mut out := []
  for x in [0 : n] do
    for b in [0 : d] do
      let y := x ^^^ (1 <<< b)
      if x < y then
        out := (x, y) :: out
  return out.reverse

private def completeBipartite (a b : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : a] do
    for j in [0 : b] do
      out := (i, a + j) :: out
  return out.reverse

private def triangles (t : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : t] do
    out := (3*i, 3*i+1) :: (3*i+1, 3*i+2) :: (3*i, 3*i+2) :: out
  return out.reverse

private def paley13 : List (Nat × Nat) := Id.run do
  let q := 13
  let qr := (List.range q).filterMap fun x =>
    if x > 0 then some ((x * x) % q) else none
  let mut out := []
  for i in [0 : q] do
    for j in [i + 1 : q] do
      if qr.contains ((j - i) % q) ∨ qr.contains ((q + i - j) % q) then
        out := (i, j) :: out
  return out.reverse

private def complete (n : Nat) : List (Nat × Nat) := pairList n

/-- The Latin-square graph `L₃(m)` of the cyclic square
`(r, c) ↦ (r + c) mod m`: the `m²` cells numbered `r * m + c`, adjacent
when they share a row, a column or a symbol. -/
private def latinSquareEdges (m : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for a in [0 : m * m] do
    for b in [a + 1 : m * m] do
      if a / m == b / m || a % m == b % m ||
          (a / m + a % m) % m == (b / m + b % m) % m then
        out := (a, b) :: out
  return out.reverse

/-- The incidence graph of the cyclic Latin square of order `q`, in the
four-colour encoding of the nauty introduction: one vertex per row
(`0 .. q-1`), column (`q .. 2q-1`), symbol (`2q .. 3q-1`) and position
(`3q + i * q + j`), with each position joined to its row, its column
and the symbol written there. Its colour-preserving automorphism group
is the isotopy group of the square. -/
private def latinIncidenceEdges (q : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : q] do
    for j in [0 : q] do
      let p := 3 * q + i * q + j
      out := (2 * q + ((i + j) % q), p) :: (q + j, p) :: (i, p) :: out
  return out.reverse.map fun (a, b) => (Nat.min a b, Nat.max a b)

/-- The four-colour vector of `latinIncidenceEdges`. -/
private def latinIncidenceColors (q : Nat) : Array Nat := Id.run do
  let mut c : Array Nat := #[]
  for _ in [0 : q] do c := c.push 0
  for _ in [0 : q] do c := c.push 1
  for _ in [0 : q] do c := c.push 2
  for _ in [0 : q * q] do c := c.push 3
  return c

/-- Apply a vertex permutation to an edge list, renormalizing to `i < j`
pairs in lexicographic order. -/
private def relabelEdges (perm : Array Nat) (edges : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (edges.map fun (a, b) =>
    let a := perm[a]!
    let b := perm[b]!
    (Nat.min a b, Nat.max a b)).mergeSort fun x y =>
      x.1 < y.1 ∨ (x.1 == y.1 ∧ x.2 ≤ y.2)

/-! # The corpora -/

/-- The SplitMix64 corpus values the fixture cases are built from: the
seed-1 relabelling of the Petersen graph, two `G(12, 1/2)` masks and
the onto colourings drawn after them. -/
private structure Corpus where
  perm10 : Array Nat
  mask12a : Nat
  col12 : Array Nat
  mask12b : Nat
  col10 : Array Nat

private def corpus : Corpus :=
  let g0 : Random.Gen := ⟨Random.seed1⟩
  let (perm10, g1) := Random.shuffle g0 (.ofFn (n := 10) (·.val))
  let (mask12a, g2) := Random.gnpMask g1 12
  let (col12, _) := Random.ontoColoring g2 12 3
  let h0 : Random.Gen := ⟨Random.seed2⟩
  let (mask12b, h1) := Random.gnpMask h0 12
  let (col10, _) := Random.ontoColoring h1 10 2
  { perm10, mask12a, col12, mask12b, col10 }

/-- Run `act` on every committed fixture case, in emission order: all
1,100 labelled uncoloured graphs for `0 ≤ n ≤ 5`, all 4,912 graph and
ordered-surjective-partition pairs for `0 ≤ n ≤ 4`, the named larger
examples with their deterministic relabellings and colourings, and the
SplitMix64 corpus cases. -/
def eachFixture (act : Case → IO Unit) : IO Unit := do
  -- all labelled uncoloured graphs, 0 ≤ n ≤ 5
  for n in [0 : 6] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      let k := if n == 0 then 0 else 1
      act ⟨s!"u/n{n}/m{mask}", n, k, .replicate n 0, edgesOfMask n mask⟩
  -- all graph and ordered-surjective-partition pairs, 0 ≤ n ≤ 4
  for n in [0 : 5] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      let edges := edgesOfMask n mask
      if n == 0 then
        act ⟨s!"c/n0/m0/k0/", 0, 0, #[], []⟩
      else
        for k in [1 : n + 1] do
          for v in colorVectors k n do
            if isOnto k v then
              let digits := String.join (v.map toString)
              act ⟨s!"c/n{n}/m{mask}/k{k}/{digits}", n, k, v.toArray, edges⟩
  -- named examples: positive and negative pairs, and automorphism-group
  -- extremes (trivial for the random graphs, small for paley13, large for
  -- empty/complete/triangles)
  act ⟨"named/petersen", 10, 1, .replicate 10 0, petersen⟩
  act ⟨"named/kneser52", 10, 1, .replicate 10 0, kneser52⟩
  act ⟨"named/prism5", 10, 1, .replicate 10 0, prism5⟩
  act ⟨"named/q3", 8, 1, .replicate 8 0, hypercube 3⟩
  act ⟨"named/q4", 16, 1, .replicate 16 0, hypercube 4⟩
  act ⟨"named/k33", 6, 1, .replicate 6 0, completeBipartite 3 3⟩
  act ⟨"named/triangles4", 12, 1, .replicate 12 0, triangles 4⟩
  act ⟨"named/paley13", 13, 1, .replicate 13 0, paley13⟩
  act ⟨"named/empty8", 8, 1, .replicate 8 0, []⟩
  act ⟨"named/complete8", 8, 1, .replicate 8 0, complete 8⟩
  -- parity two-colouring of the 4-cube: deterministic, onto, symmetric
  act ⟨"named/q4-parity2", 16, 2,
    .ofFn (n := 16) fun i => (Nauty.popCount i.val) % 2, hypercube 4⟩
  -- SplitMix64 corpus cases
  let c := corpus
  act ⟨"rand/petersen-relabel-seed1", 10, 1, .replicate 10 0,
    relabelEdges c.perm10 petersen⟩
  act ⟨"rand/g12-seed1", 12, 1, .replicate 12 0, edgesOfMask 12 c.mask12a⟩
  act ⟨"rand/g12-col3-seed1", 12, 3, c.col12, edgesOfMask 12 c.mask12a⟩
  act ⟨"rand/g12-seed2", 12, 1, .replicate 12 0, edgesOfMask 12 c.mask12b⟩
  act ⟨"rand/petersen-col2-seed2", 10, 2, c.col10, petersen⟩

/-- Run `act` on every case of the automorphism-record corpus, in
emission order: every labelled uncoloured graph on at most four
vertices, every graph and ordered-surjective-partition pair on at most
three, and the named and pseudo-random examples. -/
def eachAutos (act : Case → IO Unit) : IO Unit := do
  for n in [1 : 5] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      act ⟨s!"a/u/n{n}/m{mask}", n, 1, .replicate n 0, edgesOfMask n mask⟩
  for n in [1 : 4] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      let edges := edgesOfMask n mask
      for k in [1 : n + 1] do
        for v in colorVectors k n do
          if isOnto k v then
            let digits := String.join (v.map toString)
            act ⟨s!"a/c/n{n}/m{mask}/k{k}/{digits}", n, k, v.toArray, edges⟩
  act ⟨"a/named/petersen", 10, 1, .replicate 10 0, petersen⟩
  act ⟨"a/named/kneser52", 10, 1, .replicate 10 0, kneser52⟩
  act ⟨"a/named/prism5", 10, 1, .replicate 10 0, prism5⟩
  act ⟨"a/named/q3", 8, 1, .replicate 8 0, hypercube 3⟩
  act ⟨"a/named/q4", 16, 1, .replicate 16 0, hypercube 4⟩
  act ⟨"a/named/k33", 6, 1, .replicate 6 0, completeBipartite 3 3⟩
  act ⟨"a/named/triangles4", 12, 1, .replicate 12 0, triangles 4⟩
  act ⟨"a/named/paley13", 13, 1, .replicate 13 0, paley13⟩
  act ⟨"a/named/empty8", 8, 1, .replicate 8 0, []⟩
  act ⟨"a/named/complete8", 8, 1, .replicate 8 0, complete 8⟩
  act ⟨"a/named/latin-l3-4", 16, 1, .replicate 16 0, latinSquareEdges 4⟩
  act ⟨"a/named/latin-incidence3", 18, 4,
    latinIncidenceColors 3, latinIncidenceEdges 3⟩
  act ⟨"a/named/latin-incidence4", 28, 4,
    latinIncidenceColors 4, latinIncidenceEdges 4⟩
  act ⟨"a/named/q4-parity2", 16, 2,
    .ofFn (n := 16) fun i => (Nauty.popCount i.val) % 2, hypercube 4⟩
  let c := corpus
  act ⟨"a/rand/petersen-relabel-seed1", 10, 1, .replicate 10 0,
    relabelEdges c.perm10 petersen⟩
  act ⟨"a/rand/g12-seed1", 12, 1, .replicate 12 0, edgesOfMask 12 c.mask12a⟩
  act ⟨"a/rand/g12-col3-seed1", 12, 3, c.col12, edgesOfMask 12 c.mask12a⟩
  act ⟨"a/rand/g12-seed2", 12, 1, .replicate 12 0, edgesOfMask 12 c.mask12b⟩
  act ⟨"a/rand/petersen-col2-seed2", 10, 2, c.col10, petersen⟩

/-- The case of a bare graph, single-coloured, with the edges read off
its adjacency. -/
private def graphCase (name : String) {n : Nat} (G : Hex.Graph n) : Case := Id.run do
  let mut edges : List (Nat × Nat) := []
  for i in [0 : n] do
    for j in [i + 1 : n] do
      if h : i < n ∧ j < n then
        if G.adj ⟨i, h.1⟩ ⟨j, h.2⟩ then
          edges := (i, j) :: edges
  return ⟨name, n, if n == 0 then 0 else 1, .replicate n 0, edges.reverse⟩

/-- Run `act` on every campaign case, in emission order: all 32,768
labelled graphs at `n = 6`, the deterministic hard families including
the large instances of the extended cactus corpus, and the SplitMix64
pseudo-random cases at growing sizes. -/
def eachCampaign (act : Case → IO Unit) : IO Unit := do
  -- every labelled graph on six vertices
  for mask in [0 : 2 ^ 15] do
    act ⟨s!"campaign/n6/m{mask}", 6, 1, .replicate 6 0, edgesOfMask 6 mask⟩
  -- deterministic hard families
  act (graphCase "campaign/paley13" (Families.paley 13))
  act (graphCase "campaign/paley17" (Families.paley 17))
  act (graphCase "campaign/hypercube4" (Families.hypercube 4))
  act (graphCase "campaign/hypercube5" (Families.hypercube 5))
  act (graphCase "campaign/grid6" (Families.grid 6 6))
  act (graphCase "campaign/johnson72" (Families.johnson 7 2))
  act (graphCase "campaign/kneser72" (Families.kneser 7 2))
  act (graphCase "campaign/triangular8" (Families.triangular 8))
  act (graphCase "campaign/multipartite" (Families.completeMultipartite [3, 4, 5]))
  act (graphCase "campaign/copies5c5" (Families.copies 5 (Families.cycle 5)))
  act (graphCase "campaign/circulant17" (Families.circulant 17 [1, 2, 4, 8]))
  -- large hard instances matching the extended cactus corpus: the
  -- campaign is where nauty cross-checks these sizes
  act (graphCase "campaign/paley61" (Families.paley 61))
  act (graphCase "campaign/paley113" (Families.paley 113))
  act (graphCase "campaign/hypercube7" (Families.hypercube 7))
  act (graphCase "campaign/grid12" (Families.grid 12 12))
  act (graphCase "campaign/kneser15-2" (Families.kneser 15 2))
  act (graphCase "campaign/johnson15-2" (Families.johnson 15 2))
  act (graphCase "campaign/circulant255" (Families.circulant 255 [1, 2]))
  act (graphCase "campaign/circulant193" (Families.circulant 193 [1, 2, 4, 8]))
  act (graphCase "campaign/latin5" (Families.latinSquare 5))
  act (graphCase "campaign/latin13" (Families.latinSquare 13))
  -- pseudo-random corpus: G(n, 1/2) for both seeds at growing sizes
  let mut g : Random.Gen := ⟨Random.seed1⟩
  for n in [12, 14, 16] do
    let (mask, g') := Random.gnpMask g n
    g := g'
    act ⟨s!"campaign/g{n}-seed1", n, 1, .replicate n 0, edgesOfMask n mask⟩
    let (cols, g'') := Random.ontoColoring g n 3
    g := g''
    act ⟨s!"campaign/g{n}-col3-seed1", n, 3, cols, edgesOfMask n mask⟩
  let mut h : Random.Gen := ⟨Random.seed2⟩
  for n in [12, 14, 16] do
    let (mask, h') := Random.gnpMask h n
    h := h'
    act ⟨s!"campaign/g{n}-seed2", n, 1, .replicate n 0, edgesOfMask n mask⟩

/-- The search an emitter reads its records off, from its command line:
no argument is the public pipeline, `--engine` the second search. -/
def runnerOfArgs (args : List String) : IO Runner :=
  match args with
  | [] => pure canonAnswer
  | ["--engine"] => pure engineAnswer
  | _ => throw (IO.userError s!"emit: unknown arguments {args}")

end Hex.GraphIsoCases
