/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import VersoManual
public import HexLatticeEnum
public import HexLatticeEnumMathlib

import all HexLatticeEnum.Basic
import all HexLatticeEnumMathlib.Cert
import all HexLatticeEnumMathlib.Closest
import all HexLatticeEnumMathlib.Geometry
import all HexLatticeEnumMathlib.Shortest
import all HexLatticeEnumMathlib.Traversal

public meta import HexLatticeEnum.Cert
public meta import HexLatticeEnum.Closest
public meta import HexLatticeEnum.Decode
public meta import HexLatticeEnum.Enumerate
public meta import HexLatticeEnum.Preprocess
public meta import HexLatticeEnum.Shortest

public section

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexLatticeEnum: shortest and closest lattice vectors" =>
%%%
tag := "hex-lattice-enum"
%%%

# Introduction
%%%
tag := "hex-lattice-enum-intro"
%%%

A lattice is the set of integer combinations `z₁ b₁ + ⋯ + zₙ bₙ` of linearly
independent vectors `b₁, …, bₙ`. `HexLatticeEnum` works with lattices whose
basis vectors have integer coordinates, and answers three questions about
them exactly:

* which lattice vectors lie within a given distance of a target point,
* which nonzero lattice vectors are shortest, and
* which lattice vectors are closest to a target point.

It returns every answer, not just one: all the shortest vectors, and all the
closest vectors when several are equally close.

The `E₈` lattice is the densest lattice packing of spheres in eight
dimensions. Its usual coordinates are halves of integers, so the rows below
generate `E₈` scaled by 2. The shortest nonzero vectors of `E₈` are its 240
roots, which in this scaling have squared length 8:

```lean
open Hex Hex.Matrix Hex.LatticeEnum

namespace HexLatticeEnumChapter

def E8 : Basis 8 8 :=
  ⟨#m[ 1, -1, -1, -1, -1, -1, -1, 1;
       2,  2,  0,  0,  0,  0,  0, 0;
      -2,  2,  0,  0,  0,  0,  0, 0;
       0, -2,  2,  0,  0,  0,  0, 0;
       0,  0, -2,  2,  0,  0,  0, 0;
       0,  0,  0, -2,  2,  0,  0, 0;
       0,  0,  0,  0, -2,  2,  0, 0;
       0,  0,  0,  0,  0, -2,  2, 0],
    by decide +kernel⟩
```

```lean (name := latticeE8)
#eval (shortest E8).map fun a =>
  (a.distanceSq, a.points.length)
```
```leanOutput latticeE8
some (8, 240)
```

The 240 vectors are the 112 vectors with two entries `±2` and six entries `0`,
and the 128 vectors with every entry `±1` and an even number of minus signs.
In a packing of equal spheres centred at the points of `E₈`, they are the
centres of the 240 spheres touching the sphere at the origin.

A basis reduced by the LLL algorithm (see the {ref "hex-lll"}[HexLLL]
chapter) contains a short vector: with the classical parameters, at most
`2^((n-1)/2)` times the length of the shortest. LLL runs in polynomial time.
`HexLatticeEnum` finds the shortest vectors exactly, by a search whose cost
grows exponentially with the dimension in the worst case. The two work
together: reducing the basis with LLL first can make the search far smaller,
as {ref "hex-lattice-enum-lll"}[a later section] shows.

`HexLatticeEnum` does not depend on Mathlib. Its companion
`HexLatticeEnumMathlib` proves that every answer is correct and complete, and
restates the answers in terms of Mathlib's Euclidean space; see
{ref "hex-lattice-enum-mathlib"}[The Mathlib correspondence].

# Lattices and points

A basis `b : Basis n m` ({name}`Hex.LatticeEnum.Basis`) is an `n × m`
integer matrix whose rows are linearly independent, together with a proof of
independence. The rows need not be square or reduced, so `n < m` is allowed,
and so is `n = 0`. For a literal matrix the proof can be `by decide +kernel`,
as for `E8` above. {name}`Hex.LatticeEnum.ofMatrix?` checks independence when
the program runs, and returns `none` for dependent rows:

```lean
def dependent : Matrix Int 2 2 := #m[1, 2; 2, 4]
#guard (ofMatrix? dependent).isNone
```

Answers are lists of {name}`Hex.LatticeEnum.Point` records. Each records the
lattice vector, its coefficients in the given basis, and its squared distance
to the target as an exact rational number:

{docstring Hex.LatticeEnum.Point}

Lists of points are sorted lexicographically by the coordinates of the
lattice vector. So the list of lattice vectors in an answer does not depend on
the order in which the search found them, or on which basis of the lattice was
given; only the coefficients do.

# Lattice points in a ball
%%%
tag := "hex-lattice-enum-ball"
%%%

{name}`Hex.LatticeEnum.enumerate` takes a basis, a target `t` with rational
coordinates and a rational `r`, and returns every lattice vector `v` with
`‖v - t‖² ≤ r`. For the lattice `ℤ⁴` and the target `0`, counting the
vectors by their squared length counts the ways of writing an integer as a
sum of four squares. Jacobi's four-square theorem says that `k ≥ 1` has
`8 σ(k)` such representations when `k` is odd and `24 σ(k')` when `k` is even
with odd part `k'`, where `σ` is the sum of divisors:

```lean
def Z4 : Basis 4 4 :=
  ⟨Matrix.identity 4, by decide +kernel⟩
```

```lean (name := latticeJacobi)
#eval
  let ball := enumerate Z4 0 10
  (List.range 11).map fun k =>
    (ball.filter (·.distanceSq == (k : Rat))).length
```
```leanOutput latticeJacobi
[1, 8, 24, 32, 24, 48, 96, 64, 24, 104, 144]
```

## How the search works

The search is the Fincke–Pohst enumeration, with the coefficients visited in
the order proposed by Schnorr and Euchner. Let `b₁*, …, bₙ*` be the
Gram–Schmidt orthogonalization of the basis, with `bᵢ = bᵢ* + Σ_{j<i} μᵢⱼ bⱼ*`,
and write the target as `t = Σ τᵢ bᵢ* + t⊥`, with `t⊥` orthogonal to every
basis vector. Then for every coefficient vector `z`,

`‖Σ zᵢ bᵢ - t‖² = ‖t⊥‖² + Σᵢ ‖bᵢ*‖² (zᵢ - cᵢ)²`, where
`cᵢ = τᵢ - Σ_{j>i} μⱼᵢ zⱼ`.

The centre `cᵢ` depends only on the later coefficients `zᵢ₊₁, …, zₙ`. The
search chooses `zₙ` first, then `zₙ₋₁`, and so on. Once the later
coefficients are fixed, the terms already chosen bound the whole sum from
below, so the possible values of `zᵢ` form an interval of integers around
`cᵢ`. The library computes the Gram–Schmidt data with exact rational
arithmetic (see the {ref "hex-gram-schmidt"}[HexGramSchmidt] chapter), and
computes the endpoints of each interval with an integer square root, so no
floating-point rounding can lose a vector on the boundary of the ball. Within
an interval it tries the integers in order of their distance from `cᵢ`.

The target need not lie in the span of the basis: the term `‖t⊥‖²` accounts
for its distance from that span. The nodes of the search tree at which the last
`k` coefficients have been chosen correspond to the points of the projection of
the lattice orthogonal to `b₁, …, bₙ₋ₖ` that lie in the projected ball. Each
node costs `O(n)` rational operations, and each vector found costs `O(n m)` to
reconstruct. The number of nodes grows exponentially with the dimension in
general, and depends heavily on the basis: when the Gram–Schmidt lengths
`‖bᵢ*‖` decrease steeply, `‖bₙ*‖` is small and the interval for `zₙ`, the
first coefficient chosen, is long.

# Shortest and closest vectors
%%%
tag := "hex-lattice-enum-optimum"
%%%

{name}`Hex.LatticeEnum.shortest` returns every shortest nonzero vector of the
lattice, so both `v` and `-v`, together with their common squared length. It
returns `none` exactly when the basis is empty.
{name}`Hex.LatticeEnum.closest` returns every lattice vector closest to a
target, and their common squared distance. Both return a
{name}`Hex.LatticeEnum.Minimum`.

Finding the closest vectors to a target `t` minimizes `‖Σ zᵢ bᵢ - t‖` over
integer vectors `z`, which is the integer least-squares problem. Both
operations start from a lattice vector they can find quickly: for `shortest`, a
shortest basis vector; for `closest`, the vector found by Babai's nearest-plane
algorithm, which takes `zₙ, zₙ₋₁, …` in turn to be the integer nearest the
centre `cᵢ`. Its squared distance is the radius of the first search. Whenever
the search finds a closer vector it shrinks the radius to that vector's
distance, and when it finishes, the radius is the minimum. A second search, of
the ball with exactly that radius, collects every vector that attains it.

{name}`Hex.LatticeEnum.babai` returns Babai's vector on its own. It can be
far from the closest. For the lattice with basis `(2, 0), (1, 2)` and the
target `(1, 1)`, Babai's algorithm rounds `c₂ = 1/2` down to `0`, and then
`c₁ = 1/2` down to `0`, giving the origin at squared distance 2, while
`(1, 2)` is at squared distance 1:

```lean
def skew : Basis 2 2 :=
  ⟨#m[2, 0; 1, 2], by decide +kernel⟩
@[expose] public def target : Vector Rat 2 := #v[1, 1]
```

```lean (name := latticeBabai)
#eval ((babai skew target).ambient,
  (closest skew target).points.map (·.ambient))
```
```leanOutput latticeBabai
(#v[0, 0], [#v[1, 2]])
```

In the hexagonal lattice there are points equidistant from three lattice
points. The rows `(1, -1, 0)` and `(0, 1, -1)` generate the hexagonal lattice
`A₂` inside the plane `x + y + z = 0` of three-dimensional space. The point
`h = (2/3, -1/3, -1/3)` is the centre of the triangle with vertices `0`,
`(1, -1, 0)` and `(1, 0, -1)`, and all three vertices are closest to it:

```lean
def A2 : Basis 2 3 :=
  ⟨#m[1, -1, 0; 0, 1, -1], by decide +kernel⟩
def hole : Vector Rat 3 := #v[2/3, -1/3, -1/3]
```

```lean (name := latticeHole)
#eval ((closest A2 hole).points.map (·.ambient),
  (closest A2 hole).distanceSq)
```
```leanOutput latticeHole
([#v[0, 0, 0], #v[1, -1, 0], #v[1, 0, -1]], (2 : Rat)/3)
```

Moving the target off the plane, to `h + (1, 1, 1)`, adds
`‖(1, 1, 1)‖² = 3` to every squared distance and gives the same closest
vectors:

```lean
def lifted : Vector Rat 3 := hole + #v[1, 1, 1]
#guard (closest A2 lifted).distanceSq = 2/3 + 3
#guard (closest A2 lifted).points.map (·.ambient)
  = (closest A2 hole).points.map (·.ambient)
```

# Reducing the basis first
%%%
tag := "hex-lattice-enum-lll"
%%%

The size of the search depends on the basis. Here is `E₈` again, with its
basis multiplied by an upper unitriangular integer matrix. This gives another
basis of the same lattice:

```lean
def shear : Matrix Int 8 8 :=
  #m[1, 2, -1,  2,  1, -2,  1,  2;
     0, 1,  2, -1,  1,  2, -1,  1;
     0, 0,  1,  2, -1,  1,  2, -2;
     0, 0,  0,  1,  2, -1,  1,  2;
     0, 0,  0,  0,  1,  2, -2,  1;
     0, 0,  0,  0,  0,  1,  2, -1;
     0, 0,  0,  0,  0,  0,  1,  2;
     0, 0,  0,  0,  0,  0,  0,  1]
def E8sheared : Basis 8 8 :=
  ⟨shear * E8.rows, by decide +kernel⟩
```

{name}`Hex.LatticeEnum.lllPreprocess` reduces a basis with
{name}`Hex.lll`, using the same parameters, and returns a
{name}`Hex.LatticeEnum.BasisChange`: the reduced basis, together with integer
matrices transforming each basis into the other, which it has checked. Its
operations, such as `BasisChange.shortest`, search the reduced basis and
report the answers with coefficients in the original basis. Since answers are
sorted by the lattice vectors, the result is the same as searching the
original basis directly.

To count the nodes visited, use the forms with a budget described in
{ref "hex-lattice-enum-limits"}[Limits on the search], with no limits. On
the sheared basis the search for the shortest vectors visits about thirty
times as many nodes as on the reduced basis:

```lean
def visited : Option (Optimization n m) → Nat
  | some (.complete _ _ counts) => counts.nodes
  | some (.incomplete _ _ _ _ counts) => counts.nodes
  | none => 0

def reduced := lllPreprocess E8sheared
#guard reduced.shortest == shortest E8sheared
```

```lean (name := latticeVisited)
#eval (visited (shortestWith {} E8sheared),
  visited (reduced.shortestWith {}))
```
```leanOutput latticeVisited
(43002, 1462)
```

The gap grows with the size of the shear. With entries up to 7 in the upper
triangle, the search on the sheared basis visits nearly three million nodes,
and the search on the reduced basis still visits 1462. The report
`reports/hex-lattice-enum-performance.md` compares the search for a minimum
with the shortest and closest vector routines of the floating-point library
fplll, in their proved modes, which return a single vector. On the small
sheared bases measured there, after LLL reduction, the first search of
`HexLatticeEnum` takes 0.6 to 0.8 times as long as fplll's search.

# Limits on the search
%%%
tag := "hex-lattice-enum-limits"
%%%

{name}`Hex.LatticeEnum.enumerateWith`, {name}`Hex.LatticeEnum.closestWith`
and {name}`Hex.LatticeEnum.shortestWith` take a
{name}`Hex.LatticeEnum.Budget`, which can limit the number of nodes visited,
the number of vectors kept, and the size of the certificate built
(see {ref "hex-lattice-enum-certificates"}[Certificates]). A limit left as
`none` is not imposed. When the search finishes within the limits the result
is `complete`, with the same guarantees as the forms without a budget. The
companion proves that the counts never exceed the limits.

When a limit stops the search, the result is `incomplete`. It contains the
vectors found so far, each with its distance checked, and a description of
the parts of the search tree not yet visited. For `closestWith` and
`shortestWith` it also contains the best vector found, and says whether the
search stopped while looking for the minimum or while collecting the vectors
that attain it. An incomplete result claims nothing about the vectors it does
not contain: the best vector found need not be closest, and a ball may contain
vectors that were not reached. Here the search for the shortest vectors of
`E₈` stops after 1000 nodes, during the second search. It has found a vector
of squared length 8, and 89 of the 240 shortest vectors. Its result says
neither that 8 is the minimum nor that the list of 89 is complete:

```lean
def stopped : Option (Rat × Nat) :=
  match shortestWith { nodes := some 1000 } E8 with
  | some (.incomplete best found _ .ties _) =>
    some (best.distanceSq, found.length)
  | _ => none
```

```lean (name := latticeStopped)
#eval stopped
```
```leanOutput latticeStopped
some (8, 89)
```

# Certificates
%%%
tag := "hex-lattice-enum-certificates"
%%%

A complete search can be recorded as a certificate, which can be checked
without trusting the program that produced it.
{name}`Hex.LatticeEnum.enumerationCertificate` records the search of a ball
as a {name}`Hex.LatticeEnum.Certificate`: the basis searched, the matrices
relating it to the original basis, the Gram–Schmidt data, the search tree
with the interval of coefficients at each node, and the list of vectors
found. {name}`Hex.LatticeEnum.closestCertificate` records a closest vector
together with a certificate for the ball whose radius is its distance, which
shows that nothing is closer and lists every vector at the same distance.
{name}`Hex.LatticeEnum.shortestCertificate` does the same for a shortest
nonzero vector, with target `0`; the ball then also contains `0`, and every
other vector in it must have the same length as the shortest vector.

The search tree for the three closest vectors of `A₂` to `h` has a node for
the coefficient `z₂`, with children `0` and `1`, and below them nodes for
`z₁`. Each leaf is one of the coefficient vectors `(0, 0)`, `(1, 0)` and
`(1, 1)` of the three vertices:

```lean (name := latticeTree)
#eval (closestCertificate A2 hole).enumeration.tree
```
```leanOutput latticeTree
Hex.LatticeEnum.Tree.node
  { lo := 0, hi := 1 }
  [(0, Hex.LatticeEnum.Tree.node { lo := 0, hi := 1 } [(0, Hex.LatticeEnum.Tree.leaf), (1, Hex.LatticeEnum.Tree.leaf)]),
   (1, Hex.LatticeEnum.Tree.node { lo := 1, hi := 1 } [(1, Hex.LatticeEnum.Tree.leaf)])]
```

{name}`Hex.LatticeEnum.checkEnumeration`,
{name}`Hex.LatticeEnum.checkClosest` and
{name}`Hex.LatticeEnum.checkShortest` take the original basis matrix, the
target (except for `checkShortest`, where it is `0`) and a certificate. They
check the matrices relating the two bases and
the Gram–Schmidt identities with exact arithmetic, recompute the interval at
every node of the tree, check that the children of each node are exactly the
integers in its interval, recompute every vector at a leaf, and compare the
result with the list in the certificate. Nothing stored in the certificate is
used without being checked. {name}`Hex.LatticeEnum.encodeOptimumCertificate`
and {name}`Hex.LatticeEnum.decodeOptimumCertificate` write a certificate as
text and read it back; decoding takes a {name}`Hex.LatticeEnum.DecodeLimits`
bounding the size of the text, the dimensions and the number of nodes, and
the decoded certificate must still be checked:

```lean
def holeCertificate := closestCertificate A2 hole
#guard checkClosest A2.rows hole holeCertificate

def decodedOk : Bool :=
  match decodeOptimumCertificate {} 2 3
      (encodeOptimumCertificate holeCertificate) with
  | .ok c => checkClosest A2.rows hole c
  | .error _ => false
#guard decodedOk

end HexLatticeEnumChapter
```

The companion proves that a certificate the checker accepts is correct,
whoever produced it:

{docstring HexLatticeEnumMathlib.checkEnumeration_sound}

It also proves that the certificates the library produces are always
accepted. A certificate has a node for each node of the search of its ball,
so it is about as large as that search, and checking it costs about as much
as searching again.

# The Mathlib correspondence
%%%
tag := "hex-lattice-enum-mathlib"
%%%

`HexLatticeEnumMathlib` proves that the answers are correct and complete, for
every basis and target. The only hypothesis, for shortest vectors, is that
`shortest b` returned an answer, which happens exactly when the basis is not
empty:

{docstring HexLatticeEnumMathlib.enumerate_spec}

{docstring HexLatticeEnumMathlib.closest_spec}

{docstring HexLatticeEnumMathlib.shortest_spec}

Here `b.rows.memLattice v` says that `v` is an integer combination of the
rows, and `distance v t` is the squared distance from `v` to `t`. The theorem
{name}`HexLatticeEnumMathlib.closest_real_spec` restates `closest_spec` with
the lattice as {name}`HexLatticeEnumMathlib.realLattice`, a
`Submodule ℤ (EuclideanSpace ℝ (Fin m))`, and Mathlib's distance, and
{name}`HexLatticeEnumMathlib.shortest_real_spec` does the same for shortest
vectors. The lattice is the set of integer combinations of the rows; the real
span of the rows, which contains arbitrarily short nonzero vectors, plays no
role except as the space in which the packing below lives.

The companion also derives the packing radius and the kissing number of the
lattice from the list of shortest vectors. Here
{name}`HexLatticeEnumMathlib.IsPacking` says that the open balls of radius `r`
around the lattice points, inside the real span of the lattice, are disjoint,
and {name}`HexLatticeEnumMathlib.contacts` is the set of centres of the balls
touching the ball at the origin:

{docstring HexLatticeEnumMathlib.packing_radius}

{docstring HexLatticeEnumMathlib.kissing_number}

To use these theorems for a particular lattice, a proof needs to know the
value of `shortest b`. `decide +kernel` can compute it while checking the
proof. For the lattice `D₄`, the densest lattice packing in four dimensions,
this takes about a second, and gives its 24 vectors of length `√2` and its
packing radius `√2 / 2`:

```lean
open Hex Hex.Matrix Hex.LatticeEnum HexLatticeEnumMathlib

namespace HexLatticeEnumChapterD4

def D4 : Basis 4 4 :=
  ⟨#m[1, -1,  0,  0;
      0,  1, -1,  0;
      0,  0,  1, -1;
      0,  0,  1,  1], by decide +kernel⟩

theorem shortest_D4 :
    (shortest D4).map (fun a =>
      (a.distanceSq, a.points.length)) =
      some (2, 24) := by
  decide +kernel

theorem kissing_D4 :
    {x : EuclideanSpace ℝ (Fin 4) |
      x ∈ realLattice D4 ∧ x ≠ 0 ∧
        ‖x‖ = Real.sqrt 2}.ncard = 24 := by
  obtain ⟨a, h, ha⟩ :=
    Option.map_eq_some_iff.mp shortest_D4
  simp only [Prod.mk.injEq] at ha
  have := kissing_number D4 a h
  rw [ha.1, ha.2] at this
  simpa [contacts, mul_div_cancel₀] using this

theorem packing_D4 (r : ℝ) :
    IsPacking D4 r ↔ r ≤ Real.sqrt 2 / 2 := by
  obtain ⟨a, h, ha⟩ :=
    Option.map_eq_some_iff.mp shortest_D4
  simp only [Prod.mk.injEq] at ha
  have := packing_radius D4 a h r
  rw [ha.1] at this
  simpa using this

end HexLatticeEnumChapterD4
```

The same proof for `E₈` takes about half a minute. The other operations have
theorems of the same kind:
{name}`HexLatticeEnumMathlib.enumerateWith_spec`,
{name}`HexLatticeEnumMathlib.closestWith_spec` and
{name}`HexLatticeEnumMathlib.shortestWith_spec` describe the results with a
budget, {name}`HexLatticeEnumMathlib.change_enumerate` shows that searching
after `lllPreprocess` gives the same answer, and
{name}`HexLatticeEnumMathlib.enumerationCertificate_check`,
{name}`HexLatticeEnumMathlib.closestCertificate_check` and
{name}`HexLatticeEnumMathlib.shortestCertificate_check` show that the
certificates the library produces are accepted.
