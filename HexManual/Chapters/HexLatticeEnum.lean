/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexLatticeEnumMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexLatticeEnum: exact lattice search" =>
%%%
tag := "hex-lattice-enum"
%%%

# Integer least squares

For the row basis `(2,0), (1,2)` and target `(1,1)`, minimize
`‖z₀(2,0)+z₁(1,2)−(1,1)‖²` over integer coefficients. Babai nearest-plane
rounding supplies a finite initial bound, but its squared distance is two.
Exact closest-vector search finds `(1,2)`, at squared distance one.

```lean
open Hex Hex.LatticeEnum
namespace LatticeLeastSquares
def rows : Matrix Int 2 2 :=
  Matrix.ofRows #v[#v[2, 0], #v[1, 2]]
def target : Vector Rat 2 := #v[1, 1]
#guard (ofMatrix? rows).map
  (fun b => (babai b target).distanceSq) = some 2
#guard (ofMatrix? rows).map
  (fun b => (closest b target).distanceSq) = some 1
#guard (ofMatrix? rows).map
  (fun b => (closest b target).points.map Point.ambient) =
  some [#v[1, 2]]
#guard (ofMatrix? rows).map (fun b =>
  checkClosest rows target (closestCertificate b target)) =
    some true
end LatticeLeastSquares
```

`closest` returns every minimizer, sorted by ambient coordinates. Each record
also contains coefficients in the original input basis and its exact rational
squared distance. The companion's `closest_spec` proves the global minimum
and completeness of this list, without a prepared-data witness supplied by
the caller.

# The hexagonal lattice in three dimensions

The rows `(1,−1,0), (0,1,−1)` generate the integer lattice `A₂` in the plane
`x+y+z=0`. Its six shortest nonzero vectors have squared norm two. The closed
ball of that squared radius also contains zero.

```lean
open Hex Hex.LatticeEnum
namespace LatticeA2
def rows : Matrix Int 2 3 :=
  Matrix.ofRows #v[#v[1, -1, 0], #v[0, 1, -1]]
#guard ((ofMatrix? rows).bind shortest).map
  (fun a => a.distanceSq) = some 2
#guard ((ofMatrix? rows).bind shortest).map
  (fun a => a.points.length) = some 6
#guard (ofMatrix? rows).map
  (fun b => (enumerate b 0 2).length) = some 7
end LatticeA2
```

`realLattice` is an integer submodule of Euclidean space. Its real span is
used only as the ambient space for packing. Taking rational or real linear
combinations instead would introduce arbitrarily short nonzero vectors.
For any shortest answer with squared norm `s`, `packing_radius` proves that
open balls centred at lattice points are disjoint within that span exactly
when their radius is at most `sqrt(s)/2`. The theorem `kissing_number`
identifies the number of contacting spheres with the complete shortest-vector
list length. Both signs are included. Rank zero returns `none` from `shortest`.

```lean
open Hex.LatticeEnum HexLatticeEnumMathlib
namespace LatticeGeometry
example (b : Basis n m) (a : Minimum n m)
    (h : shortest b = some a) (r : Real) :
    IsPacking b r ↔
      r ≤ Real.sqrt (a.distanceSq : Real) / 2 :=
  packing_radius b a h r
end LatticeGeometry
```

# Rectangular bases and resource limits

Targets may lie outside the row span. Exact Gram–Schmidt preparation retains
the target's orthogonal residual; its squared norm is included in every bound.
Negative squared radii give empty balls, and zero radii retain exact matches.
`ofMatrix?` rejects dependent rows before a search starts.

`enumerateWith`, `closestWith` and `shortestWith` accept independent limits on
visited nodes, retained answers and allocated certificate nodes. Limits are
shared across the optimization and tie passes. A complete result proves
exhaustion; an incomplete result contains checked points, a checked incumbent
for optimization, and pending suffixes or coefficient streams. An incomplete
incumbent carries no global optimality claim. The unlimited forms have no
resource-related failure branch.

```lean
open Hex Hex.LatticeEnum
namespace LatticeBudget
def stopped : Optimization 2 2 → Bool
  | .incomplete _ _ pending .optimum counts =>
    !pending.isEmpty && counts.nodes == 0
  | _ => false
#guard (ofMatrix? (Matrix.identity (R := Int) 2)).map
  (fun b => stopped
    (closestWith { nodes := some 0 } b #v[1/2, 1/2])) =
      some true
end LatticeBudget
```

# The Mathlib correspondence

The companion proves validity of preparation, exhaustive traversal,
coefficient uniqueness and global minima for the executable definitions.
`closest_real_spec` and `shortest_real_spec` express the same complete lists
in real Euclidean space. `checkEnumeration_sound` applies even to certificates
received from an untrusted producer; the native acceptance theorems prove
that completed native runs always pass replay.

# Preparation, preprocessing and certificates

`prepare` computes exact data once. `retarget` reuses the basis orthogonalization
for another target. `lllPreprocess` uses Hex's existing optional LLL provider
policy and checks both integer row transformations. Calling the resulting
`BasisChange` methods searches the reduced basis while returning original-basis
coefficients. Pending work remains expressed in the working basis.

Certificates contain that working basis, both transforms, rational
Gram–Schmidt identities, an exhaustive coefficient tree, and sorted original
points. Replay independently recomputes each interval, checks every child label
and reconstructs every leaf. An optimum certificate adds an attained candidate
and checks that its complete closed ball contains no eligible improvement.
Soundness applies to arbitrary accepted certificates.

`encodeCertificate` and `decodeCertificate` use the versioned
`hex-lattice-enum-1` text format. `DecodeLimits` bounds bytes, dimensions,
numeric token sizes, tree nodes and points before allocation. Decoding returns
untrusted data: call `checkEnumeration`, `checkClosest` or `checkShortest`
afterward. All of these operations are in the Mathlib-free library.

Literal certificates can also be replayed by Lean's kernel. For example, the
two closest integers to one half are zero and one:

```lean
open Hex Hex.LatticeEnum
namespace LatticeReplay
def certificate : Certificate 1 1 where
  rows := Matrix.ofRows #v[#v[1]]
  forward := Matrix.ofRows #v[#v[1]]
  reverse := Matrix.ofRows #v[#v[1]]
  data := ⟨Matrix.ofRows #v[#v[1]],
    Matrix.ofRows #v[#v[1]], #v[1], #v[1/2], #v[0]⟩
  tree := .node ⟨0, 1⟩ [(0, .leaf), (1, .leaf)]
  points := [⟨#v[0], #v[0], 1/4⟩, ⟨#v[1], #v[1], 1/4⟩]
example : checkClosest (Matrix.ofRows #v[#v[1]]) #v[1/2]
    ⟨⟨#v[0], #v[0], 1/4⟩, certificate⟩ = true := by
  decide +kernel
end LatticeReplay
```
