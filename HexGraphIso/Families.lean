/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Colored

public section

/-!
Deterministic graph families for the conformance and benchmark corpus,
per SPEC/Libraries/hex-graph-iso.md § Reproducible generators. Each
generator documents its mathematical definition and its stable
vertex-numbering rule; none uses randomness. This module carries the
first slice — paths, cycles, circulants, complete multipartite graphs,
repeated components, grids, hypercubes, Johnson, Kneser, triangular, and
Paley graphs — with the incidence-geometry families (Latin squares,
Hadamard matrices, projective planes) and the CFI, Miyazaki, and
multipede instances to follow in the staged corpus.
-/

namespace Hex.GraphIso.Families

open Hex

/-- The path `0 - 1 - ⋯ - (n-1)`. -/
@[expose] def path (n : Nat) : Graph n :=
  Graph.ofRel fun i j => j.val == i.val + 1

/-- The cycle on `n` vertices in their natural order; for `n ≤ 2` this
degenerates to the path. -/
@[expose] def cycle (n : Nat) : Graph n :=
  Graph.ofRel fun i j => j.val == (i.val + 1) % n

/-- The circulant graph: `i` and `j` are adjacent when their difference
modulo `n` lies in the connection set (in either direction). -/
@[expose] def circulant (n : Nat) (s : List Nat) : Graph n :=
  Graph.ofRel fun i j => s.contains ((n + j.val - i.val) % n)

/-- The complete multipartite graph over the given part sizes: vertices
are numbered part by part in the given order, and two vertices are
adjacent exactly when they lie in different parts. -/
@[expose] def completeMultipartite (parts : List Nat) : Graph parts.sum :=
  Graph.ofRel fun i j => partOf parts i.val != partOf parts j.val
where
  /-- The index of the part containing flat vertex `v`. -/
  partOf : List Nat → Nat → Nat
    | [], _ => 0
    | p :: rest, v => if v < p then 0 else 1 + partOf rest (v - p)

/-- The complete bipartite graph `K_{a,b}`: vertices `0..a-1` on the
left, `a..a+b-1` on the right. -/
@[expose] def completeBipartite (a b : Nat) : Graph (a + b) :=
  Graph.ofRel fun i j => i.val < a && a ≤ j.val

/-- `t` disjoint copies of a graph on `m` vertices: copy `c` occupies
vertices `c*m..(c+1)*m-1` in the original order. -/
@[expose] def copies (t : Nat) {m : Nat} (G : Graph m) : Graph (t * m) :=
  Graph.ofRel fun i j =>
    i.val / m == j.val / m &&
      (if h : m = 0 then false
       else G.adj ⟨i.val % m, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩
        ⟨j.val % m, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩)

/-- The `a × b` grid: vertex `(r, c)` is numbered `r*b + c`, and
vertices are adjacent when they differ by one in exactly one
coordinate. -/
@[expose] def grid (a b : Nat) : Graph (a * b) :=
  Graph.ofRel fun i j =>
    (i.val / b == j.val / b && j.val % b == i.val % b + 1) ||
    (i.val % b == j.val % b && j.val / b == i.val / b + 1)

/-- The hypercube of dimension `d`: vertices are the `2^d` bitstrings,
numbered by their value, adjacent when they differ in one bit. -/
@[expose] def hypercube (d : Nat) : Graph (2 ^ d) :=
  Graph.ofRel fun i j =>
    (List.range d).any fun b => j.val == i.val ^^^ (1 <<< b)

/-- The binomial coefficient, by the Pascal recurrence; `choose`
lives in Mathlib and this library is Mathlib-free. -/
@[expose] def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 => choose n r + choose n (r + 1)

/-- The `r`-element subset of `Fin m` with colexicographic rank `v`:
the standard combinatorial number system, choosing the largest possible
top element greedily. Elements are returned in descending order. -/
@[expose] def unrankColex (m r v : Nat) : List Nat :=
  go r v (m - 1) m
where
  go : Nat → Nat → Nat → Nat → List Nat
    | 0, _, _, _ => []
    | _ + 1, _, _, 0 => []
    | r + 1, v, c, fuel + 1 =>
      if choose c (r + 1) ≤ v then
        c :: go r (v - choose c (r + 1)) (c - 1) fuel
      else
        go (r + 1) v (c - 1) fuel

/-- The Johnson graph `J(m, r)` on the `choose m r` subsets of size `r`
in colexicographic order, adjacent when the subsets share `r - 1`
elements. -/
@[expose] def johnson (m r : Nat) : Graph (choose m r) :=
  Graph.ofRel fun i j =>
    ((unrankColex m r i.val).filter
      fun x => (unrankColex m r j.val).contains x).length + 1 == r

/-- The Kneser graph `K(m, r)` on the `choose m r` subsets of size `r`
in colexicographic order, adjacent when the subsets are disjoint. -/
@[expose] def kneser (m r : Nat) : Graph (choose m r) :=
  Graph.ofRel fun i j =>
    ((unrankColex m r i.val).filter
      fun x => (unrankColex m r j.val).contains x).length == 0

/-- The triangular graph `T(m) = J(m, 2)`. -/
@[expose] def triangular (m : Nat) : Graph (choose m 2) :=
  johnson m 2

/-- The Paley graph on `q` vertices: `i` and `j` are adjacent when their
difference is a nonzero quadratic residue modulo `q`, symmetrized. The
intended domain is a prime `q ≡ 1 (mod 4)`, where the residue relation
is already symmetric. -/
@[expose] def paley (q : Nat) : Graph q :=
  Graph.ofRel fun i j =>
    (List.range q).any fun x => x != 0 && (x * x) % q == (q + j.val - i.val) % q

/-- The one-cell coloured graph of a family member; `n = 0` requires
`k = 0`, so this is defined for positive `n`. -/
@[expose] def plain {n : Nat} (G : Graph n) (h : 0 < n) : Colored n 1 :=
  { graph := G, coloring := Coloring.trivial n h }

end Hex.GraphIso.Families
