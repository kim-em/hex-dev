/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexPermGroupMathlib
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Index

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The Rubik's cube group" =>
%%%
tag := "tutorial-rubiks-cube"
%%%

Each quarter turn of a Rubik's cube permutes its 54 coloured stickers, so the
positions reachable from the solved cube form a subgroup of the symmetric
group on 54 points. Lean can prove how many there are:

```lean
namespace RubiksCubeTutorial

def U : Equiv.Perm (Fin 54) :=
  c[0, 2, 8, 6] * c[1, 5, 7, 3] * c[9, 18, 36, 45] * c[10, 19, 37, 46] * c[11, 20, 38, 47]
def R : Equiv.Perm (Fin 54) :=
  c[2, 51, 29, 20] * c[5, 48, 32, 23] * c[8, 45, 35, 26] * c[9, 11, 17, 15] * c[10, 14, 16, 12]
def F : Equiv.Perm (Fin 54) :=
  c[6, 9, 29, 44] * c[7, 12, 28, 41] * c[8, 15, 27, 38] * c[18, 20, 26, 24] * c[19, 23, 25, 21]
def D : Equiv.Perm (Fin 54) :=
  c[15, 51, 42, 24] * c[16, 52, 43, 25] * c[17, 53, 44, 26] * c[27, 29, 35, 33] * c[28, 32, 34, 30]
def L : Equiv.Perm (Fin 54) :=
  c[0, 18, 27, 53] * c[3, 21, 30, 50] * c[6, 24, 33, 47] * c[36, 38, 44, 42] * c[37, 41, 43, 39]
def B : Equiv.Perm (Fin 54) :=
  c[0, 42, 35, 11] * c[1, 39, 34, 14] * c[2, 36, 33, 17] * c[45, 47, 53, 51] * c[46, 50, 52, 48]

/-- The positions reachable by turning the faces. -/
def RubikGroup : Subgroup (Equiv.Perm (Fin 54)) :=
  Subgroup.closure {U, R, F, D, L, B}

theorem card_rubikGroup : Nat.card RubikGroup = 43252003274489856000 := by
  perm_group

end RubiksCubeTutorial
```

The `perm_group` tactic comes from {ref "hex-perm-group"}[`HexPermGroupMathlib`].
It runs the Schreier–Sims algorithm in compiled code and has the kernel check
the resulting stabilizer chain, so the theorem depends only on the standard
axioms. The rest of this page proves which positions are out of reach, shows
how much the cube gains if it may be taken apart, and computes where the
turns can move a single sticker.

# Stickers and turns
%%%
tag := "tutorial-rubiks-cube-stickers"
%%%

The faces are up, right, front, down, left and back, in that order, and each
has nine stickers. Laid out flat, with the front face in the middle, the
stickers are numbered:

```
             0  1  2
             3  4  5
             6  7  8
 36 37 38   18 19 20    9 10 11   45 46 47
 39 40 41   21 22 23   12 13 14   48 49 50
 42 43 44   24 25 26   15 16 17   51 52 53
            27 28 29
            30 31 32
            33 34 35
```

Each turn above is a clockwise quarter turn of one face, seen from outside the
cube. It is written in Mathlib's cycle notation as five 4-cycles: the face's
own corner stickers, its own edge stickers, and three rows of stickers on the
four neighbouring faces. For example, `U` sends sticker `0` to `2`, and moves
the top row of the front face (`18`, `19`, `20`) onto the left face. The centre
stickers `4`, `13`, `22`, `31`, `40` and `49` never move.

# Positions that cannot be reached
%%%
tag := "tutorial-rubiks-cube-unreachable"
%%%

Twisting one corner in place, flipping one edge in place, or exchanging two
edges cannot be done by turning faces. Here they are as permutations of the
stickers. The corner at `8`, `9`, `20` sits between the up, right and front
faces; the edge at `7`, `19` between the up and front faces; and the edge at
`5`, `10` between the up and right faces.

```lean
namespace RubiksCubeTutorial

/-- Turn the up-right-front corner a third of a turn. -/
def twist : Equiv.Perm (Fin 54) := c[8, 9, 20]
/-- Flip the up-front edge. -/
def flip : Equiv.Perm (Fin 54) := c[7, 19]
/-- Exchange the up-front and up-right edges. -/
def swap : Equiv.Perm (Fin 54) := c[5, 7] * c[10, 19]

theorem twist_not_mem : twist ∉ RubikGroup := by perm_group
theorem flip_not_mem : flip ∉ RubikGroup := by perm_group
theorem swap_not_mem : swap ∉ RubikGroup := by perm_group

end RubiksCubeTutorial
```

The usual explanation uses invariants that every turn preserves: the corner
twists add up to zero modulo 3, the edge flips add up to zero modulo 2, and the
permutations of the corners and of the edges have the same sign. The proofs
above use none of this. `perm_group` sifts each permutation through the
stabilizer chain of {name}`RubiksCubeTutorial.RubikGroup` and the kernel checks
that the sift fails. The chain is checked once, by `card_rubikGroup`, and the
three proofs reuse it.

# Taking the cube apart
%%%
tag := "tutorial-rubiks-cube-assembly"
%%%

If the cube may be taken apart and put back together, the eight corners can go
into the eight corner slots in any order and any of three orientations, and
the twelve edges into the edge slots in any order and either orientation, for
`8! · 3⁸ · 12! · 2¹²` positions. Adding the three moves above to the six turns
generates all of them:

```lean
namespace RubiksCubeTutorial

/-- The positions reachable by turning faces and reassembling pieces. -/
def Assembly : Subgroup (Equiv.Perm (Fin 54)) :=
  Subgroup.closure {U, R, F, D, L, B, twist, flip, swap}

theorem card_assembly : Nat.card Assembly = 519024039293878272000 := by
  perm_group

theorem rubikGroup_le_assembly : RubikGroup ≤ Assembly := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_self, true_or, or_true]

theorem relIndex_rubikGroup : RubikGroup.relIndex Assembly = 12 := by
  have h := Subgroup.relIndex_mul_card (H := RubikGroup) (K := Assembly)
  rw [inf_of_le_left rubikGroup_le_assembly, card_rubikGroup, card_assembly] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

end RubiksCubeTutorial
```

The index is `12 = 3 · 2 · 2`, one factor for each invariant. A cube put back
together at random can be solved with probability `1/12`.

# Where a sticker can go
%%%
tag := "tutorial-rubiks-cube-orbits"
%%%

Mathlib's subgroup has no computational content, so for computations we build
the same group in {ref "hex-perm-group"}[`HexPermGroup`]. `Perm.ofEquiv`
converts each turn:

```lean
namespace RubiksCubeTutorial

open Hex Hex.PermGroup

def cube : Group 54 := Group.ofGenerators (#[U, R, F, D, L, B].map Perm.ofEquiv)

end RubiksCubeTutorial
```

The stickers fall into eight orbits:

```lean (name := rubikOrbits)
#eval RubiksCubeTutorial.cube.orbits.map (·.size)
```
```leanOutput rubikOrbits
#[24, 24, 1, 1, 1, 1, 1, 1]
```

The 24 corner stickers form one orbit and the 24 edge stickers another: turns
can carry any corner sticker to any other, but never to an edge. The six
centres are fixed.

By the orbit-stabilizer theorem, the positions that leave sticker `8` in place
are `1/24` of the group. Fixing that one sticker fixes its whole corner, since
the other two stickers of the corner must come along: the stabilizer of `8` is
as large as the subgroup fixing all of `8`, `9` and `20`.

```lean (name := rubikStabilizer)
#eval ((RubiksCubeTutorial.cube.stabilizer 8).order,
  (RubiksCubeTutorial.cube.pointwise [8, 9, 20]).order)
```
```leanOutput rubikStabilizer
(1802166803103744000, 1802166803103744000)
```

With that corner held in place, the turns still reach every position of the
other seven corners and of all twelve edges: the other 21 corner stickers form
one orbit, and the edge stickers another.

```lean (name := rubikStabilizerOrbits)
#eval (RubiksCubeTutorial.cube.stabilizer 8).orbits.map (·.size)
```
```leanOutput rubikStabilizerOrbits
#[21, 24, 1, 1, 1, 1, 1, 1, 1, 1, 1]
```

These numbers are computed by `#eval` and are not checked by the kernel. The
theorems {name}`Hex.PermGroup.Group.order_card` and
{name}`Hex.PermGroup.Group.contains_spec` connect the computational group to
Mathlib, as described in the {ref "hex-perm-group"}[`HexPermGroup` chapter].
