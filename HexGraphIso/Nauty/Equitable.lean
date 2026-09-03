/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CellPerm

public section

/-!
Equitable partitions (SPEC § Verified search refinement, the
cheapautom clause of the store-validity obligation).

`refine` makes the partition at `level` equitable with respect to the
exhausted active set. The manual chapter states this as prose; this
file begins its formalization. The target theorem is: when
`refineLoop` exits because `pickSplit` finds no active cell, the
partition is `Equitable`. Discrete exits are covered separately by
`equitable_of_singletons`.

The intended loop invariant, recorded here for the follow-up work:
for every cell `C` of the current partition and every cell `D` not in
the active set, there is a set `U` of current cells with `D ∈ U` and
every other member of `U` active, such that `C` has constant
neighbour counts into the union of `U` (`SplitDone` on the union).
At exit the certificate `U` collapses to `{D}`, giving equitability.
The invariant survives a splitting pass because a pass leaves every
current cell with constant counts into the captured splitter set
(each processed cell is rearranged into constant-count groups, and a
cell that does not split already had constant counts), and because
`SplitDone` only strengthens under refinement of either cell. The
fragment that the activation rule leaves inactive is covered by the
certificate consisting of its active sibling fragments together with
the parent's certificate, since counts into the parent are the sum of
counts into the fragments. Exit by fuel is excluded by a potential
argument: `popCount active + 2 * (n - numcells)` drops by at least
one per pass, and starts at most `3 * n`, below the supplied
`4 * n + 8`.

This file proves the predicate layer and the per-cell postcondition
of the trivial-splitter pass. The pass level, the loop invariant, the
nontrivial-splitter pass, the fuel bound, and the cheapautom
small-cell lemma remain.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-- The window of `len` positions from `lo` has constant neighbour
counts into the vertex set `workset`. -/
def SplitDone (ctx : Ctx) (lab : Array Nat) (workset lo len : Nat) : Prop :=
  ∀ o o', o < len → o' < len →
    popCount (workset &&& ctx.g[lab[lo + o]!]!) =
      popCount (workset &&& ctx.g[lab[lo + o']!]!)

/-- The partition at `level` is equitable: every cell has constant
neighbour counts into every cell's vertex set. -/
def Equitable (ctx : Ctx) (level : Nat) (lab ptn : Array Nat) : Prop :=
  ∀ cd ∈ cells ptn level ctx.n, ∀ de ∈ cells ptn level ctx.n,
    SplitDone ctx lab (worksetOf lab de.1 de.2) cd.1 (cd.2 + 1 - cd.1)

/-- Constant counts restrict to any sub-window. -/
theorem SplitDone.sub {lab : Array Nat} {workset lo len lo' len' : Nat}
    (h : SplitDone ctx lab workset lo len) (hlo : lo ≤ lo')
    (hhi : lo' + len' ≤ lo + len) : SplitDone ctx lab workset lo' len' := by
  intro o o' ho ho'
  have h1 := h (lo' - lo + o) (lo' - lo + o') (by omega) (by omega)
  have e1 : lo + (lo' - lo + o) = lo' + o := by omega
  have e2 : lo + (lo' - lo + o') = lo' + o' := by omega
  rwa [e1, e2] at h1

/-- Windows with at most one position have constant counts. -/
theorem splitDone_of_le_one {lab : Array Nat} {workset lo len : Nat}
    (h : len ≤ 1) : SplitDone ctx lab workset lo len := by
  intro o o' ho ho'
  have : o = o' := by omega
  rw [this]

/-- Constant counts transfer between labellings agreeing on the
window. -/
theorem SplitDone.congr {lab lab' : Array Nat} {workset lo len : Nat}
    (h : SplitDone ctx lab workset lo len)
    (hagree : ∀ o, o < len → lab'[lo + o]! = lab[lo + o]!) :
    SplitDone ctx lab' workset lo len := by
  intro o o' ho ho'
  rw [hagree o ho, hagree o' ho']
  exact h o o' ho ho'

/-- A discrete partition is equitable. -/
theorem equitable_of_singletons {level : Nat} {lab ptn : Array Nat}
    (h : ∀ cd ∈ cells ptn level ctx.n, cd.2 = cd.1) :
    Equitable ctx level lab ptn := by
  intro cd hcd de _
  exact splitDone_of_le_one (by rw [h cd hcd]; omega)

/-- A power of two has one set bit. -/
private theorem popCount_two_pow : ∀ u : Nat, popCount (2 ^ u) = 1
  | 0 => by rw [Nat.pow_zero, popCount_eq, popCount_eq]; simp
  | u + 1 => by
    have h2 : 2 ^ (u + 1) = 2 * 2 ^ u := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, popCount_eq, Nat.mul_mod_right,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2), Nat.zero_add]
    exact popCount_two_pow u

/-- The count into a single-vertex set is the adjacency bit. -/
theorem popCount_and_single (u x : Nat) :
    popCount (insert 0 u &&& x) = if x.testBit u then 1 else 0 := by
  rcases hbit : x.testBit u with _ | _
  · have hz : insert 0 u &&& x = 0 := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_and, testBit_insert, Nat.zero_testBit,
        Bool.false_or]
      rcases Decidable.em (u = i) with rfl | hne
      · simp [hbit]
      · simp [hne]
    rw [hz, popCount_zero]
    rfl
  · have hs : insert 0 u &&& x = insert 0 u := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_and, testBit_insert, Nat.zero_testBit,
        Bool.false_or]
      rcases Decidable.em (u = i) with rfl | hne
      · simp [hbit]
      · simp [hne]
    have hval : insert 0 u = 2 ^ u := by
      show 0 ||| 1 <<< u = 2 ^ u
      rw [Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    rw [hs, hval, popCount_two_pow]
    rfl

/-- Constant adjacency to a vertex on a window gives constant counts
into its singleton set. -/
theorem splitDone_single_of_const {lab : Array Nat} {u lo len : Nat}
    {b : Bool}
    (hconst : ∀ o, o < len → (ctx.g[lab[lo + o]!]!).testBit u = b) :
    SplitDone ctx lab (insert 0 u) lo len := by
  intro o o' ho ho'
  rw [popCount_and_single, popCount_and_single, hconst o ho, hconst o' ho']

end Hex.GraphIso.Nauty
