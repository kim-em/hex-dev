/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellAll
public import HexGraphIso.Nauty.CodeFaithful
import all HexGraphIso.Nauty.SmallCellLeaves
import all HexGraphIso.Nauty.CodeFaithful
import all HexGraphIso.Nauty.Search

public section

/-!
First-path geometry (SPEC § Verified search refinement, the code-1 arm
of the domination induction).

The refinement code cannot identify a descent: `mash` masks the
accumulator to fifteen bits, so the code is a hash of the splitting
history and two different partitions may share one. What does identify
a descent is its target-and-offset path, because every step is the
function `childSt` applied to the step's own target cell and offset.
`descPath_det` states that, and it is the fact both consumers of the
first-path thread need: the code-1 depth clause reaches it as "the
first path stopped where this leaf stopped", and the `FirstDescOk`
derivation reaches it as "the transported descent is the first path".

The state side of the same thread lives here too: the write sites of
`eqlevFirst` and `firsttc`, which is where the search decides whether
the current path still agrees with the first path.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # A descent is a function of its target-and-offset path -/

/-- Two descents from one state along one target-and-offset path end at
one state. Every `DescPath` step is `childSt` applied to the step's
recorded target cell and offset, so the path determines the descent
outright; no hypothesis about the graph, the partition or the codes is
needed. -/
theorem descPath_det :
    ∀ {level : Nat} {st : RefineSt} {path : List (Nat × Nat)}
      {l₁ l₂ : Nat} {st₁ st₂ : RefineSt},
      DescPath ctx level st path l₁ st₁ →
      DescPath ctx level st path l₂ st₂ →
      l₁ = l₂ ∧ st₁ = st₂
  | _, _, _, _, _, _, _, .refl _ _, .refl _ _ => ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, .step _ _ _ _ _ _ _ h₁, .step _ _ _ _ _ _ _ h₂ =>
      descPath_det h₁ h₂

/-- The level a descent ends at is a function of its path. -/
theorem descPath_det_level {level : Nat} {st : RefineSt}
    {path : List (Nat × Nat)} {l₁ l₂ : Nat} {st₁ st₂ : RefineSt}
    (h₁ : DescPath ctx level st path l₁ st₁)
    (h₂ : DescPath ctx level st path l₂ st₂) : l₁ = l₂ :=
  (descPath_det h₁ h₂).1

/-- The state a descent ends at is a function of its path. -/
theorem descPath_det_state {level : Nat} {st : RefineSt}
    {path : List (Nat × Nat)} {l₁ l₂ : Nat} {st₁ st₂ : RefineSt}
    (h₁ : DescPath ctx level st path l₁ st₁)
    (h₂ : DescPath ctx level st path l₂ st₂) : st₁ = st₂ :=
  (descPath_det h₁ h₂).2

/-- The labelling a descent ends with is a function of its path. This is
the form the `FirstDescOk` derivation applies: a descent transported
across the gca's child relation and the first path itself are the same
descent once their paths agree, so their labellings agree. -/
theorem descPath_det_lab {level : Nat} {st : RefineSt}
    {path : List (Nat × Nat)} {l₁ l₂ : Nat} {st₁ st₂ : RefineSt}
    (h₁ : DescPath ctx level st path l₁ st₁)
    (h₂ : DescPath ctx level st path l₂ st₂) : st₁.lab = st₂.lab := by
  rw [descPath_det_state h₁ h₂]

/-! # What the sentinel position records

`firstterminal` fires at the level where the first path went discrete,
and it is the only writer of `codeSentinel` into `firstcode`. The
sentinel's position therefore records the first path's depth, and
nothing later moves it: `firstPathNode` writes only at the levels it
descends through, and every event after `firstterminal` leaves
`firstcode` alone.

This is what turns the previous sitting's reduction into a statement
about the search's geometry. `firstCodeInv_eq_of_live` asks for
`firstcode[cs.length + 1]! = codeSentinel`; by the lemmas here that is
exactly "the first path went discrete at the current leaf's depth",
which is a fact about where two descents stop, not about an array
cell. -/

theorem firstterminal_firstcode (level : Nat) (st : SearchSt) :
    (firstterminal level st).firstcode =
      st.firstcode.set! (level + 1) codeSentinel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

theorem firstterminal_firsttc (level : Nat) (st : SearchSt) :
    (firstterminal level st).firsttc =
      st.firsttc.set! (level + 1) (-1) := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- The first path's depth is recorded by the sentinel: at the level
where `firstterminal` fires, the next `firstcode` entry is the
sentinel. -/
theorem firstterminal_sentinel {level : Nat} {st : SearchSt}
    (h : level + 1 < st.firstcode.size) :
    (firstterminal level st).firstcode[level + 1]! = codeSentinel := by
  rw [firstterminal_firstcode, Array.getElem!_set!_self _ _ _ h]

/-- The first path's target-cell record is `-1` just past its last
level, matching the discreteness that stopped it. -/
theorem firstterminal_firsttc_neg {level : Nat} {st : SearchSt}
    (h : level + 1 < st.firsttc.size) :
    (firstterminal level st).firsttc[level + 1]! = -1 := by
  rw [firstterminal_firsttc, Array.getElem!_set!_self _ _ _ h]

/-! # Where target-cell agreement comes from

`othernode` decides its target cell in two branches, and only one of
them checks agreement with the first path.

With `compCanon < 0` the node calls `maketargetcell` with the first
path's own record as the hint and demotes `eqlevFirst` to `level - 1`
when the chosen position differs from it, so agreement at that level is
enforced by the search itself.

With `compCanon` at least `0` the node calls `maketargetcell` with the
hint `-1`, which is exactly what `firstPathNode` passes, and performs no
check. The outer guard admits `eqlevFirst = level` here, so a live
`eqlevFirst` in this branch carries no state-level witness of agreement.
Agreement instead follows from the two nodes having equal partitions,
through the congruence below, since the target-cell choice is a function
of the partition and the hint.

Target-cell agreement and partition agreement are therefore one
level-by-level induction rather than two stages: agreement of the
targets below a level gives equal partitions at it, and equal partitions
at a level give agreement of the targets there. -/

/-- The target-cell choice is a function of the labelling, the partition
and the hint. This is the step that carries partition agreement into
target agreement in the branch where `othernode` performs no check. -/
theorem maketargetcell_congr {lab ptn lab' ptn' : Array Nat}
    {level tcLevel : Nat} {hint : Int}
    (hlab : lab = lab') (hptn : ptn = ptn') :
    maketargetcell ctx lab ptn level tcLevel hint =
      maketargetcell ctx lab' ptn' level tcLevel hint := by
  rw [hlab, hptn]

end Hex.GraphIso.Nauty
