/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellAll
import all HexGraphIso.Nauty.SmallCellLeaves

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

end Hex.GraphIso.Nauty
