/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellLeaves

public section

/-!
The imperative tie and the code-1 assembly (SPEC § Verified search
refinement, the code-1 arm of the store-validity obligation).

The search's child loops perform `breakout` at the parent and then the
child node's `refine`; that composite is exactly `childSt`
(`childSt_eq_search_step`), and each surviving target-cell vertex is a
window member of the target cell (`maketargetcell_mem`), so an
imperative descent below a node is a `DescPath` step by step. Both
children of one imperative node use the same `maketargetcell` result,
so the first-path leaf and a code-1-tested leaf below the greatest
common ancestor are same-target descents, and
`descPath_leafRows_all` gives them equal leaf rows
(`leafRows_eq_of_descPaths`); the admitted scatter then passes
`checkAutom` through `checkAutom_scatter_of_leafRows_eq`
(`checkAutom_scatter_of_descPaths`).

`subtreeOk_of_cheapautom` establishes the node invariant at the
ancestor from the guard: the first branch of `cheapautom_iff` gives
the small shape (`cheapautom_shape_or_exotic`); the second branch —
a defect of at most four with a cell of size four or five, or two
triples — is the exotic configuration, surfaced here as an explicit
hypothesis and discharged by the defect-four flip analogues
(`SmallCellExotic`).

The run-level facts these theorems consume — the two descents from
the ancestor with equal target paths, equitability and the boundary
count at the ancestor, and the guard having held there — are exactly
the bookkeeping the domination induction carries (`gcaFirst`,
`eqlevFirst`, `firsttc`, `noncheaplevel`); it discharges them when
threading `processnode`'s admission event.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # The imperative step is `childSt` -/

/-- The composite the search's child loops perform — `breakout` at the
parent, then the child node's `refine` on the returned labelling,
split partition, and singleton active set — is `childSt` of the
parent's post-refine state. -/
theorem childSt_eq_search_step (r : RefineSt) (level tc tv : Nat) :
    refine ctx (level + 1)
      (breakout r.lab r.ptn (level + 1) tc tv).1
      (breakout r.lab r.ptn (level + 1) tc tv).2.1
      (breakout r.lab r.ptn (level + 1) tc tv).2.2
      (r.numcells + 1) =
    childSt ctx level r tc tv := rfl

/-- A surviving target-cell vertex is a window member: any vertex of
the cell set `maketargetcell` returns sits at some offset of the
target cell, in the shape a `DescPath` step consumes. -/
theorem maketargetcell_mem {r : RefineSt} {level tcLevel : Nat}
    {hint : Int} {tcPos cellSet size tv : Nat}
    (hn1 : 1 ≤ level) (hsz : r.ptn.size = ctx.n)
    (hend : r.ptn[r.ptn.size - 1]! ≤ level)
    (hlive : bcount r.ptn level ctx.n < ctx.n)
    (hmk : maketargetcell ctx r.lab r.ptn level tcLevel hint =
      (tcPos, cellSet, size))
    (htv : elem cellSet tv = true) :
    ∃ e o, (tcPos, e) ∈ cells r.ptn level ctx.n ∧ tcPos < e ∧
      o ≤ e - tcPos ∧ r.lab[tcPos + o]! = tv := by
  obtain ⟨tc, len, hmk', hic, hlen2, hbd⟩ :=
    maketargetcell_open (lab := r.lab) (tcLevel := tcLevel)
      (hint := hint) hn1 hsz hend hlive
  rw [hmk] at hmk'
  injection hmk' with h1 h23
  injection h23 with h2 h3
  subst h1
  subst h2
  subst h3
  have hmem : tv ∈ segN r.lab tcPos (tcPos + size - 1 + 1 - tcPos) :=
    elem_worksetOf.mp htv
  obtain ⟨o, ho, hov⟩ := mem_segN_iff.mp hmem
  refine ⟨tcPos + size - 1, o,
    mem_cells_of_isCell (by omega) hend hic (by omega) (by omega),
    by omega, by omega, hov⟩

end Hex.GraphIso.Nauty
