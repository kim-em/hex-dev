/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeSweep
public import HexGraphIso.Nauty.SearchOutcomeTotal

public section

/-!
Fuel-separated totality statements for the transcribed search.

The logical fuel in `nodeKey`, the node recursion fuel, and a sibling
loop's cursor fuel are deliberately kept distinct.  The strict node-fuel
bound is preserved by descent and makes the executable zero-fuel branch
unreachable at every well-formed node.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Totality of one off-path node at a fixed executable recursion fuel. -/
@[expose] def OtherTotal (G : Colored n k) (ctx : Ctx)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes bs fs : List Nat)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail),
    ctx.n = n → ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    1 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    NodeInv G ctx tcLevel level codes bs fs numcells st best trail →
    Live ctx level st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel runFuel level codes fs st
        (otherNode ctx inf tcLevel runFuel level numcells st).2 numcells
        best outBest trail eventTrail
        (otherNode ctx inf tcLevel runFuel level numcells st).1

/-- Totality of one node on the unique descent preceding the first leaf. -/
@[expose] def FirstTotal (G : Colored n k) (ctx : Ctx)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes : List Nat)
    (st : SearchSt) (trail : FrameTrail),
    ctx.n = n → ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    1 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    FirstInv G ctx level codes numcells st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel specFuel runFuel level codes fs st
        (firstPathNode ctx inf tcLevel runFuel level numcells st).2
        numcells outBest trail eventTrail
        (firstPathNode ctx inf tcLevel runFuel level numcells st).1

/-- A well-formed search node cannot occur deeper than the graph. -/
theorem SearchOk.levelLe {G : Colored n k} {level numcells : Nat}
    {st : SearchSt} (h : SearchOk G level numcells st) : level ≤ n :=
  Nat.le_trans h.bc (bcount_le st.ptn level n)

/-- The strict node-fuel invariant rules out the zero-fuel off-path
branch before any operational case analysis is needed. -/
theorem OtherTotal.zero (G : Colored n k) (ctx : Ctx) (inf tcLevel : Nat) :
    OtherTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes bs fs st best trail hn _ _ _ _ _ _
    hfuel hnode _ _
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  omega

/-- The same strict bound rules out zero executable fuel on the initial
descent. -/
theorem FirstTotal.zero (G : Colored n k) (ctx : Ctx) (inf tcLevel : Nat) :
    FirstTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes st trail hn _ _ _ _ _ _ hfuel
    hfirst _
  have hle : level ≤ n := hfirst.searchOk.levelLe
  omega

end Hex.GraphIso.Nauty
