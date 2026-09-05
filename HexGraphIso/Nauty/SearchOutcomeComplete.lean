/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeStep

public section

/-!
Fuel-separated totality statements for the transcribed search.

The logical fuel in `nodeKey`, the node recursion fuel, and a sibling
loop's cursor fuel are deliberately kept distinct.  The strict node-fuel
bound is preserved by descent and makes the executable zero-fuel branch
unreachable at every well-formed node.

Beyond the packaged run, each node statement carries the facts the
enclosing loops thread through it: the saved cheap-cell boundary, the
small-cell descent invariant at the refined frame, orbit soundness, the
coset cursor, and domination of the first leaf by the incumbent.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Facts a first-path node preserves or establishes beyond its packaged
run. -/
structure FirstKeep (ctx : Ctx n) (level : Nat) (st out : SearchSt n)
    (fs : List Nat) (outBest : Option (Key n)) : Prop where
  dom : ∀ b, outBest = some b → keyLe (pathLeafKey ctx fs out.firstlab) b
  orbits : OrbSound (OrbConn out.genTrace.toList n) out.orbits n
  coset : st.cosetindex < n → out.cosetindex < n
  boundary : out.noncheaplevel < level → out.noncheaplevel = st.noncheaplevel
  guide : level ≤ out.gcaFirst

/-- Totality of one off-path node at a fixed executable recursion fuel.
Off-path nodes are never the root, so the level is at least two. -/
@[expose] def OtherTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes bs fs : List Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    2 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    NodeInv G ctx tcLevel level codes bs fs numcells st best trail →
    Live ctx level st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    st.cosetindex < n →
    (∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b) →
    ∃ outBest eventTrail,
      OtherRun G ctx tcLevel specFuel runFuel level codes fs st
          (otherNode ctx inf tcLevel runFuel level numcells st).2 numcells
          best outBest trail eventTrail
          (otherNode ctx inf tcLevel runFuel level numcells st).1 ∧
        OtherKeep ctx level st
          (otherNode ctx inf tcLevel runFuel level numcells st).2

/-- Totality of one node on the unique descent preceding the first leaf. -/
@[expose] def FirstTotal (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel runFuel : Nat) : Prop :=
  ∀ (specFuel level numcells : Nat) (codes : List Nat)
    (st : SearchSt n) (trail : FrameTrail),
    ctx.g = rowsOf G → inf = n + 2 → 0 < n →
    1 ≤ level → level = codes.length + 1 →
    level + specFuel = n + 1 → n + 2 < level + runFuel →
    st.noncheaplevel ≤ level →
    CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells) →
    OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
    FirstInv G ctx level codes numcells st trail →
    PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st →
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel specFuel runFuel level codes fs st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel runFuel level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel runFuel level numcells st).2 fs
          outBest

/-- A well-formed search node cannot occur deeper than the graph. -/
theorem SearchOk.levelLe {G : Colored n k} {level numcells : Nat}
    {st : SearchSt n} (h : SearchOk G level numcells st) : level ≤ n :=
  Nat.le_trans h.bc (bcount_le st.ptn level n)

/-- The strict node-fuel invariant rules out the zero-fuel off-path
branch before any operational case analysis is needed. -/
theorem OtherTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    OtherTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes bs fs st best trail _ _ _ _ _ _
    hfuel _ _ hnode _ _ _ _ _
  have hle : level ≤ n := hnode.run.searchOk.levelLe
  omega

/-- The same strict bound rules out zero executable fuel on the initial
descent. -/
theorem FirstTotal.zero (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat) :
    FirstTotal G ctx inf tcLevel 0 := by
  intro specFuel level numcells codes st trail _ _ _ _ _ _ hfuel _ _ _
    hfirst _
  have hle : level ≤ n := hfirst.searchOk.levelLe
  omega

end Hex.GraphIso.Nauty
