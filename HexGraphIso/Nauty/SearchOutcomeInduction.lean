/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLocatedProof
public import HexGraphIso.Nauty.QuartetNode

public section

/-!
Semantic state carried by the outcome-indexed search induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Both leaf references installed after the first descent are reached
permutation labellings. -/
structure LeafRefsOk (G : Colored n k) (st : SearchSt) : Prop where
  firstSize : st.firstlab.size = n
  firstReach : CellsReach G st.firstlab
  canonSize : st.canonlab.size = n
  canonReach : CellsReach G st.canonlab

/-- A permutation inside the cells of a reached search state is still
reachable from the initial coloured partition. -/
theorem CellsReach.ofCellsPerm {G : Colored n k} {level numcells : Nat}
    {st : SearchSt} {lab : Array Nat} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (hsize : lab.size = n)
    (hperm : cellsPerm st.ptn level st.lab lab) : CellsReach G lab := by
  have hinit := initial_nodeOk G hn0
  apply cellsPerm_trans hok.reach
  apply cellsPerm_coarsen
      (ptnC := initPtn n (n + 2) (initialPartition G).2)
      (ptnF := st.ptn) (levC := 1) (levF := level)
  · rw [size_initPtn, hok.ptnSize]
  · rw [hok.labSize, hok.ptnSize]
  · rw [hsize, hok.ptnSize]
  · exact hperm
  · exact searchOk_end hn0 hok hlevel
  · exact hinit.ptnEnd
  · intro q hq
    exact Nat.le_trans (hok.init1 q hq) hlevel

/-- Installing the first leaf seeds both valid leaf references. -/
theorem LeafRefsOk.firstterminal {G : Colored n k} {level numcells : Nat}
    {st : SearchSt} (hok : SearchOk G level numcells st) :
    LeafRefsOk G (firstterminal level st) := by
  constructor
  · rw [firstterminal_firstlab]
    exact hok.labSize
  · rw [firstterminal_firstlab]
    exact hok.reach
  · rw [firstterminal_canonlab]
    exact hok.labSize
  · rw [firstterminal_canonlab]
    exact hok.reach

/-- Every verified search fragment preserves validity of both installed
leaf references. -/
theorem SearchOut.leafRefs {G : Colored n k} {B level numcells : Nat}
    {st out : SearchSt} (h : SearchOut G B level st out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st) :
    LeafRefsOk G out := by
  constructor
  · rcases h.firstStore with heq | hperm
    · rw [heq]
      exact hrefs.firstSize
    · rw [hperm.1, hok.labSize]
  · rcases h.firstStore with heq | hperm
    · rw [heq]
      exact hrefs.firstReach
    · exact CellsReach.ofCellsPerm hn0 hlevel hok
        (by rw [hperm.1, hok.labSize]) hperm.2
  · rcases h.canon with heq | hreach
    · rw [heq]
      exact hrefs.canonSize
    · exact hreach.1
  · rcases h.canon with heq | hreach
    · rw [heq]
      exact hrefs.canonReach
    · exact hreach.2

/-! # Stable post-install state -/

/-- The semantic state available after the first leaf has been installed.

The explicit `level` makes the package usable both at node entries and
inside their child loops. At a node entry, `level = cs.length + 1`
recovers `DomOk`; a loop instead carries the code path through its current
node, so its path has length `level`. -/
structure RunInv (G : Colored n k) (ctx : Ctx) (rlab rptn : Array Nat)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  stab : ∀ γ ∈ st.genTrace,
    CellStab st.ptn level st.lab γ
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g rptn rlab 1 ctx.n st.autos
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel level st best trail
  nonpositive : st.compCanon ≤ 0
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- At a node boundary the stable package supplies the existing `DomOk`
record consumed by the leaf-event theorems. -/
theorem RunInv.dom {G : Colored n k} {ctx : Ctx} {rlab rptn : Array Nat}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunInv G ctx rlab rptn tcLevel level cs bs fs numcells st best
      trail)
    (hpath : level = cs.length + 1) :
    DomOk G ctx rlab rptn cs bs fs numcells st := by
  subst level
  exact ⟨h.searchOk, h.codeInv, h.firstInv, h.canongInv, h.stab,
    h.genTraceOk, h.autosOk⟩

/-- The semantic incumbent threaded by the induction agrees with the
stable imperative state. -/
theorem RunInv.read {G : Colored n k} {ctx : Ctx}
    {rlab rptn : Array Nat} {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunInv G ctx rlab rptn tcLevel level cs bs fs numcells st best
      trail) : stInc ctx st = best := by
  have hne : st.compCanon ≠ 1 := by
    intro heq
    have hnp := h.nonpositive
    rw [heq] at hnp
    omega
  rw [stInc_eq_ghost h.codeInv hne, ghostInc]
  simp only [h.bestCodes, ↓reduceIte, h.incumbent]

end Hex.GraphIso.Nauty
