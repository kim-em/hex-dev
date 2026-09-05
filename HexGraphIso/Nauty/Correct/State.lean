/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Unwind
public import HexGraphIso.Nauty.QuartetNode
public import HexGraphIso.Nauty.TargetCell
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.SmallCellTie

public section

/-!
The semantic state carried by the outcome-indexed search induction,
together with root-ledger preservation and leaf admission.
-/

/-!
Semantic state carried by the outcome-indexed search induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Elimination form of `LabInj`, exported so downstream outcome modules
need not unfold its intentionally opaque definition. -/
theorem LabInj.eq_of_getElem! {lab : Array Nat} {n i j : Nat}
    (h : LabInj lab n) (hi : i < n) (hj : j < n)
    (heq : lab[i]! = lab[j]!) : i = j := by
  exact h i j hi hj heq

/-- Both leaf references installed after the first descent are reached
permutation labellings. -/
structure LeafRefsOk (G : Colored n k) (st : SearchSt n) : Prop where
  firstSize : st.firstlab.size = n
  firstReach : CellsReach G st.firstlab
  canonSize : st.canonlab.size = n
  canonReach : CellsReach G st.canonlab

/-- A permutation inside the cells of a reached search state is still
reachable from the initial coloured partition. -/
theorem CellsReach.ofCellsPerm {G : Colored n k} {level numcells : Nat}
    {st : SearchSt n} {lab : Array Nat} (hn0 : 0 < n) (hlevel : 1 ≤ level)
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
    {st : SearchSt n} (hok : SearchOk G level numcells st) :
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
    {st out : SearchSt n} (h : SearchOut G B level st out)
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

/-! # Cheap-automorphism ledger boundary -/

/-- The implicit automorphism pair remains valid while search stays
strictly below the level at which that pair was frozen.  At the frozen
level itself the implication is deliberately dormant: `processnode` does
not insert an implicit pair there, and a failed cheap-automorphism guard
will move the boundary before the next descent. -/
structure CheapOk (ctx : Ctx n) (rlab rptn : Array Nat) (level : Nat)
    (st : SearchSt n) : Prop where
  positive : 0 < st.noncheaplevel
  labSize : st.lab.size = n
  ptnSize : st.ptn.size = n
  rootEnd : st.ptn[st.ptn.size - 1]! ≤ 1
  pair : st.noncheaplevel < level →
    PairOk ctx.g rptn rlab 1
      (fmptn st.lab st.ptn st.noncheaplevel n).1
      (fmptn st.lab st.ptn st.noncheaplevel n).2

/-- At a node entry, the runtime bound turns the strict-boundary ledger
invariant into the premise consumed by `processnode`. -/
theorem CheapOk.ready {ctx : Ctx n} {rlab rptn : Array Nat} {level : Nat}
    {st : SearchSt n} (h : CheapOk ctx rlab rptn level st)
    (hbound : st.noncheaplevel ≤ level) (hne : level ≠ st.noncheaplevel) :
    PairOk ctx.g rptn rlab 1
      (fmptn st.lab st.ptn st.noncheaplevel n).1
      (fmptn st.lab st.ptn st.noncheaplevel n).2 :=
  h.pair (by omega)

/-- The cheap-boundary invariant depends only on the current labelling,
partition, and boundary level. -/
theorem CheapOk.ofFrames {ctx : Ctx n} {rlab rptn : Array Nat}
    {level : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn level st)
    (hlab : out.lab = st.lab) (hptn : out.ptn = st.ptn)
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn level out := by
  constructor
  · rw [hncl]
    exact h.positive
  · rw [hlab]
    exact h.labSize
  · rw [hptn]
    exact h.ptnSize
  · rw [hptn]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    rw [hlab, hptn, hncl]
    exact h.pair hlt

/-- Reopening below `level` preserves every `fmptn` frozen at or above
the root and at or below `level`. -/
theorem recover_fmptn {st : SearchSt n} {inf level saved : Nat}
    (hsize : n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ saved)
    (hsaved : saved ≤ level) (hinf : level < inf) :
    fmptn (Nauty.recover n inf level st).lab
        (Nauty.recover n inf level st).ptn
        saved n =
      fmptn st.lab st.ptn saved n := by
  have hcells : cells (Nauty.recover n inf level st).ptn saved n =
      cells st.ptn saved n := by
    apply cells_eq_of_low (recover_ptn_size n inf level st)
    intro q hq
    rw [recover_ptn]
    rcases Decidable.em (q < n ∧ st.ptn[q]! > level) with hc | hc
    · rw [ite_eq_left hc]
      exfalso
      rcases hq with hold | hnew
      · omega
      · rw [recover_ptn, ite_eq_left hc] at hnew
        omega
    · rw [ite_eq_right hc]
  apply Eq.symm
  apply fmptn_congr hsize hend hcells.symm
  rw [recover_lab]
  exact cellsPerm_refl _ _ _

/-- Recovery either parks the boundary just below the next child, where
the strict obligation is dormant, or retains an older frozen pair. -/
theorem CheapOk.recover {ctx : Ctx n} {rlab rptn : Array Nat}
    {current level inf : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn current st) (hle : level ≤ current)
    (hlevel : 1 ≤ level) (hinf : level < inf) :
    CheapOk ctx rlab rptn level (Nauty.recover n inf level st) := by
  have hncl : (Nauty.recover n inf level st).noncheaplevel =
      if level < st.noncheaplevel then level + 1
      else st.noncheaplevel := by
    rw [Nauty.recover]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.noncheaplevel, ite_self]
  constructor
  · rw [hncl]
    split
    · omega
    · exact h.positive
  · rw [recover_lab]
    exact h.labSize
  · rw [recover_ptn_size]
    exact h.ptnSize
  · rw [recover_ptn_size, recover_ptn]
    rcases Decidable.em
        (st.ptn.size - 1 < n ∧
          st.ptn[st.ptn.size - 1]! > level) with hc | hc
    · rw [ite_eq_left hc]
      exfalso
      have := h.rootEnd
      omega
    · rw [ite_eq_right hc]
      exact h.rootEnd
  · intro hlt
    rcases Decidable.em (level < st.noncheaplevel) with hc | hc
    · rw [hncl, ite_eq_left hc] at hlt
      omega
    · have heq : (Nauty.recover n inf level st).noncheaplevel =
          st.noncheaplevel := by rw [hncl, ite_eq_right hc]
      rw [heq] at hlt ⊢
      have hpos := h.positive
      rw [recover_fmptn (Nat.le_of_eq h.ptnSize.symm)
        (Nat.le_trans h.rootEnd (by omega : 1 ≤ st.noncheaplevel))
        (by omega : st.noncheaplevel ≤ level) hinf]
      exact h.pair (by omega)

/-- Leaf processing does not move the frozen pair's defining fields. -/
theorem CheapOk.processnode {ctx : Ctx n} {rlab rptn : Array Nat}
    {level numcells : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn level st) :
    CheapOk ctx rlab rptn level (processnode ctx level numcells st).2 := by
  obtain ⟨hlab, hptn, -, -, -, -, -, hncl, -⟩ :=
    processnode_frames ctx level numcells st
  exact h.ofFrames hlab hptn hncl

/-- Installing the first leaf does not move the frozen pair's defining
fields. -/
theorem CheapOk.firstterminal {ctx : Ctx n} {rlab rptn : Array Nat}
    {level : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn level st) :
    CheapOk ctx rlab rptn level (Nauty.firstterminal level st) := by
  apply h.ofFrames
  · rw [Nauty.firstterminal]
    simp only [Id.run_bind, Id.run_pure]
  · rw [Nauty.firstterminal]
    simp only [Id.run_bind, Id.run_pure]
  · rw [Nauty.firstterminal]
    simp only [Id.run_bind, Id.run_pure]

/-- The comparison preparation step does not move the frozen pair's
defining fields. -/
theorem CheapOk.otherNodePrep {ctx : Ctx n} {rlab rptn : Array Nat}
    {level code : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn level st) :
    CheapOk ctx rlab rptn level (Nauty.otherNodePrep level code st) := by
  obtain ⟨-, -, -, -, -, -, -, -, hncl, -, -, hlab, hptn⟩ :=
    otherNodePrep_frames level code st
  exact h.ofFrames hlab hptn hncl

/-- Writing a boundary at or above the logical level suspends the pair
obligation without changing the partition facts needed to revive it. -/
theorem CheapOk.park {ctx : Ctx n} {rlab rptn : Array Nat}
    {old current boundary : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn old st) (hpos : 0 < boundary)
    (hcurrent : current ≤ boundary) :
    CheapOk ctx rlab rptn current
      { st with noncheaplevel := boundary } := by
  refine ⟨hpos, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  simp only
  omega

/-- A valid pair at the current boundary extends the invariant through
the next logical level. -/
theorem CheapOk.next {ctx : Ctx n} {rlab rptn : Array Nat}
    {level : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn level st)
    (hpair : st.noncheaplevel = level →
      PairOk ctx.g rptn rlab 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    CheapOk ctx rlab rptn (level + 1) st := by
  refine ⟨h.positive, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  intro hlt
  rcases Decidable.em (st.noncheaplevel = level) with heq | hne
  · exact hpair heq
  · exact h.pair (by omega)

/-- Refinement only splits at the current level and permutes within the
old current cells, so every pair frozen at a strictly smaller level is
unchanged. -/
theorem CheapOk.refine {ctx : Ctx n} {rlab rptn : Array Nat}
    {level numcells : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn level st) (hlevel : 1 ≤ level)
    (hlab : out.lab =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).lab)
    (hptn : out.ptn =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn level out := by
  let rs := Nauty.refine ctx level st.lab st.ptn st.active numcells
  have hnnEq : n = st.ptn.size := h.ptnSize.symm
  have hnn : n ≤ st.ptn.size := Nat.le_of_eq hnnEq
  have hls : st.lab.size = st.ptn.size := h.labSize.trans h.ptnSize.symm
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    Nat.le_trans h.rootEnd hlevel
  have hR := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hncl]
    exact h.positive
  · rw [hlab, hR.labSize]
    exact h.labSize
  · rw [hptn, hR.ptnSize]
    exact h.ptnSize
  · rw [hptn, hR.ptnSize]
    rw [refine_frozen hnnEq hls hend hend]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    have hpos := h.positive
    have hendSaved : st.ptn[st.ptn.size - 1]! ≤
        st.noncheaplevel := Nat.le_trans h.rootEnd (by omega)
    have hcells : cells st.ptn st.noncheaplevel n =
        cells rs.ptn st.noncheaplevel n := by
      apply Eq.symm
      apply cells_eq_of_low hR.ptnSize
      intro q hq
      rcases hq with hold | hnew
      · exact refine_frozen hnnEq hls hend
          (Nat.le_trans hold (Nat.le_of_lt hlt))
      · rcases ptn_refine_vals ctx level st.lab st.ptn st.active
            numcells q with heq | heq
        · exact heq
        · rw [heq] at hnew
          omega
    have hperm : cellsPerm st.ptn st.noncheaplevel st.lab rs.lab := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
          (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact hls
      · rw [hR.labSize]
        exact hls
      · exact hR.perm
      · exact hend
      · exact hendSaved
      · intro q hq
        exact Nat.le_trans hq (Nat.le_of_lt hlt)
    have hfm : fmptn st.lab st.ptn st.noncheaplevel n =
        fmptn rs.lab rs.ptn st.noncheaplevel n :=
      fmptn_congr hnn hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- Individualizing inside a current cell does not change the implicit
pair frozen at an older cheap boundary. -/
theorem CheapOk.breakout {ctx : Ctx n} {rlab rptn : Array Nat}
    {level tc len o : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn (level + 1) st)
    (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hlab : out.lab =
      (Nauty.breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1)
    (hptn : out.ptn = st.ptn.set! tc (level + 1))
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn (level + 1) out := by
  have hls : st.lab.size = st.ptn.size := h.labSize.trans h.ptnSize.symm
  have hpos := h.positive
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    Nat.le_trans h.rootEnd hlevel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hncl]
    exact h.positive
  · rw [hlab, breakout_lab_size]
    exact h.labSize
  · rw [hptn, Array.size_set!]
    exact h.ptnSize
  · rw [hptn, Array.size_set!]
    rw [Array.getElem!_set!_ne _ _ _ _ (by rw [h.ptnSize]; omega)]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    have hsaved : st.noncheaplevel ≤ level := by omega
    have hendSaved : st.ptn[st.ptn.size - 1]! ≤
        st.noncheaplevel := Nat.le_trans h.rootEnd (by omega)
    have hcells : cells st.ptn st.noncheaplevel n =
        cells (st.ptn.set! tc (level + 1)) st.noncheaplevel n := by
      apply Eq.symm
      apply cells_eq_of_low (by rw [Array.size_set!])
      intro q hq
      rcases Decidable.em (q = tc) with heq | hne
      · subst q
        have hopen := hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
        rw [Array.getElem!_set!_self _ _ _ (by rw [h.ptnSize]; omega)] at hq
        rcases hq with hq | hq <;> omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hne he.symm)]
    have hperm : cellsPerm st.ptn st.noncheaplevel st.lab
        (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
          (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact hls
      · rw [breakout_lab_size]
        exact hls
      · exact breakout_cellsPerm (n := n) hcell (by rw [h.ptnSize]; exact hrange)
          hls ho
      · exact hend
      · exact hendSaved
      · intro q hq
        exact Nat.le_trans hq hsaved
    have hfm : fmptn st.lab st.ptn st.noncheaplevel n =
        fmptn (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 (st.ptn.set! tc (level + 1))
          st.noncheaplevel n :=
      fmptn_congr (Nat.le_of_eq h.ptnSize.symm) hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- The initial search boundary is one, so its strict pair obligation is
empty at the root. -/
theorem CheapOk.root {G : Colored n k} {ctx : Ctx n} {numcells : Nat}
    {st : SearchSt n} (hn0 : 0 < n)
    (hok : SearchOk G 1 numcells st) (hncl : st.noncheaplevel = 1) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) 1 st := by
  refine ⟨by rw [hncl]; exact Nat.zero_lt_succ 0, ?_, ?_,
    searchOk_end hn0 hok (Nat.le_refl 1), ?_⟩
  · rw [hok.labSize]
  · rw [hok.ptnSize]
  · intro hlt
    rw [hncl] at hlt
    omega

/-! # Stable post-install state -/

/-- The semantic state available after the first leaf has been installed.

The explicit `level` makes the package usable both at node entries and
inside their child loops. At a node entry, `level = cs.length + 1`
recovers `DomOk`; a loop instead carries the code path through its current
node, so its path has length `level`. The comparison sign is deliberately
unrestricted: an internal node whose code first exceeds the incumbent can
enter its child loop with sign one. Consumers that read the mutable
incumbent or return an event supply the appropriate sign premise. -/
structure RunInv (G : Colored n k) (ctx : Ctx n)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g
    (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 1 st.autos
  workspace : WorkspaceOk st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel level st best trail
  trailOk : TrailOk ctx level st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  firstBound : st.gcaFirst ≤ level
  canonBound : st.gcaCanon ≤ level
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- At a node boundary the stable package supplies the existing `DomOk`
record consumed by the leaf-event theorems. -/
theorem RunInv.dom {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best
      trail)
    (hpath : level = cs.length + 1)
    (hstab : ∀ γ ∈ st.genTrace,
      CellStab st.ptn level st.lab γ) :
    DomOk G ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      cs bs fs numcells st := by
  subst level
  exact ⟨h.searchOk, h.codeInv, h.firstInv, h.canongInv, hstab,
    h.genTraceOk, h.autosOk⟩

/-- The semantic incumbent threaded by the induction agrees with the
stable imperative state. -/
theorem RunInv.read {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best
      trail) (hne : st.compCanon ≠ 1) : stInc ctx st = best := by
  rw [stInc_eq_ghost h.codeInv hne, ghostInc]
  simp only [h.bestCodes, ↓reduceIte, h.incumbent]

/-! # Post-refinement comparison state -/

/-- The semantic state after refinement and `otherNodePrep`, before
`processnode` restores the stable comparison sign.  This differs from
`RunInv` only in omitting `compCanon ≤ 0`: comparing the freshly appended
refinement code may set the sign to one. -/
structure RunPrep (G : Colored n k) (ctx : Ctx n)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g
    (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 1 st.autos
  workspace : WorkspaceOk st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel level st best trail
  trailOk : TrailOk ctx level st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  firstBound : st.gcaFirst ≤ level
  canonBound : st.gcaCanon ≤ level
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- Once no immediate comparison prune is pending, the prepared state is
the ordinary state carried into a child sweep. The two records are kept
separate because `RunPrep` is also consumed by the leaf classifiers. -/
theorem RunPrep.run {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail) :
    RunInv G ctx tcLevel level cs bs fs numcells st best trail :=
  ⟨h.searchOk, h.codeInv, h.firstInv, h.canongInv, h.genTraceOk,
    h.autosOk, h.workspace, h.cheap, h.leafRefs, h.guides, h.trailOk,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-! # Node-entry refinement state -/

/-- Equitability depends only on the vertex sets of the partition cells,
not on their order inside each cell. -/
theorem Equitable.ofCellsPerm {ctx : Ctx n} {level : Nat}
    {lab lab' ptn : Array Nat}
    (heq : Equitable ctx level lab ptn)
    (hperm : cellsPerm ptn level lab lab')
    (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    Equitable ctx level lab' ptn := by
  intro cd hcd de hde
  have hcdCell := cells_isCell (Nat.le_of_eq hpsz.symm) hend cd hcd
  have hdeCell := cells_isCell (Nat.le_of_eq hpsz.symm) hend de hde
  have hcdPerm := hperm cd.1 (cd.2 + 1 - cd.1) hcdCell
  have hdePerm := hperm de.1 (de.2 + 1 - de.1) hdeCell
  have hwork : worksetOf n lab de.1 de.2 = worksetOf n lab' de.1 de.2 :=
    worksetOf_perm hdePerm
  rw [splitDone_iff_constOn]
  rw [← hwork]
  exact (splitDone_iff_constOn.mp (heq cd hcd de hde)).perm hcdPerm.symm

/-- The extra certificate state needed exactly where a node is about to
call `refine`.  `RunInv` is deliberately weaker because it also describes
recovered parent-loop states, whose stale `active` field is never refined
again. -/
structure NodeInv (G : Colored n k) (ctx : Ctx n)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt n) (best : Option (Key n)) (trail : FrameTrail) : Prop where
  run : RunInv G ctx tcLevel level cs bs fs numcells st best trail
  cert : CertInv ctx level
    { lab := st.lab, ptn := st.ptn, active := st.active,
      numcells := numcells, hint := 0, maxpos := 0,
      longcode := numcells }
  activeStarts : ∀ v : Nat, st.active.mem v = true →
    v = 0 ∨ st.ptn[v - 1]! ≤ level
  firstBelow : st.gcaFirst < level
  canonBelow : st.gcaCanon < level
  shortClear : st.needshortprune = false

/-- Refining a valid node entry produces the equitable frame used by its
target-cell selection and child sweep. -/
theorem NodeInv.refined {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level)
    (h : NodeInv G ctx tcLevel level cs bs fs numcells st best trail) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    IterOk ctx level r ∧ Equitable ctx level r.lab r.ptn ∧
      bcount r.ptn level n = r.numcells := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  have hend := searchOk_end hn0 h.run.searchOk hlevel
  have hls : st.lab.size = n := h.run.searchOk.labSize
  have hps : st.ptn.size = n := h.run.searchOk.ptnSize
  have hlab : LabOk st.lab n :=
    labOk_of_reach h.run.searchOk.labSize h.run.searchOk.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach h.run.searchOk.labSize hn0 h.run.searchOk.reach
  have hrst : StOk n level r := by
    apply refine_stOk (ctx := ctx) hls hlab hps hend
  have hrreach : CellsReach G r.lab := by
    apply refine_cellsReach hn0 h.run.searchOk.reach
      h.run.searchOk.labSize h.run.searchOk.ptnSize hend
    intro q hq
    exact Nat.le_trans (h.run.searchOk.init1 q hq) hlevel
  have hrit : IterOk ctx level r := by
    refine ⟨hrst, ?_, ?_, ?_⟩
    · exact labInj_of_reach hrst.labSize hn0 hrreach
    · intro q hq
      rcases ptn_refine_vals ctx level st.lab st.ptn st.active
        numcells q with he | he
      · rw [he]
        rcases h.run.searchOk.vals q hq with hq | hq
        · exact Or.inl hq
        · exact Or.inr hq
      · rw [he]
        exact Or.inl (Nat.le_refl level)
    · have hb := h.run.searchOk.bc
      have hbn := bcount_le st.ptn level n
      omega
  have heqt : Equitable ctx level r.lab r.ptn := by
    apply refine_equitable hls hlab hps hend hinj h.activeStarts
    · intro u v hu hv
      rw [hg]
      exact rowsOf_symm G u v hu hv
    · exact h.run.searchOk.count.symm
    · exact h.cert
  have hacc : bcount r.ptn level n = r.numcells := by
    have hc := refine_bcount (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (active := st.active)
      (numcells := numcells) hps.symm (by rw [hls, hps]) hend
    have hold := h.run.searchOk.count
    change r.numcells + bcount st.ptn level n =
      numcells + bcount r.ptn level n at hc
    omega
  exact ⟨hrit, heqt, hacc⟩

/-- The unhinted executable target record of an internal node is exactly
the specification target record, together with its nontrivial-cell
geometry. -/
theorem NodeInv.target {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level)
    (h : NodeInv G ctx tcLevel level cs bs fs numcells st best trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    ∃ tc len,
      maketargetcell ctx r.lab r.ptn level tcLevel (-1) =
        (tc, worksetOf n r.lab tc (tc + len - 1), len) ∧
      specMaketargetcell ctx r.lab r.ptn level tcLevel =
        (tc, worksetOf n r.lab tc (tc + len - 1), len) ∧
      IsCell r.ptn level tc len ∧ 2 ≤ len ∧
      tc + len ≤ n := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  have href := h.refined hg hn0 hlevel
  have htarget : maketargetcell ctx r.lab r.ptn level tcLevel (-1) =
      specMaketargetcell ctx r.lab r.ptn level tcLevel := by
    apply maketargetcell_eq_spec href.2.1 href.1.ok.labOk
      href.1.ok.labSize href.1.ok.ptnSize href.1.ok.ptnEnd
  have hlive : bcount r.ptn level n < n := by
    have hb : r.numcells ≤ n := by
      rw [← href.2.2]
      exact bcount_le r.ptn level n
    have hne : r.numcells ≠ n := by
      simpa only [r] using hnum
    calc
      bcount r.ptn level n = r.numcells := href.2.2
      _ < n := Nat.lt_of_le_of_ne hb hne
  obtain ⟨tc, len, hmk, hcell, hlen, hrange⟩ :=
    maketargetcell_open (lab := r.lab) (tcLevel := tcLevel)
      (hint := (-1 : Int)) hlevel href.1.ok.ptnSize
      href.1.ok.ptnEnd hlive
  exact ⟨tc, len, hmk, htarget.symm.trans hmk,
    hcell, hlen, hrange⟩

/-- The target record supplied by `NodeInv.target` exposes the node key as
the exact maximum swept by the executable child loop. -/
theorem NodeInv.children {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat}
    {cs bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (_h : NodeInv G ctx tcLevel level cs bs fs numcells st best trail)
    (hdisc : discreteAt
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level n = false)
    (hspec : specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tcLevel =
        (tc, worksetOf n
          (refine ctx level st.lab st.ptn st.active numcells).lab
          tc (tc + len - 1), len))
    (hlen : 2 ≤ len) :
    nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab
          (refine ctx level st.lab st.ptn st.active numcells).ptn tc
          (refine ctx level st.lab st.ptn st.active numcells).numcells 0)
        ((List.range (len - 1)).map fun o =>
          sweepKey ctx tcLevel specFuel level
            (cs ++ [(refine ctx level st.lab st.ptn st.active
              numcells).longcode])
            (refine ctx level st.lab st.ptn st.active numcells).lab
            (refine ctx level st.lab st.ptn st.active numcells).ptn tc
            (refine ctx level st.lab st.ptn st.active numcells).numcells
            (o + 1)) := by
  have hout := nodeKey_children (ctx := ctx) (tcLevel := tcLevel)
    (fuel := specFuel) (level := level) (numcells := numcells)
    (len := len - 1) (cs := cs) (st := st) hdisc (by
      rw [hspec]
      simp only
      omega)
  rw [hspec] at hout
  exact hout

/-- Individualization carries a stable loop state into a valid recursive
node entry. The loop supplies the two facts that depend on its history:
the cheap-boundary state selected by the guard and the newly active guide
store. Parent equitability seeds the child's refinement certificate. -/
theorem RunInv.child {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc len o coset : Nat}
    {cs bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail childTrail : FrameTrail}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail)
    (heq : Equitable ctx level st.lab st.ptn)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hshort : st.needshortprune = false)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st)
    (hguides : GuideStore ctx tcLevel (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]!
        cosetindex := coset }
      best childTrail)
    (htrail : TrailOk ctx (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]!
        cosetindex := coset }
      childTrail) :
    NodeInv G ctx tcLevel (level + 1) cs bs fs (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]!
        cosetindex := coset }
      best childTrail := by
  let child : SearchSt n := { st with
    lab := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1
    ptn := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).2.1
    active := (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).2.2
    fixedpts := st.fixedpts.insert st.lab[tc + o]!
    cosetindex := coset }
  have hok : SearchOk G (level + 1) (numcells + 1) child := by
    apply breakout_searchOk hn0 h.searchOk hlevel hcell hlen hrange ho
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!
    · rfl
  change NodeInv G ctx tcLevel (level + 1) cs bs fs (numcells + 1)
    child best childTrail
  have hrun : RunInv G ctx tcLevel (level + 1) cs bs fs
      (numcells + 1) child best childTrail := by
    refine ⟨hok, h.codeInv, h.firstInv, h.canongInv, h.genTraceOk,
      h.autosOk, ?_, ?_, ?_, hguides, htrail, h.firstPositive,
      h.canonPositive, ?_, ?_, h.bestCodes, h.incumbent⟩
    · exact h.workspace.ofFields rfl rfl
    · apply hcheap.breakout hlevel hcell hlen hrange ho <;> rfl
    · exact ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
        h.leafRefs.canonSize, h.leafRefs.canonReach⟩
    · change st.gcaFirst ≤ level + 1
      exact Nat.le_trans h.firstBound (Nat.le_succ level)
    · change st.gcaCanon ≤ level + 1
      exact Nat.le_trans h.canonBound (Nat.le_succ level)
  refine ⟨hrun, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem : (tc, tc + len - 1) ∈ cells st.ptn level n := by
      apply isCell_mem_cells hcell
      · exact Nat.le_of_eq h.searchOk.ptnSize.symm
      · exact searchOk_end hn0 h.searchOk hlevel
      · omega
    have hcert := certInv_breakout (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (tc := tc)
      (e := tc + len - 1) (o := o) (numcells := numcells)
      h.searchOk.labSize h.searchOk.ptnSize
      (searchOk_end hn0 h.searchOk hlevel) (by
        intro q hq
        rcases h.searchOk.vals q hq with hq | hq
        · exact Or.inl hq
        · right
          have hb := bcount_le st.ptn level n
          have hc := h.searchOk.bc
          omega)
      (labInj_of_reach h.searchOk.labSize hn0 h.searchOk.reach)
      hmem (by omega) (by omega) heq
    change CertInv ctx (level + 1)
      { lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1,
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1,
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 }
    rw [breakout_ptn]
    exact hcert
  · change ∀ v : Nat,
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.2.mem v = true →
      v = 0 ∨ (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1[v - 1]! ≤ level + 1
    rw [breakout_ptn]
    exact split_starts hcell (by omega)
  · change st.gcaFirst < level + 1
    exact Nat.lt_succ_of_le h.firstBound
  · change st.gcaCanon < level + 1
    exact Nat.lt_succ_of_le h.canonBound
  · change st.needshortprune = false
    exact hshort

/-- Refinement followed by the off-path comparison step enters
`RunPrep`.  Generator validity is global, while stabilization is proved
only at the loop frame where a generator is consumed. -/
theorem RunInv.otherLeaf {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hpath : level = cs.length + 1)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail) :
    RunPrep G ctx tcLevel level
      (cs ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st) best trail := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  have hout : otherLeafSt ctx level numcells st =
      otherNodePrep level rs.longcode base := by
    rfl
  have hframes := otherNodePrep_frames level rs.longcode base
  have hstore := otherNodePrep_store level rs.longcode base
  have hlab : (otherLeafSt ctx level numcells st).lab = rs.lab := by
    rw [hout, hframes.2.2.2.2.2.2.2.2.2.2.2.1]
  have hptn : (otherLeafSt ctx level numcells st).ptn = rs.ptn := by
    rw [hout, hframes.2.2.2.2.2.2.2.2.2.2.2.2]
  have hcanon : (otherLeafSt ctx level numcells st).canonlab =
      st.canonlab := by
    rw [hout, hframes.1]
  have hfirst : (otherLeafSt ctx level numcells st).firstlab =
      st.firstlab := by
    rw [hout, hframes.2.2.2.2.1]
  have hgcaFirst : (otherLeafSt ctx level numcells st).gcaFirst =
      st.gcaFirst := by
    rw [hout, hframes.2.2.2.2.2.2.1]
  have hgcaCanon : (otherLeafSt ctx level numcells st).gcaCanon =
      st.gcaCanon := by
    rw [hout, hframes.2.2.2.2.2.2.2.1]
  have hncl : (otherLeafSt ctx level numcells st).noncheaplevel =
      st.noncheaplevel := by
    rw [hout, hframes.2.2.2.2.2.2.2.2.1]
  have hgen : (otherLeafSt ctx level numcells st).genTrace =
      st.genTrace := by
    rw [hout, hstore.1]
  have hautos : (otherLeafSt ctx level numcells st).autos = st.autos := by
    rw [hout, hstore.2]
  have hok : SearchOk G level rs.numcells
      (otherLeafSt ctx level numcells st) :=
    refine_searchOk hn0 h.searchOk hlevel hlab hptn (Or.inl hcanon)
  have htrail : TrailOk ctx level (otherLeafSt ctx level numcells st)
      trail := by
    apply h.trailOk.refine
    · rw [h.searchOk.labSize]
    · rw [h.searchOk.ptnSize]
    · exact searchOk_end hn0 h.searchOk hlevel
    · exact hlab
    · exact hptn
  subst level
  refine ⟨hok,
    otherNodePrep_codeInv h.codeInv
      (refine_longcode_lt ctx (cs.length + 1) st.lab st.ptn st.active
        numcells) ?_,
    otherNodePrep_firstCodeInv h.firstInv
      (refine_longcode_lt ctx (cs.length + 1) st.lab st.ptn st.active
        numcells), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        h.bestCodes, ?_⟩
  · have hb := bcount_le st.ptn (cs.length + 1) n
    have hc := h.searchOk.bc
    omega
  · rw [hout]
    exact canongInv_otherNodePrep h.canongInv
  · exact genTraceOk_of_eq hgen h.genTraceOk
  · exact autosOk_of_eq hautos h.autosOk
  · exact h.workspace.ofFields (WorkspaceOk.prepCap _ _ _) hautos
  · apply h.cheap.refine (by omega) hlab hptn hncl
  · exact ⟨by rw [hfirst]; exact h.leafRefs.firstSize,
      by rw [hfirst]; exact h.leafRefs.firstReach,
      by rw [hcanon]; exact h.leafRefs.canonSize,
      by rw [hcanon]; exact h.leafRefs.canonReach⟩
  · exact h.guides.stateEq hgcaFirst hfirst hgcaCanon hcanon
  · exact htrail
  · rw [hgcaFirst]
    exact h.firstPositive
  · rw [hgcaCanon]
    exact h.canonPositive
  · rw [hgcaFirst]
    exact h.firstBound
  · rw [hgcaCanon]
    exact h.canonBound
  · rw [hcanon]
    exact h.incumbent

/-! # First-leaf phase transition -/

/-- The state fields needed to enter the stable induction immediately
after `firstterminal`. -/
theorem firstterminal_state (level : Nat) (st : SearchSt n) :
    (firstterminal level st).lab = st.lab ∧
    (firstterminal level st).ptn = st.ptn ∧
    (firstterminal level st).gcaFirst = level ∧
    (firstterminal level st).gcaCanon = level ∧
    (firstterminal level st).compCanon = 0 := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  simp

/-- Neither first-leaf preparation nor installation raises a short-prune
request. -/
theorem firstterminal_short (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (firstterminal level (firstLeafSt ctx level numcells st)).needshortprune =
      st.needshortprune := by
  rw [firstterminal, firstLeafSt]
  simp only [Id.run_bind, Id.run_pure]

/-- Installing the first leaf preserves the search skeleton and records a
reached canonical labelling. -/
theorem SearchOk.firstterminal {G : Colored n k} {level numcells : Nat}
    {st : SearchSt n} (h : SearchOk G level numcells st) :
    SearchOk G level numcells (Nauty.firstterminal level st) := by
  obtain ⟨hlab, hptn, -, -, -⟩ := firstterminal_state level st
  constructor
  · rw [hlab]
    exact h.labSize
  · rw [hptn]
    exact h.ptnSize
  · rw [hlab]
    exact h.reach
  · intro q hq
    rw [hptn]
    exact h.init1 q hq
  · intro q hq
    rw [hptn]
    exact h.vals q hq
  · rw [hptn]
    exact h.count
  · rw [hptn]
    exact h.bc
  · rw [firstterminal_canonlab]
    exact Or.inr ⟨h.labSize, h.reach⟩

/-- The first leaf changes the pre-incumbent descent into the stable
post-install invariant. Both mutable stores are still empty at this point;
all later store growth is handled by the ordinary node induction. -/
theorem RunInv.firstterminal {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hpath : level = cs.length) (hok : SearchOk G level numcells st)
    (hfirstSize : st.firstcode.size = n + 2)
    (hcanonSize : st.canoncode.size = n + 2)
    (hbound : cs.length ≤ n)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel)
    (hcanong : st.canong.size = n)
    (hgen : st.genTrace = #[]) (hautos : st.autos = #[])
    (hworkspace : WorkspaceOk st)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) cs.length st)
    (htrail : TrailOk ctx level st trail)
    (hne : cs ≠ []) :
    RunInv G ctx tcLevel level cs cs cs numcells
      (Nauty.firstterminal level st)
      (some (pathLeafKey ctx cs st.lab)) trail := by
  subst level
  have hstate := firstterminal_state cs.length st
  have hstore := firstterminal_store cs.length st
  have hpositive : 0 < cs.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hne (List.length_eq_zero_iff.mp hz)
  refine ⟨hok.firstterminal,
    firstterminal_codeInv hcanonSize hbound hcodes hlt,
    firstterminal_firstCodeInv hfirstSize hbound hcodes hlt,
    firstterminal_canongInv hcanong, ?_, ?_,
    ?_, hcheap.firstterminal, LeafRefsOk.firstterminal hok, ?_, ?_, ?_, ?_,
    ?_, ?_, hne, ?_⟩
  · unfold GenTraceOk
    intro γ hγ
    rw [hstore.1, hgen] at hγ
    simp at hγ
  · intro p hp
    rw [hstore.2, hautos] at hp
    simp at hp
  · exact hworkspace.ofFields (WorkspaceOk.firstCap _ _) hstore.2
  · constructor
    · intro _ hbelow
      rw [hstate.2.2.1] at hbelow
      omega
    · intro _ hbelow
      rw [hstate.2.2.2.1] at hbelow
      omega
  · exact htrail.stateEq hstate.1 hstate.2.1
  · rw [hstate.2.2.1]
    exact hpositive
  · rw [hstate.2.2.2.1]
    exact hpositive
  · rw [hstate.2.2.1]
    exact Nat.le_refl _
  · rw [hstate.2.2.2.1]
    exact Nat.le_refl _
  · rw [firstterminal_canonlab]
    rfl

/-! # Unwind framing -/

/-- `recover` clamps the canonical guide target to the receiving level. -/
theorem recover_gcaCanon (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).gcaCanon =
      if level < st.gcaCanon then level else st.gcaCanon := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.gcaCanon, ite_self]
  repeat' split
  all_goals rfl

/-- Parent recovery leaves the one-shot short-prune request unchanged. -/
theorem recover_needshortprune (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).needshortprune = st.needshortprune := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.needshortprune, ite_self]

/-- Clearing the one-shot prune request commutes with parent recovery. -/
theorem recover_clearShort (n inf level : Nat) (st : SearchSt n) :
    recover n inf level { st with needshortprune := false } =
      { recover n inf level st with needshortprune := false } := by
  rw [recover, recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Recovering a parent frame preserves both installed leaf references. -/
theorem LeafRefsOk.recover {G : Colored n k} {inf level : Nat}
    {st : SearchSt n} (h : LeafRefsOk G st) :
    LeafRefsOk G (Nauty.recover n inf level st) := by
  obtain ⟨hcanon, -, -, -, hfirst, -, -, -, -, -⟩ :=
    recover_frames n inf level st
  constructor
  · rw [hfirst]
    exact h.firstSize
  · rw [hfirst]
    exact h.firstReach
  · rw [hcanon]
    exact h.canonSize
  · rw [hcanon]
    exact h.canonReach

/-- Recovering to an ancestor drops any guide aimed at the receiving
frame and preserves every strictly older located guide. -/
theorem GuideStore.recover {ctx : Ctx n} {tcLevel current : Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    {inf level : Nat}
    (h : GuideStore ctx tcLevel current st best trail)
    (hle : level ≤ current) :
    GuideStore ctx tcLevel level (Nauty.recover n inf level st) best
      trail := by
  obtain ⟨hcanonlab, -, -, -, hfirstlab, -, hgcaFirst, -, -, -⟩ :=
    recover_frames n inf level st
  constructor
  · intro hp hlt
    rw [hgcaFirst] at hp hlt ⊢
    obtain ⟨g, href, hloc⟩ := h.first hp
      (Nat.lt_of_lt_of_le hlt hle)
    exact ⟨g, href.trans hfirstlab.symm, hloc⟩
  · intro hp hlt
    have hgcaCanon : (Nauty.recover n inf level st).gcaCanon =
        st.gcaCanon := by
      rcases Decidable.em (level < st.gcaCanon) with hclamp | hkeep
      · have hcontra := hlt
        rw [recover_gcaCanon, ite_eq_left hclamp] at hcontra
        omega
      · rw [recover_gcaCanon, ite_eq_right hkeep]
    rw [hgcaCanon] at hp hlt ⊢
    obtain ⟨g, href, hloc⟩ := h.canon hp
      (Nat.lt_of_lt_of_le hlt hle)
    exact ⟨g, href.trans hcanonlab.symm, hloc⟩

/-- A leaf event preserves every older guide when the first reference is
unchanged and any changed canonical reference is installed at the current
level. -/
theorem GuideStore.processnode {ctx : Ctx n} {tcLevel level : Nat}
    {st out : SearchSt n} {before best : Option (Key n)} {trail : FrameTrail}
    (h : GuideStore ctx tcLevel level st before trail)
    (hinc : IncGrows before best)
    (hfirst : out.gcaFirst = st.gcaFirst)
    (hfirstlab : out.firstlab = st.firstlab)
    (hcanon : out.gcaCanon < level →
      out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) :
    GuideStore ctx tcLevel level out best trail := by
  have hgrow := h.grow hinc
  constructor
  · intro hp hlt
    rw [hfirst] at hp hlt ⊢
    obtain ⟨g, href, hloc⟩ := hgrow.first hp hlt
    exact ⟨g, href.trans hfirstlab.symm, hloc⟩
  · intro hp hlt
    obtain ⟨hgca, href⟩ := hcanon hlt
    rw [hgca] at hp hlt ⊢
    obtain ⟨g, href', hloc⟩ := hgrow.canon hp hlt
    exact ⟨g, href'.trans href.symm, hloc⟩

/-! # Event state and recovery -/

/-- State returned by a node event before its caller applies `recover`.
The second comparison-machine case is the row-rejection reset: the
mutable sign is negative while the retained proof is deliberately stated
at sign zero, exactly as required by `recover_codeInv_reset`. -/
structure RunEvent (G : Colored n k) (ctx : Ctx n)
    (tcLevel current : Nat)
    (cs bs fs : List Nat) (st : SearchSt n) (best : Option (Key n))
    (trail : FrameTrail) : Prop where
  machines :
    (st.compCanon ≤ 0 ∧ CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon) ∨
    (st.compCanon < 0 ∧ CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon 0)
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g
    (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 1 st.autos
  workspace : WorkspaceOk st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) current st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel current st best trail
  trailOk : TrailOk ctx current st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  firstBound : st.gcaFirst ≤ current
  canonBound : st.gcaCanon ≤ current
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- A stable state is already a valid event state. -/
theorem RunInv.event {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best
      trail) (hnp : st.compCanon ≤ 0) :
    RunEvent G ctx tcLevel level cs bs fs st best trail :=
  ⟨Or.inl ⟨hnp, h.codeInv⟩, h.firstInv, h.canongInv,
    h.genTraceOk, h.autosOk, h.workspace, h.cheap, h.leafRefs, h.guides, h.trailOk,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- A nonpositive comparison sign remains nonpositive when `recover`
either leaves it alone or resets it to zero. -/
theorem recover_nonpositive {inf level : Nat} {st : SearchSt n}
    (h : st.compCanon ≤ 0) :
    (Nauty.recover n inf level st).compCanon ≤ 0 := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.compCanon, ite_self]
  repeat' split
  all_goals omega

/-- Applying `recover` to an event state restores the ordinary stable
invariant at the selected ancestor prefix. Search reachability and cell
stabilization are supplied by the surrounding loop, whose frozen frame
determines the recovered partition. -/
theorem RunEvent.recover {G : Colored n k} {ctx : Ctx n}
    {tcLevel current level inf numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hle : level ≤ current) (hlevel : 1 ≤ level) (hinf : level < inf)
    (hpath : level ≤ cs.length)
    (hfirst : st.gcaFirst ≤ level)
    (hok : SearchOk G level numcells (Nauty.recover n inf level st)) :
    RunInv G ctx tcLevel level (cs.take level) bs fs numcells
      (Nauty.recover n inf level st) best trail := by
  have hm := recover_machines
    (nn := n) (inf := inf) (cs := cs) (bs := bs)
    (fs := fs) (st := st) (lvl := level)
    (h.machines.elim Or.inl (fun hr => Or.inr hr.2)) h.firstInv hpath
  have hstore := recover_store n inf level st
  have hframes := recover_frames n inf level st
  have hnp : st.compCanon ≤ 0 := h.machines.elim (fun hl => hl.1)
    (fun hr => Int.le_of_lt hr.1)
  refine ⟨hok, hm.1, hm.2, canongInv_recover h.canongInv,
    genTraceOk_of_eq hstore.1 h.genTraceOk,
    autosOk_of_eq hstore.2 h.autosOk,
    h.workspace.ofFields (WorkspaceOk.recoverCap _ _ _ _) hstore.2,
    h.cheap.recover hle hlevel hinf, h.leafRefs.recover,
    h.guides.recover hle, h.trailOk.recover hle, ?_, ?_, ?_, ?_,
    h.bestCodes, ?_⟩
  · rw [hframes.2.2.2.2.2.2.1]
    exact h.firstPositive
  · rw [recover_gcaCanon]
    by_cases hc : level < st.gcaCanon
    · rw [ite_eq_left hc]
      omega
    · rw [ite_eq_right hc]
      exact h.canonPositive
  · rw [hframes.2.2.2.2.2.2.1]
    exact hfirst
  · rw [recover_gcaCanon]
    split <;> omega
  rw [hframes.1]
  exact h.incumbent

/-! # Leaf admission without a path-index mismatch -/

/-- Valid installed leaf references, a valid current search labelling, and
the row store are the exact hypotheses needed to preserve the generator
store through `processnode`. This avoids packaging the post-refinement
state in `DomOk`, whose path index intentionally describes a node before
its next refinement code is appended. -/
theorem LeafRefsOk.processnodeGen {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hgen : GenTraceOk ctx st) :
    GenTraceOk ctx (processnode ctx level numcells st).2 := by
  exact genTraceOk_processnode hgen hsymm hloop
    hrefs.firstSize
    (labOk_of_reach hrefs.firstSize hrefs.firstReach)
    (labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach)
    hok.labSize (labOk_of_reach hok.labSize hok.reach)
    (labInj_of_reach hok.labSize hn0 hok.reach)
    hrefs.canonSize
    (labOk_of_reach hrefs.canonSize hrefs.canonReach)
    (labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach)
    (fun htie => rows_eq_of_testcanlab_tie hcanong htie)

/-- The same correctly indexed leaf-state hypotheses identify any newly
admitted generator as a checked carrier from the first or canonical leaf. -/
theorem LeafRefsOk.processnodeCarrier {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
      LabelCarrier ctx st.firstlab st.lab
        (processnode ctx level numcells st).2.genTrace ∨
      LabelCarrier ctx st.canonlab st.lab
        (processnode ctx level numcells st).2.genTrace := by
  rcases processnode_carrier hsymm hloop hrefs.firstSize
      (labOk_of_reach hrefs.firstSize hrefs.firstReach)
      (labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach)
      hok.labSize (labOk_of_reach hok.labSize hok.reach)
      (labInj_of_reach hok.labSize hn0 hok.reach)
      hrefs.canonSize
      (labOk_of_reach hrefs.canonSize hrefs.canonReach)
      (labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach)
      (fun htie => rows_eq_of_testcanlab_tie hcanong htie) with
    hsame | ⟨γ, hpush, hcheck, hmap⟩
  · exact Or.inl hsame
  · have hmem : γ ∈ (processnode ctx level numcells st).2.genTrace := by
      rw [hpush]
      exact Array.mem_push.mpr (Or.inr rfl)
    rcases hmap with hfirst | hcanon
    · exact Or.inr (Or.inl ⟨γ, hmem, hcheck, hfirst⟩)
    · exact Or.inr (Or.inr ⟨γ, hmem, hcheck, hcanon⟩)

private theorem pushAuto_canonRef (st : SearchSt n) (p : VSet n × VSet n) :
    (pushAuto st p).canonlab = st.canonlab := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_canonLevel (st : SearchSt n) (p : VSet n × VSet n) :
    (pushAuto st p).canonlevel = st.canonlevel := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon' (st : SearchSt n) (p : VSet n × VSet n) :
    (pushAuto st p).gcaCanon = st.gcaCanon := by
  rw [pushAuto]
  split <;> rfl

private theorem ite_nonzero (p : Prop) [Decidable p] {a b : Nat}
    (ha : a ≠ 0) (hb : b ≠ 0) : (if p then a else b) ≠ 0 := by
  split <;> assumption

private theorem ite_or' {α : Type} {P : α → Prop} {c : Prop}
    [Decidable c] {a b : α} (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- `processnode` either retains the canonical reference or installs the
current reached labelling. -/
theorem processnode_canonRef (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∨
      (processnode ctx level numcells st).2.canonlab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.canonlab),
    pushAuto_canonRef]
  refine ite_or' (P := fun y => y = st.canonlab ∨ y = st.lab) ?_ ?_ <;>
    repeat' first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | apply ite_or' (P := fun y => y = st.canonlab ∨ y = st.lab)

/-- `processnode` either preserves the canonical guide and its reference,
or installs the current leaf with the guide parked at the current level. -/
theorem processnode_canonGuide (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    ((processnode ctx level numcells st).2.gcaCanon = st.gcaCanon ∧
      (processnode ctx level numcells st).2.canonlab = st.canonlab) ∨
    ((processnode ctx level numcells st).2.gcaCanon = level ∧
      (processnode ctx level numcells st).2.canonlab = st.lab) := by
  show (fun x : Int × SearchSt n =>
      (x.2.gcaCanon = st.gcaCanon ∧ x.2.canonlab = st.canonlab) ∨
        (x.2.gcaCanon = level ∧ x.2.canonlab = st.lab))
      (processnode ctx level numcells st)
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n =>
      (x.2.gcaCanon = st.gcaCanon ∧ x.2.canonlab = st.canonlab) ∨
        (x.2.gcaCanon = level ∧ x.2.canonlab = st.lab)),
    pushAuto_gcaCanon', pushAuto_canonRef, ite_self]
  simp

/-- Leaf-reference validity crosses every `processnode` outcome. -/
theorem LeafRefsOk.processnode {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (h : LeafRefsOk G st) (hok : SearchOk G level numcells st) :
    LeafRefsOk G (Nauty.processnode ctx level numcells st).2 := by
  obtain ⟨-, -, -, -, hfirst, -, -, -, -⟩ :=
    processnode_frames ctx level numcells st
  constructor
  · rw [hfirst]
    exact h.firstSize
  · rw [hfirst]
    exact h.firstReach
  · rcases processnode_canonRef ctx level numcells st with heq | heq
    · rw [heq]
      exact h.canonSize
    · rw [heq]
      exact hok.labSize
  · rcases processnode_canonRef ctx level numcells st with heq | heq
    · rw [heq]
      exact h.canonReach
    · rw [heq]
      exact hok.reach

/-- Once an incumbent exists, `processnode` either retains its positive
level or replaces it by the current positive level. -/
theorem processnode_installed {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (hlevel : 0 < level) (hold : st.canonlevel ≠ 0) :
    (processnode ctx level numcells st).2.canonlevel ≠ 0 := by
  have hnew : level ≠ 0 := Nat.ne_of_gt hlevel
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.canonlevel),
    pushAuto_canonLevel, ite_self]
  repeat' first
  | exact hold
  | exact hnew
  | apply ite_nonzero

end Hex.GraphIso.Nauty

/-!
Root-ledger preservation and leaf admission for the outcome-indexed search
induction.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Root-ledger entries -/

/-- A checked scatter between two reached labellings yields a valid
explicit autos-ledger entry at the initial coloured partition. -/
theorem pairOk_fmperm_of_reach {G : Colored n k} {ctx : Ctx n}
    {lab₁ lab₂ γ : Array Nat}
    (hn0 : 0 < n)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g γ = true) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmperm γ n).1 (fmperm γ n).2 := by
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmperm hroot.labOk hroot.labSize hroot.ptnSize
    hroot.ptnEnd hca
  exact cellStab_of_scatter hroot.ptnSize hroot.labSize hs₁
    hroot.ptnEnd hr₁ hr₂ hsc

/-- The finite array represented by a vertex renaming. -/
@[expose] def renamingArray (sigma : Renaming n) : Array Nat :=
  .ofFn fun i : Fin n => sigma i

theorem renamingArray_size (sigma : Renaming n) :
    (renamingArray sigma).size = n := by
  simp [renamingArray]

theorem renamingArray_get (sigma : Renaming n) {v : Nat} (hv : v < n) :
    (renamingArray sigma)[v]! = sigma v := by
  rw [getElem!_pos _ _ (by rw [renamingArray_size]; exact hv)]
  simp [renamingArray]

private theorem map_range_get (a : Array Nat) (hs : a.size = n) :
    (List.range n).map (fun i => a[i]!) = a.toList := by
  refine List.ext_getElem (by simp [hs]) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos a i (by simpa using h₂)]
  simp

/-- A row-preserving renaming passes the concrete automorphism checker. -/
theorem checkAutom_renaming {ctx : Ctx n} (sigma : Renaming n)
    (hrows : RowsMap sigma ctx.g ctx.g) :
    checkAutom ctx.g (renamingArray sigma) = true := by
  have hs := renamingArray_size sigma
  have hok : LabOk (renamingArray sigma) n := by
    intro i hi
    rw [hs] at hi
    rw [renamingArray_get sigma hi]
    exact (sigma.maps i).mp hi
  have hinj : LabInj (renamingArray sigma) n := by
    intro i j hi hj heq
    rw [renamingArray_get sigma hi, renamingArray_get sigma hj] at heq
    exact sigma.inj _ _ heq
  rw [checkAutom]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using hs, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun v hv => by
      have hvn := List.mem_range.mp hv
      simpa using hok v (by rw [hs]; exact hvn)
  · rw [List.isPerm_iff, map_range_get _ hs]
    exact labInj_perm_range hs hok hinj
  · refine List.all_eq_true.mpr fun v hv => ?_
    have hvn := List.mem_range.mp hv
    simp only [beq_iff_eq]
    rw [renamingArray_get sigma hvn, hrows.2.2 v hvn]
    exact image_congr _ fun w hw => (renamingArray_get sigma hw).symm

/-- At a small-cell node, every two members of a non-singleton cell have
equal semantic child subtrees.  This packages the geometric flip as the
concrete checked, cell-stabilizing array expected by `childKey_of_carried`.
-/
theorem childKey_eq_of_subtree {ctx : Ctx n} {st : RefineSt n}
    {tcLevel fuel level tc len numcells oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (hoU : oU < len) (hoV : oV < len)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oV =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells oU := by
  rcases Decidable.em (oU = oV) with rfl | hUV
  · rfl
  have hmem : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    mem_cells_of_isCell (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
      hS.it.ok.ptnEnd
      hcell (by omega) (by rw [hS.it.ok.ptnSize]; exact hrange)
  have hdiff : tc + len - 1 - tc = len - 1 := by omega
  obtain ⟨sigma, hrows, hperm, hmap⟩ :=
    flipData_of_subtreeOk (oU := oU) (oV := oV) hS hgsz hsymm hloop hmem
      (by omega) (by rw [hdiff]; omega) (by rw [hdiff]; omega) hUV
  let gamma := renamingArray sigma
  have hstab : CellStab st.ptn level st.lab gamma := by
    change cellsPerm st.ptn level st.lab
      (st.lab.map fun w => gamma[w]!)
    have hmapLab : st.lab.map (fun w => gamma[w]!) =
        st.lab.map sigma.toFun :=
      map_congr_of_labOk hS.it.ok.labOk fun w hw =>
        renamingArray_get sigma hw
    rw [hmapLab]
    exact hperm.cells
  apply childKey_of_carried hgsz (checkAutom_renaming sigma hrows)
    tcLevel fuel level hstab hS.it.ok.labSize hS.it.ok.labOk
    hS.it.ok.ptnSize hS.it.ok.ptnEnd (fun q => by
      rcases Decidable.em (q < n) with hq | hq
      · exact hS.it.vals q hq
      · left
        rw [getElem!_oob (by rw [hS.it.ok.ptnSize]; omega)]
        exact Nat.zero_le _)
    hcell hrange
    hoV hoU hfuel
  have hidxU : tc + oU < st.lab.size := by
    rw [hS.it.ok.labSize]
    omega
  rw [renamingArray_get sigma (hS.it.ok.labOk _ hidxU)]
  exact hmap.symm

/-- If refinement exposes a small-cell node, its unpruned maximum is the
subtree below any chosen member of the specification target cell.  The
target is non-singleton, and the flip theorem makes every entry in its
finite maximum equal. -/
theorem nodeKey_eq_child_of_subtree {ctx : Ctx n} {st : SearchSt n}
    {tcLevel fuel level numcells tc len o : Nat} {codes : List Nat}
    (hS : SubtreeOk ctx level
      (refine ctx level st.lab st.ptn st.active numcells))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hdisc : discreteAt
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level n = false)
    (hsize : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tcLevel).2.2 = len)
    (htc : (specMaketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tcLevel).1 = tc)
    (hcell : IsCell
      (refine ctx level st.lab st.ptn st.active numcells).ptn
      level tc len)
    (hlen : 2 ≤ len) (hrange : tc + len ≤ n) (ho : o < len)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    nodeKey ctx tcLevel (fuel + 1) level codes st numcells =
      sweepKey ctx tcLevel fuel level
        (codes ++ [(refine ctx level st.lab st.ptn st.active
          numcells).longcode])
        (refine ctx level st.lab st.ptn st.active numcells).lab
        (refine ctx level st.lab st.ptn st.active numcells).ptn tc
        (refine ctx level st.lab st.ptn st.active numcells).numcells o := by
  let r := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [r.longcode]
  let key := fun j => sweepKey ctx tcLevel fuel level full r.lab r.ptn tc
    r.numcells j
  have hkey : ∀ j, j < len → key j = key o := by
    intro j hj
    apply congrArg (prefixKey full)
    exact childKey_eq_of_subtree (tcLevel := tcLevel)
      (numcells := r.numcells) (oU := o) (oV := j) hS hgsz
      hsymm hloop hcell hlen hrange ho hj hfuel
  have hchildren : nodeKey ctx tcLevel (fuel + 1) level codes st numcells =
      keysMax (key 0) ((List.range (len - 1)).map fun j => key (j + 1)) := by
    have hlen' : len = len - 1 + 1 := by omega
    have htarget : (specMaketargetcell ctx r.lab r.ptn level
        tcLevel).2.2 = len - 1 + 1 := by
      simpa only [r] using hsize.trans hlen'
    have hn := nodeKey_children (ctx := ctx) (tcLevel := tcLevel)
      (fuel := fuel) (level := level) (numcells := numcells)
      (cs := codes) (st := st) hdisc htarget
    simpa only [r, full, key, htc] using hn
  rw [hchildren]
  apply keysMax_eq_of_le
  · rw [hkey 0 (by omega)]
    exact keyLe_refl _
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have hj' := List.mem_range.mp hj
    rw [hkey (j + 1) (by omega)]
    exact keyLe_refl _
  · rcases Nat.eq_zero_or_pos o with rfl | hop
    · exact Or.inl rfl
    · right
      apply List.mem_map.mpr
      exact ⟨o - 1, List.mem_range.mpr (by omega),
        congrArg key (by omega)⟩

/-- The implicit pair recorded at a small-cell node is valid at the root
partition.  Its missing vertices are realized by the node's flip
automorphisms, while singleton cells supply the fixed set. -/
theorem pairOk_fmptn_of_subtree {ctx : Ctx n} {G : Colored n k}
    {level : Nat} {r : RefineSt n}
    (hn0 : 0 < n) (hlevel : 1 <= level)
    (hgsz : ctx.g.size = n)
    (hsymm : forall u v, u < n -> v < n ->
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : forall v, v < n -> (ctx.g[v]!).mem v = false)
    (hS : SubtreeOk ctx level r)
    (hreach : CellsReach G r.lab)
    (hinit : forall q : Nat,
      (initPtn n (n + 2) (initialPartition G).2)[q]! <= 1 ->
        r.ptn[q]! <= 1) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn r.lab r.ptn level n).1
      (fmptn r.lab r.ptn level n).2 := by
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmptn
  · intro v hv
    obtain ⟨p, hp, hpv⟩ := labInj_surj
      (Nat.le_of_eq hS.it.ok.labSize.symm) hS.it.ok.labOk hS.it.inj v hv
    obtain ⟨c, hc, hp1, hp2⟩ := cells_cover p hp
    exact ⟨p, c.1, c.2, hc, hp1, hp2, hpv⟩
  · intro v c1 c2 hv hcell hp hq
    rcases hp with ⟨p, hp1, hp2, hpv⟩
    rcases hq with ⟨q, hq1, hq2, hqlt⟩
    have hoff : p - c1 ≠ q - c1 := by
      intro heq
      have : p = q := by omega
      subst q
      omega
    obtain ⟨sigma, hrows, hperm, hmap⟩ :=
      flipData_of_subtreeOk hS hgsz hsymm hloop hcell
        (by omega) (by omega) (by omega) hoff
    let gamma := renamingArray sigma
    refine ⟨gamma, checkAutom_renaming sigma hrows, ?_, ?_, ?_⟩
    · intro u hu hfix
      obtain ⟨c, hcellc, hcu⟩ := fmptn_fix hfix
      have hcb := cells_bound (Nat.le_of_eq hS.it.ok.ptnSize.symm)
        hS.it.ok.ptnEnd (c, c) hcellc
      have hc : c < r.lab.size := by
        rw [hS.it.ok.labSize, ← hS.it.ok.ptnSize]
        exact hcb
      have hic := cells_isCell
        (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
        hS.it.ok.ptnEnd (c, c) hcellc
      have heq := cellsPerm_singleton hperm.cells
        (show IsCell r.ptn level c 1 by simpa using hic)
      change r.lab[c]! = (r.lab.map sigma.toFun)[c]! at heq
      rw [getElem!_map_of_lt _ _ hc] at heq
      rw [renamingArray_get sigma hu]
      rw [← hcu]
      exact heq.symm
    · have hrootperm : cellsPerm
          (initPtn n (n + 2) (initialPartition G).2) 1
          r.lab (mapSt sigma r).lab := by
        apply cellsPerm_coarsen
            (ptnC := initPtn n (n + 2) (initialPartition G).2)
            (ptnF := r.ptn) (levC := 1) (levF := level)
        · rw [size_initPtn, hS.it.ok.ptnSize]
        · rw [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · simp [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · exact hperm.cells
        · exact hS.it.ok.ptnEnd
        · exact hroot.ptnEnd
        · intro x hx
          exact Nat.le_trans (hinit x hx) hlevel
      apply cellStab_of_scatter hroot.ptnSize hroot.labSize
        hS.it.ok.labSize hroot.ptnEnd hreach
        (cellsPerm_trans hreach hrootperm)
      intro i hi
      have hil : i < r.lab.size := by rw [hS.it.ok.labSize]; exact hi
      have hv' := hS.it.ok.labOk i hil
      rw [renamingArray_get sigma hv']
      exact (getElem!_map_of_lt sigma.toFun r.lab hil).symm
    · have hσ := hmap
      simp only [Nat.add_sub_of_le hp1, Nat.add_sub_of_le hq1] at hσ
      rw [renamingArray_get sigma hv, ← hpv, ← hσ]
      rw [hpv]
      exact hqlt

/-- A guard-passing refined node supplies the pair needed to carry the
cheap-boundary invariant into its children. -/
theorem CheapOk.nextOfSubtree {ctx : Ctx n} {G : Colored n k}
    {level : Nat} {st : SearchSt n} {r : RefineSt n}
    (h : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn n (n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1)
    (hlab : st.lab = r.lab) (hptn : st.ptn = r.ptn) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (level + 1) st := by
  apply h.next
  intro hncl
  rw [hncl, hlab, hptn]
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hsymm hloop hS
    hreach hinit

/-- Admitting a checked scatter between reached labellings preserves the
root automorphism ledger. -/
theorem AutosOk.pushFmperm {ctx : Ctx n} {G : Colored n k}
    {st : SearchSt n} {lab₁ lab₂ gamma : Array Nat}
    (hn0 : 0 < n)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → gamma[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g gamma = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (pushAuto st (fmperm gamma n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmperm_of_reach hn0 hs₁ hr₁ hr₂ hsc hca

/-- Recording the scan-free pair justified by a small-cell subtree
preserves the root automorphism ledger. -/
theorem AutosOk.pushFmptn {ctx : Ctx n} {G : Colored n k}
    {st : SearchSt n} {level : Nat} {r : RefineSt n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn n (n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (pushAuto st (fmptn r.lab r.ptn level n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hsymm hloop hS
    hreach hinit

/-- A successful code-one admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeAuto {ctx : Ctx n} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx
      (firstScatter n st.firstlab st.lab) = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  have hinj := labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach
  have hfirstOk := labOk_of_reach hrefs.firstSize hrefs.firstReach
  have hsc : ∀ i, i < n →
      (firstScatter n st.firstlab st.lab)[st.firstlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hfirstOk j (by rw [hrefs.firstSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (firstScatter n st.firstlab st.lab) = true := by
    apply checkAutom_scatter_of_isautom
      (firstScatter_size n st.firstlab st.lab)
      hrefs.firstSize
      (isPerm_of_cellsReach hrefs.firstSize hn0 hrefs.firstReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega)) hsymm hloop hpass
  rw [processnode_auto_autos heq hsent hnc hpass]
  exact hprev.pushFmperm hn0 hrefs.firstSize hrefs.firstReach
    hok.reach hsc hca

/-- A successful code-two admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeRowTie {ctx : Ctx n} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  have hcanonOk := labOk_of_reach hrefs.canonSize hrefs.canonReach
  have hinj := labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach
  have hsc : ∀ i, i < n →
      (canonScatter n st.canonlab st.lab)[st.canonlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    rw [canonScatter_eq_firstScatter]
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hcanonOk j (by rw [hrefs.canonSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (canonScatter n st.canonlab st.lab) = true := by
    apply checkAutom_scatter_of_leafRows_eq
      (by rw [canonScatter_eq_firstScatter]; exact
        firstScatter_size n st.canonlab st.lab)
      hrefs.canonSize
      (isPerm_of_cellsReach hrefs.canonSize hn0 hrefs.canonReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega))
      (rows_eq_of_testcanlab_tie hcanong htie)
  rw [processnode_rowTie_autos hef hnc hcc hge htie]
  exact hprev.pushFmperm hn0 hrefs.canonSize hrefs.canonReach
    hok.reach hsc hca

/-- The shared code-three/code-four tail preserves the ledger whenever
its optional implicit pair is valid. -/
theorem AutosOk.pruneAutos {ctx : Ctx n} {G : Colored n k}
    {level : Nat} {st : SearchSt n}
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 (pruneAutos level st) := by
  unfold Hex.GraphIso.Nauty.pruneAutos
  split
  · exact hprev
  · exact autosOk_pushAuto hprev (hpair (by assumption))

private theorem processnode_plain_autos {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hfast : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == n) = true)) :
    (processnode ctx level numcells st).2.autos = st.autos := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.autos)]
  simp [hfast, hnc]

/-- A leaf branch that leaves the pair array alone preserves its bounded
workspace. -/
private theorem WorkspaceOk.processSame {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} (h : WorkspaceOk st)
    (hautos : (processnode ctx level numcells st).2.autos = st.autos) :
    WorkspaceOk (processnode ctx level numcells st).2 := by
  apply h.ofFields
  · exact WorkspaceOk.processCap ctx level numcells st
  · exact hautos

/-- A leaf branch that records one pair preserves its bounded workspace. -/
private theorem WorkspaceOk.processPush {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} {pair : VSet n × VSet n}
    (h : WorkspaceOk st)
    (hautos : (processnode ctx level numcells st).2.autos =
      (pushAuto st pair).autos) :
    WorkspaceOk (processnode ctx level numcells st).2 := by
  apply (WorkspaceOk.push (pair := pair) h).ofFields
  · rw [WorkspaceOk.processCap, WorkspaceOk.pushCap]
  · exact hautos

/-- A successful first-path generator admission preserves the bounded
workspace. -/
theorem WorkspaceOk.processAuto {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} (h : WorkspaceOk st)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx
      (firstScatter n st.firstlab st.lab) = true) :
    WorkspaceOk (processnode ctx level numcells st).2 := by
  apply h.processPush
  exact processnode_auto_autos heq hsent hnc hpass

/-- The optional pair admission in the shared prune tail stays within the
configured workspace capacity. -/
private theorem WorkspaceOk.processPrune {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} (h : WorkspaceOk st)
    (hautos : (processnode ctx level numcells st).2.autos =
      pruneAutos level st) :
    WorkspaceOk (processnode ctx level numcells st).2 := by
  constructor
  · rw [WorkspaceOk.processCap]
    exact h.1
  · rw [hautos, WorkspaceOk.processCap]
    unfold pruneAutos
    split
    · exact h.2
    · simpa only [WorkspaceOk.pushCap] using (WorkspaceOk.push
        (pair := fmptn st.lab st.ptn st.noncheaplevel n) h).2

/-- Off the first path, every comparison-machine leaf branch preserves
the bounded workspace. -/
theorem WorkspaceOk.processOff {ctx : Ctx n}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt n}
    (h : WorkspaceOk st)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hef : ¬((st.eqlevFirst == level) = true)) :
    WorkspaceOk (processnode ctx level numcells st).2 := by
  have hef' : st.eqlevFirst ≠ level := fun he => hef (beq_iff_eq.mpr he)
  rcases hcode.tri with hzero | ⟨j, hj1, hjc, hjb, heqlev, hpre, hcase⟩
  · have hcc : st.compCanon = 0 := hzero.1
    rcases hnc : (numcells == n) with _ | _
    · apply h.processSame
      exact processnode_plain_autos (by rw [hcc]; omega) (by simp [hnc])
    · have hnc' : (numcells == n) = true := hnc
      rcases Decidable.em (level < st.canonlevel) with hlt | hge
      · apply h.processPrune
        exact processnode_shortInstall_autos hef hnc' hcc hlt
      · let row := (testcanlab ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        rcases Int.lt_trichotomy row 0 with hrow | hrow | hrow
        · apply h.processPrune
          exact processnode_rowReject_autos hef hnc' hcc hge hrow
        · apply h.processPush
          exact processnode_rowTie_autos hef hnc' hcc hge hrow
        · apply h.processPrune
          exact processnode_rowInstall_autos hef hnc' hcc hge hrow
  · rcases hcase with hdown | hup
    · have hcc : st.compCanon = -1 := hdown.1
      apply h.processPrune
      exact processnode_fast_autos ⟨hef', by rw [hcc]; omega⟩
    · have hcc : st.compCanon = 1 := hup.1
      rcases hnc : (numcells == n) with _ | _
      · apply h.processSame
        exact processnode_plain_autos (by rw [hcc]; omega) (by simp [hnc])
      · apply h.processPrune
        exact processnode_upInstall_autos hef hnc hcc

/-- On a non-discrete node admitted to its child sweep, `processnode`
performs no state update. -/
theorem processnode_internal {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hgate : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == n) = true)) :
    processnode ctx level numcells st = (Int.ofNat level, st) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  simp [hgate, hnc]

/-- Off the first path, `processnode` preserves the root ledger in every
comparison-machine outcome. -/
theorem AutosOk.processnodeOff {ctx : Ctx n} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2)
    (hef : ¬((st.eqlevFirst == level) = true)) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  have hef' : st.eqlevFirst ≠ level := fun he => hef (beq_iff_eq.mpr he)
  have hprune := hprev.pruneAutos hpair
  rcases hcode.tri with hzero | ⟨j, hj1, hjc, hjb, heqlev, hpre, hcase⟩
  · have hcc : st.compCanon = 0 := hzero.1
    rcases hnc : (numcells == n) with _ | _
    · rw [processnode_plain_autos (by rw [hcc]; omega)
          (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == n) = true := hnc
      rcases Decidable.em (level < st.canonlevel) with hlt | hge
      · rw [processnode_shortInstall_autos hef hnc' hcc hlt]
        exact hprune
      · let row := (testcanlab ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        rcases Int.lt_trichotomy row 0 with hrow | hrow | hrow
        · rw [processnode_rowReject_autos hef hnc' hcc hge hrow]
          exact hprune
        · exact hprev.processnodeRowTie hn0 hok hrefs hcanong
            hef hnc' hcc hge hrow
        · rw [processnode_rowInstall_autos hef hnc' hcc hge hrow]
          exact hprune
  · rcases hcase with hdown | hup
    · have hcc : st.compCanon = -1 := hdown.1
      rw [processnode_fast_autos ⟨hef', by rw [hcc]; omega⟩]
      exact hprune
    · have hcc : st.compCanon = 1 := hup.1
      rcases hnc : (numcells == n) with _ | _
      · rw [processnode_plain_autos (by rw [hcc]; omega)
            (by simp [hnc])]
        exact hprev
      · have hnc' : (numcells == n) = true := hnc
        rw [processnode_upInstall_autos hef hnc' hcc]
        exact hprune

/-- A failed first-path generator gate reduces to the ordinary off-path
ledger proof once canonical-labelling validity discharges the reused
workspace overwrite. -/
theorem AutosOk.processnodeGateFail {ctx : Ctx n} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2)
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == n) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter n st.firstlab st.lab) = false) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  let off := { st with eqlevFirst := level + 1 }
  have hoff : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells off).2.autos := by
    apply AutosOk.processnodeOff hn0 (st := off) (cs := cs)
      (bs := bs)
    · exact ⟨hok.labSize, hok.ptnSize, hok.reach, hok.init1, hok.vals,
        hok.count, hok.bc, hok.canon⟩
    · exact ⟨hrefs.firstSize, hrefs.firstReach, hrefs.canonSize,
        hrefs.canonReach⟩
    · change CanongInv ctx st.canong st.canonlab st.samerows
      exact hcanong
    · change CodeCmpInv n cs bs st.canoncode st.canonlevel
        st.eqlevCanon st.compCanon
      exact hcode
    · change AutosOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 st.autos
      exact hprev
    · change level ≠ st.noncheaplevel →
        PairOk ctx.g
          (initPtn n (n + 2) (initialPartition G).2)
          (initialPartition G).1 1
          (fmptn st.lab st.ptn st.noncheaplevel n).1
          (fmptn st.lab st.ptn st.noncheaplevel n).2
      exact hpair
    · simp [off]
  rw [processnode_gateFail_autos hrefs.canonSize
    (labOk_of_reach hrefs.canonSize hrefs.canonReach)
    (labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach)
    heq hnc hfail]
  exact hoff

/-- `processnode` preserves the root automorphism ledger in every leaf,
internal, generator, and comparison-prune outcome. -/
theorem AutosOk.processnode {ctx : Ctx n} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt n}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  rcases heq : (st.eqlevFirst == level) with _ | _
  · exact hprev.processnodeOff hn0 hok hrefs hcanong hcode
      hpair (by
        intro htrue
        rw [heq] at htrue
        exact Bool.noConfusion htrue)
  · rcases hnc : (numcells == n) with _ | _
    · rw [processnode_plain_autos
        (by intro h; exact h.1 (beq_iff_eq.mp heq)) (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == n) = true := hnc
      rcases hsent : (st.firstcode[level + 1]! == codeSentinel) with _ | _
      · apply hprev.processnodeGateFail hn0 hok hrefs hcanong hcode
          hpair heq hnc'
        exact Or.inl (by simpa only [beq_eq_false_iff_ne] using hsent)
      · have hsent' : st.firstcode[level + 1]! = codeSentinel :=
          beq_iff_eq.mp hsent
        rcases hpass : isautom ctx
            (firstScatter n st.firstlab st.lab) with _ | _
        · apply hprev.processnodeGateFail hn0 hok hrefs hcanong
            hcode hpair heq hnc'
          exact Or.inr hpass
        · exact hprev.processnodeAuto hn0 hsymm hloop hok hrefs
            heq hsent' hnc' hpass

/-- The stable search invariant now discharges the last independent
ledger premise of `processnode`: the runtime bound selects the frozen
pair carried by `CheapOk`. -/
theorem RunInv.processnodeAutos {ctx : Ctx n} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn0 hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- The prepared state also discharges the root-ledger premise of a leaf
event; unlike `RunInv`, it permits the positive comparison sign produced
by the immediately preceding code comparison. -/
theorem RunPrep.processnodeAutos {ctx : Ctx n} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn0 hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- An ordinary off-first-path discrete leaf turns the prepared state
into an event state whose incumbent is exactly the maximum of the old
incumbent and that leaf.  The return disjunction is retained for the
node outcome split. -/
theorem RunPrep.leaf {ctx : Ctx n} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail) :
    ∃ bs' : List Nat,
      RunEvent G ctx tcLevel level cs bs' fs
        (processnode ctx level numcells st).2
        (some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab)) trail ∧
      incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab) (pathLeafKey ctx cs st.lab) ∧
      ((processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∨
        (processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  subst level
  have hcsn : cs.length ≤ n := by
    have hb := bcount_le st.ptn cs.length n
    have hc := h.searchOk.bc
    omega
  obtain ⟨bs', hmax, hcanong, hmachines, hreturn⟩ :=
    processnode_leaf h.codeInv h.canongInv hcsn hef hnc
  have hcs : cs ≠ [] := by
    intro he
    subst cs
    simp at hlevel
  have hbs' : bs' ≠ [] :=
    incKey_max_nonempty h.bestCodes hcs hmax
  have hinc : IncGrows best
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) := by
    intro b hb
    rw [h.incumbent] at hb
    injection hb with hb
    subst b
    refine ⟨incKey ctx bs'
      (processnode ctx cs.length numcells st).2.canonlab, rfl, ?_⟩
    rw [hmax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  obtain ⟨hlab, hptn, heqFirst, hfirstCode, hfirstlab, -, hgcaFirst,
      -, -⟩ := processnode_frames ctx cs.length numcells st
  have hguides : GuideStore ctx tcLevel cs.length
      (processnode ctx cs.length numcells st).2
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) trail := by
    apply h.guides.processnode hinc hgcaFirst hfirstlab
    intro hlt
    rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · exact hold
    · rw [hnew.1] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn0 hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn0 hsymm hloop hbound
  · exact h.workspace.processOff h.codeInv hef
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew.1]
      exact hlevel
  · rw [hgcaFirst]
    exact h.firstBound
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonBound
    · rw [hnew.1]
      exact Nat.le_refl _

/-- A first-path-agreeing leaf whose generator admission guard fails has
the same exact event invariant as an ordinary compared leaf. -/
theorem RunPrep.leafFirst {ctx : Ctx n} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (heq : (st.eqlevFirst == level) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter n st.firstlab st.lab) = false)
    (hnc : (numcells == n) = true)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail) :
    ∃ bs' : List Nat,
      RunEvent G ctx tcLevel level cs bs' fs
        (processnode ctx level numcells st).2
        (some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab)) trail ∧
      incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
        keyMax (incKey ctx bs st.canonlab) (pathLeafKey ctx cs st.lab) ∧
      ((processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∨
        (processnode ctx level numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx level numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  subst level
  have hcsn : cs.length ≤ n := by
    have hb := bcount_le st.ptn cs.length n
    have hc := h.searchOk.bc
    omega
  obtain ⟨bs', hmax, hcanong, hmachines, hreturn⟩ :=
    processnode_leafFirst h.codeInv h.canongInv hcsn heq hnc hfail
  have hcs : cs ≠ [] := by
    intro he
    subst cs
    simp at hlevel
  have hbs' : bs' ≠ [] :=
    incKey_max_nonempty h.bestCodes hcs hmax
  have hinc : IncGrows best
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) := by
    intro b hb
    rw [h.incumbent] at hb
    injection hb with hb
    subst b
    refine ⟨incKey ctx bs'
      (processnode ctx cs.length numcells st).2.canonlab, rfl, ?_⟩
    rw [hmax]
    exact keyLe_iff.mpr (keyMax_not_lt_left _ _)
  obtain ⟨-, -, heqFirst, hfirstCode, hfirstlab, -, hgcaFirst,
      -, -⟩ := processnode_frames ctx cs.length numcells st
  have hguides : GuideStore ctx tcLevel cs.length
      (processnode ctx cs.length numcells st).2
      (some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab)) trail := by
    apply h.guides.processnode hinc hgcaFirst hfirstlab
    intro hlt
    rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · exact hold
    · rw [hnew.1] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn0 hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn0 hsymm hloop hbound
  · let off : SearchSt n := { st with eqlevFirst := cs.length + 1 }
    have hoff : WorkspaceOk off := h.workspace.ofFields rfl rfl
    have hcodeOff : CodeCmpInv n cs bs off.canoncode off.canonlevel
        off.eqlevCanon off.compCanon := by
      simpa only [off] using h.codeInv
    have hw : WorkspaceOk
        (processnode ctx cs.length numcells off).2 := by
      apply hoff.processOff hcodeOff
      simp [off]
    apply hw.ofFields
    · rw [WorkspaceOk.processCap, WorkspaceOk.processCap]
    · have hcanonSize : st.canonlab.size = n := by
        exact h.leafRefs.canonSize
      have hcanonOk : LabOk st.canonlab n := by
        exact labOk_of_reach h.leafRefs.canonSize h.leafRefs.canonReach
      have hcanonInj : LabInj st.canonlab n := by
        exact labInj_of_reach h.leafRefs.canonSize hn0
          h.leafRefs.canonReach
      exact processnode_gateFail_autos hcanonSize
        hcanonOk hcanonInj heq hnc hfail
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew.1]
      exact hlevel
  · rw [hgcaFirst]
    exact h.firstBound
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonBound
    · rw [hnew.1]
      exact Nat.le_refl _

end Hex.GraphIso.Nauty
