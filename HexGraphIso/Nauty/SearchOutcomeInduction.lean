/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeTrail
public import HexGraphIso.Nauty.QuartetNode
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.SmallCellTie

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

/-! # Cheap-automorphism ledger boundary -/

/-- The implicit automorphism pair remains valid while search stays
strictly below the level at which that pair was frozen.  At the frozen
level itself the implication is deliberately dormant: `processnode` does
not insert an implicit pair there, and a failed cheap-automorphism guard
will move the boundary before the next descent. -/
structure CheapOk (ctx : Ctx) (rlab rptn : Array Nat) (level : Nat)
    (st : SearchSt) : Prop where
  positive : 0 < st.noncheaplevel
  labSize : st.lab.size = ctx.n
  ptnSize : st.ptn.size = ctx.n
  rootEnd : st.ptn[st.ptn.size - 1]! ≤ 1
  pair : st.noncheaplevel < level →
    PairOk ctx.g rptn rlab 1 ctx.n
      (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
      (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2

/-- At a node entry, the runtime bound turns the strict-boundary ledger
invariant into the premise consumed by `processnode`. -/
theorem CheapOk.ready {ctx : Ctx} {rlab rptn : Array Nat} {level : Nat}
    {st : SearchSt} (h : CheapOk ctx rlab rptn level st)
    (hbound : st.noncheaplevel ≤ level) (hne : level ≠ st.noncheaplevel) :
    PairOk ctx.g rptn rlab 1 ctx.n
      (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
      (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2 :=
  h.pair (by omega)

/-- The cheap-boundary invariant depends only on the current labelling,
partition, and boundary level. -/
theorem CheapOk.ofFrames {ctx : Ctx} {rlab rptn : Array Nat}
    {level : Nat} {st out : SearchSt}
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
theorem recover_fmptn {st : SearchSt} {n inf level saved : Nat}
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
theorem CheapOk.recover {ctx : Ctx} {rlab rptn : Array Nat}
    {current level inf : Nat} {st : SearchSt}
    (h : CheapOk ctx rlab rptn current st) (hle : level ≤ current)
    (hlevel : 1 ≤ level) (hinf : level < inf) :
    CheapOk ctx rlab rptn level (Nauty.recover ctx.n inf level st) := by
  have hncl : (Nauty.recover ctx.n inf level st).noncheaplevel =
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
        (st.ptn.size - 1 < ctx.n ∧
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
    · have heq : (Nauty.recover ctx.n inf level st).noncheaplevel =
          st.noncheaplevel := by rw [hncl, ite_eq_right hc]
      rw [heq] at hlt ⊢
      have hpos := h.positive
      rw [recover_fmptn (Nat.le_of_eq h.ptnSize.symm)
        (Nat.le_trans h.rootEnd (by omega : 1 ≤ st.noncheaplevel))
        (by omega : st.noncheaplevel ≤ level) hinf]
      exact h.pair (by omega)

/-- Leaf processing does not move the frozen pair's defining fields. -/
theorem CheapOk.processnode {ctx : Ctx} {rlab rptn : Array Nat}
    {level numcells : Nat} {st : SearchSt}
    (h : CheapOk ctx rlab rptn level st) :
    CheapOk ctx rlab rptn level (processnode ctx level numcells st).2 := by
  obtain ⟨hlab, hptn, -, -, -, -, -, hncl, -⟩ :=
    processnode_frames ctx level numcells st
  exact h.ofFrames hlab hptn hncl

/-- Installing the first leaf does not move the frozen pair's defining
fields. -/
theorem CheapOk.firstterminal {ctx : Ctx} {rlab rptn : Array Nat}
    {level : Nat} {st : SearchSt}
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
theorem CheapOk.otherNodePrep {ctx : Ctx} {rlab rptn : Array Nat}
    {level code : Nat} {st : SearchSt}
    (h : CheapOk ctx rlab rptn level st) :
    CheapOk ctx rlab rptn level (Nauty.otherNodePrep level code st) := by
  obtain ⟨-, -, -, -, -, -, -, -, hncl, -, -, hlab, hptn⟩ :=
    otherNodePrep_frames level code st
  exact h.ofFrames hlab hptn hncl

/-- Writing a boundary at or above the logical level suspends the pair
obligation without changing the partition facts needed to revive it. -/
theorem CheapOk.park {ctx : Ctx} {rlab rptn : Array Nat}
    {old current boundary : Nat} {st : SearchSt}
    (h : CheapOk ctx rlab rptn old st) (hpos : 0 < boundary)
    (hcurrent : current ≤ boundary) :
    CheapOk ctx rlab rptn current
      { st with noncheaplevel := boundary } := by
  refine ⟨hpos, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  simp only
  omega

/-- A valid pair at the current boundary extends the invariant through
the next logical level. -/
theorem CheapOk.next {ctx : Ctx} {rlab rptn : Array Nat}
    {level : Nat} {st : SearchSt}
    (h : CheapOk ctx rlab rptn level st)
    (hpair : st.noncheaplevel = level →
      PairOk ctx.g rptn rlab 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2) :
    CheapOk ctx rlab rptn (level + 1) st := by
  refine ⟨h.positive, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  intro hlt
  rcases Decidable.em (st.noncheaplevel = level) with heq | hne
  · exact hpair heq
  · exact h.pair (by omega)

/-- Refinement only splits at the current level and permutes within the
old current cells, so every pair frozen at a strictly smaller level is
unchanged. -/
theorem CheapOk.refine {ctx : Ctx} {rlab rptn : Array Nat}
    {level numcells : Nat} {st out : SearchSt}
    (h : CheapOk ctx rlab rptn level st) (hlevel : 1 ≤ level)
    (hlab : out.lab =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).lab)
    (hptn : out.ptn =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn level out := by
  let rs := Nauty.refine ctx level st.lab st.ptn st.active numcells
  have hnnEq : ctx.n = st.ptn.size := h.ptnSize.symm
  have hnn : ctx.n ≤ st.ptn.size := Nat.le_of_eq hnnEq
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
    have hcells : cells st.ptn st.noncheaplevel ctx.n =
        cells rs.ptn st.noncheaplevel ctx.n := by
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
    have hfm : fmptn st.lab st.ptn st.noncheaplevel ctx.n =
        fmptn rs.lab rs.ptn st.noncheaplevel ctx.n :=
      fmptn_congr hnn hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- Individualizing inside a current cell does not change the implicit
pair frozen at an older cheap boundary. -/
theorem CheapOk.breakout {ctx : Ctx} {rlab rptn : Array Nat}
    {level tc len o : Nat} {st out : SearchSt}
    (h : CheapOk ctx rlab rptn (level + 1) st)
    (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n) (ho : o < len)
    (hlab : out.lab =
      (Nauty.breakout st.lab st.ptn (level + 1) tc
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
    have hcells : cells st.ptn st.noncheaplevel ctx.n =
        cells (st.ptn.set! tc (level + 1)) st.noncheaplevel ctx.n := by
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
        (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
          (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact hls
      · rw [breakout_lab_size]
        exact hls
      · exact breakout_cellsPerm hcell (by rw [h.ptnSize]; exact hrange)
          hls ho
      · exact hend
      · exact hendSaved
      · intro q hq
        exact Nat.le_trans hq hsaved
    have hfm : fmptn st.lab st.ptn st.noncheaplevel ctx.n =
        fmptn (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 (st.ptn.set! tc (level + 1))
          st.noncheaplevel ctx.n :=
      fmptn_congr (Nat.le_of_eq h.ptnSize.symm) hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- The initial search boundary is one, so its strict pair obligation is
empty at the root. -/
theorem CheapOk.root {G : Colored n k} {ctx : Ctx} {numcells : Nat}
    {st : SearchSt} (hn : ctx.n = n) (hn0 : 0 < n)
    (hok : SearchOk G 1 numcells st) (hncl : st.noncheaplevel = 1) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) 1 st := by
  refine ⟨by rw [hncl]; exact Nat.zero_lt_succ 0, ?_, ?_,
    searchOk_end hn0 hok (Nat.le_refl 1), ?_⟩
  · rw [hok.labSize, hn]
  · rw [hok.ptnSize, hn]
  · intro hlt
    rw [hncl] at hlt
    omega

/-! # Stable post-install state -/

/-- The semantic state available after the first leaf has been installed.

The explicit `level` makes the package usable both at node entries and
inside their child loops. At a node entry, `level = cs.length + 1`
recovers `DomOk`; a loop instead carries the code path through its current
node, so its path has length `level`. -/
structure RunInv (G : Colored n k) (ctx : Ctx)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g
    (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 1 ctx.n st.autos
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel level st best trail
  trailOk : TrailOk ctx level st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  nonpositive : st.compCanon ≤ 0
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- At a node boundary the stable package supplies the existing `DomOk`
record consumed by the leaf-event theorems. -/
theorem RunInv.dom {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
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
theorem RunInv.read {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best
      trail) : stInc ctx st = best := by
  have hne : st.compCanon ≠ 1 := by
    intro heq
    have hnp := h.nonpositive
    rw [heq] at hnp
    omega
  rw [stInc_eq_ghost h.codeInv hne, ghostInc]
  simp only [h.bestCodes, ↓reduceIte, h.incumbent]

/-! # Post-refinement comparison state -/

/-- The semantic state after refinement and `otherNodePrep`, before
`processnode` restores the stable comparison sign.  This differs from
`RunInv` only in omitting `compCanon ≤ 0`: comparing the freshly appended
refinement code may set the sign to one. -/
structure RunPrep (G : Colored n k) (ctx : Ctx)
    (tcLevel level : Nat) (cs bs fs : List Nat) (numcells : Nat)
    (st : SearchSt) (best : Option Key) (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codeInv : CodeCmpInv n cs bs st.canoncode st.canonlevel
    st.eqlevCanon st.compCanon
  firstInv : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  canongInv : CanongInv ctx st.canong st.canonlab st.samerows
  genTraceOk : GenTraceOk ctx st
  autosOk : AutosOk ctx.g
    (initPtn n (n + 2) (initialPartition G).2)
    (initialPartition G).1 1 ctx.n st.autos
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel level st best trail
  trailOk : TrailOk ctx level st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- Refinement followed by the off-path comparison step enters
`RunPrep`.  Generator validity is global, while stabilization is proved
only at the loop frame where a generator is consumed. -/
theorem RunInv.otherLeaf {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hpath : level = cs.length + 1)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail) :
    RunPrep G ctx tcLevel level
      (cs ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs fs
      (refine ctx level st.lab st.ptn st.active numcells).numcells
      (otherLeafSt ctx level numcells st) best trail := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt :=
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
    refine_searchOk hn hn0 h.searchOk hlevel hlab hptn (Or.inl hcanon)
  have htrail : TrailOk ctx level (otherLeafSt ctx level numcells st)
      trail := by
    apply h.trailOk.refine
    · rw [h.searchOk.labSize, ← hn]
    · rw [h.searchOk.ptnSize, ← hn]
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
        numcells), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.bestCodes, ?_⟩
  · have hb := bcount_le st.ptn (cs.length + 1) n
    have hc := h.searchOk.bc
    omega
  · rw [hout]
    exact canongInv_otherNodePrep h.canongInv
  · exact genTraceOk_of_eq hgen h.genTraceOk
  · exact autosOk_of_eq hautos h.autosOk
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
  · rw [hcanon]
    exact h.incumbent

/-! # First-leaf phase transition -/

/-- The state fields needed to enter the stable induction immediately
after `firstterminal`. -/
theorem firstterminal_state (level : Nat) (st : SearchSt) :
    (firstterminal level st).lab = st.lab ∧
    (firstterminal level st).ptn = st.ptn ∧
    (firstterminal level st).gcaFirst = level ∧
    (firstterminal level st).gcaCanon = level ∧
    (firstterminal level st).compCanon = 0 := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  simp

/-- Installing the first leaf preserves the search skeleton and records a
reached canonical labelling. -/
theorem SearchOk.firstterminal {G : Colored n k} {level numcells : Nat}
    {st : SearchSt} (h : SearchOk G level numcells st) :
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
theorem RunInv.firstterminal {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hpath : level = cs.length) (hok : SearchOk G level numcells st)
    (hfirstSize : st.firstcode.size = n + 2)
    (hcanonSize : st.canoncode.size = n + 2)
    (hbound : cs.length ≤ n)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel)
    (hcanong : st.canong.size = ctx.n)
    (hgen : st.genTrace = #[]) (hautos : st.autos = #[])
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
    hcheap.firstterminal, LeafRefsOk.firstterminal hok, ?_, ?_, ?_, ?_,
    ?_, hne, ?_⟩
  · unfold GenTraceOk
    intro γ hγ
    rw [hstore.1, hgen] at hγ
    simp at hγ
  · intro p hp
    rw [hstore.2, hautos] at hp
    simp at hp
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
  · rw [hstate.2.2.2.2]
    exact Int.le_refl 0
  · rw [firstterminal_canonlab]
    rfl

/-! # Unwind framing -/

/-- `recover` clamps the canonical guide target to the receiving level. -/
theorem recover_gcaCanon (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).gcaCanon =
      if level < st.gcaCanon then level else st.gcaCanon := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.gcaCanon, ite_self]
  repeat' split
  all_goals rfl

/-- Recovering a parent frame preserves both installed leaf references. -/
theorem LeafRefsOk.recover {G : Colored n k} {n inf level : Nat}
    {st : SearchSt} (h : LeafRefsOk G st) :
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
theorem GuideStore.recover {ctx : Ctx} {tcLevel current : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    {n inf level : Nat}
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
theorem GuideStore.processnode {ctx : Ctx} {tcLevel level : Nat}
    {st out : SearchSt} {before best : Option Key} {trail : FrameTrail}
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
structure RunEvent (G : Colored n k) (ctx : Ctx)
    (tcLevel current : Nat)
    (cs bs fs : List Nat) (st : SearchSt) (best : Option Key)
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
    (initialPartition G).1 1 ctx.n st.autos
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) current st
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel current st best trail
  trailOk : TrailOk ctx current st trail
  firstPositive : 0 < st.gcaFirst
  canonPositive : 0 < st.gcaCanon
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- A stable state is already a valid event state. -/
theorem RunInv.event {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best
      trail) :
    RunEvent G ctx tcLevel level cs bs fs st best trail :=
  ⟨Or.inl ⟨h.nonpositive, h.codeInv⟩, h.firstInv, h.canongInv,
    h.genTraceOk, h.autosOk, h.cheap, h.leafRefs, h.guides, h.trailOk,
    h.firstPositive, h.canonPositive, h.bestCodes, h.incumbent⟩

/-- A nonpositive comparison sign remains nonpositive when `recover`
either leaves it alone or resets it to zero. -/
theorem recover_nonpositive {n inf level : Nat} {st : SearchSt}
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
theorem RunEvent.recover {G : Colored n k} {ctx : Ctx}
    {tcLevel current level inf numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hle : level ≤ current) (hlevel : 1 ≤ level) (hinf : level < inf)
    (hpath : level ≤ cs.length)
    (hok : SearchOk G level numcells (Nauty.recover ctx.n inf level st)) :
    RunInv G ctx tcLevel level (cs.take level) bs fs numcells
      (Nauty.recover ctx.n inf level st) best trail := by
  have hm := recover_machines
    (nn := n) (N := ctx.n) (inf := inf) (cs := cs) (bs := bs)
    (fs := fs) (st := st) (lvl := level)
    (h.machines.elim Or.inl (fun hr => Or.inr hr.2)) h.firstInv hpath
  have hstore := recover_store ctx.n inf level st
  have hframes := recover_frames ctx.n inf level st
  have hnp : st.compCanon ≤ 0 := h.machines.elim (fun hl => hl.1)
    (fun hr => Int.le_of_lt hr.1)
  refine ⟨hok, hm.1, hm.2, canongInv_recover h.canongInv,
    genTraceOk_of_eq hstore.1 h.genTraceOk,
    autosOk_of_eq hstore.2 h.autosOk,
    h.cheap.recover hle hlevel hinf, h.leafRefs.recover,
    h.guides.recover hle, h.trailOk.recover hle, ?_, ?_,
    recover_nonpositive hnp, h.bestCodes, ?_⟩
  · rw [hframes.2.2.2.2.2.2.1]
    exact h.firstPositive
  · rw [recover_gcaCanon]
    by_cases hc : level < st.gcaCanon
    · rw [if_pos hc]
      omega
    · rw [if_neg hc]
      exact h.canonPositive
  rw [hframes.1]
  exact h.incumbent

/-! # Leaf admission without a path-index mismatch -/

/-- Valid installed leaf references, a valid current search labelling, and
the row store are the exact hypotheses needed to preserve the generator
store through `processnode`. This avoids packaging the post-refinement
state in `DomOk`, whose path index intentionally describes a node before
its next refinement code is appended. -/
theorem LeafRefsOk.processnodeGen {G : Colored n k} {ctx : Ctx}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hgen : GenTraceOk ctx st) :
    GenTraceOk ctx (processnode ctx level numcells st).2 := by
  subst n
  exact genTraceOk_processnode hgen hgb hsymm hloop
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
theorem LeafRefsOk.processnodeCarrier {G : Colored n k} {ctx : Ctx}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
      LabelCarrier ctx st.firstlab st.lab
        (processnode ctx level numcells st).2.genTrace ∨
      LabelCarrier ctx st.canonlab st.lab
        (processnode ctx level numcells st).2.genTrace := by
  subst n
  rcases processnode_carrier hgb hsymm hloop hrefs.firstSize
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

private theorem pushAuto_canonRef (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canonlab = st.canonlab := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_canonLevel (st : SearchSt) (p : Nat × Nat) :
    (pushAuto st p).canonlevel = st.canonlevel := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_gcaCanon' (st : SearchSt) (p : Nat × Nat) :
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
theorem processnode_canonRef (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∨
      (processnode ctx level numcells st).2.canonlab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.canonlab),
    pushAuto_canonRef]
  refine ite_or' (P := fun y => y = st.canonlab ∨ y = st.lab) ?_ ?_ <;>
    repeat' first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | apply ite_or' (P := fun y => y = st.canonlab ∨ y = st.lab)

/-- `processnode` either preserves the canonical guide and its reference,
or installs the current leaf with the guide parked at the current level. -/
theorem processnode_canonGuide (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    ((processnode ctx level numcells st).2.gcaCanon = st.gcaCanon ∧
      (processnode ctx level numcells st).2.canonlab = st.canonlab) ∨
    (processnode ctx level numcells st).2.gcaCanon = level := by
  show (fun x : Int × SearchSt =>
      (x.2.gcaCanon = st.gcaCanon ∧ x.2.canonlab = st.canonlab) ∨
        x.2.gcaCanon = level) (processnode ctx level numcells st)
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt =>
      (x.2.gcaCanon = st.gcaCanon ∧ x.2.canonlab = st.canonlab) ∨
        x.2.gcaCanon = level),
    pushAuto_gcaCanon', pushAuto_canonRef, ite_self]
  simp

/-- Leaf-reference validity crosses every `processnode` outcome. -/
theorem LeafRefsOk.processnode {G : Colored n k} {ctx : Ctx}
    {level numcells : Nat} {st : SearchSt}
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
theorem processnode_installed {ctx : Ctx} {level numcells : Nat}
    {st : SearchSt} (hlevel : 0 < level) (hold : st.canonlevel ≠ 0) :
    (processnode ctx level numcells st).2.canonlevel ≠ 0 := by
  have hnew : level ≠ 0 := Nat.ne_of_gt hlevel
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.canonlevel),
    pushAuto_canonLevel, ite_self]
  repeat' first
  | exact hold
  | exact hnew
  | apply ite_nonzero

/-! # Root-ledger entries -/

/-- A checked scatter between two reached labellings yields a valid
explicit autos-ledger entry at the initial coloured partition. -/
theorem pairOk_fmperm_of_reach {G : Colored n k} {ctx : Ctx}
    {lab₁ lab₂ γ : Array Nat}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hs₂ : lab₂.size = n) (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g γ ctx.n = true) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmperm γ ctx.n).1 (fmperm γ ctx.n).2 := by
  subst hn
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmperm hbg hroot.labOk hroot.labSize hroot.ptnSize
    hroot.ptnEnd hca
  exact cellStab_of_scatter hroot.ptnSize hroot.labSize hs₁
    hroot.ptnEnd hr₁ hr₂ hsc

/-- The finite array represented by a vertex renaming. -/
@[expose] def renamingArray (n : Nat) (sigma : Renaming n) : Array Nat :=
  .ofFn fun i : Fin n => sigma i

theorem renamingArray_size (sigma : Renaming n) :
    (renamingArray n sigma).size = n := by
  simp [renamingArray]

theorem renamingArray_get (sigma : Renaming n) {v : Nat} (hv : v < n) :
    (renamingArray n sigma)[v]! = sigma v := by
  rw [getElem!_pos _ _ (by rw [renamingArray_size]; exact hv)]
  simp [renamingArray]

private theorem map_range_get (a : Array Nat) (hs : a.size = n) :
    (List.range n).map (fun i => a[i]!) = a.toList := by
  refine List.ext_getElem (by simp [hs]) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos a i (by simpa using h₂)]
  simp

/-- A row-preserving renaming passes the concrete automorphism checker. -/
theorem checkAutom_renaming {ctx : Ctx} (sigma : Renaming ctx.n)
    (hrows : RowsMap sigma ctx.g ctx.g) :
    checkAutom ctx.g (renamingArray ctx.n sigma) ctx.n = true := by
  have hs := renamingArray_size sigma
  have hok : LabOk (renamingArray ctx.n sigma) ctx.n := by
    intro i hi
    rw [hs] at hi
    rw [renamingArray_get sigma hi]
    exact (sigma.maps i).mp hi
  have hinj : LabInj (renamingArray ctx.n sigma) ctx.n := by
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

/-- The implicit pair recorded at a small-cell node is valid at the root
partition.  Its missing vertices are realized by the node's flip
automorphisms, while singleton cells supply the fixed set. -/
theorem pairOk_fmptn_of_subtree {ctx : Ctx} {G : Colored ctx.n k}
    {level : Nat} {r : RefineSt}
    (hn0 : 0 < ctx.n) (hlevel : 1 <= level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : forall v, v < ctx.n -> ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : forall u v, u < ctx.n -> v < ctx.n ->
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : forall v, v < ctx.n -> (ctx.g[v]!).testBit v = false)
    (hS : SubtreeOk ctx level r)
    (hreach : CellsReach G r.lab)
    (hinit : forall q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! <= 1 ->
        r.ptn[q]! <= 1) :
    PairOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (fmptn r.lab r.ptn level ctx.n).1
      (fmptn r.lab r.ptn level ctx.n).2 := by
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
      flipData_of_subtreeOk hS hgsz hgb hsymm hloop hcell
        (by omega) (by omega) (by omega) hoff
    let gamma := renamingArray ctx.n sigma
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
          (initPtn ctx.n (ctx.n + 2) (initialPartition G).2) 1
          r.lab (mapSt sigma r).lab := by
        apply cellsPerm_coarsen
            (ptnC := initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
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
theorem CheapOk.nextOfSubtree {ctx : Ctx} {G : Colored ctx.n k}
    {level : Nat} {st : SearchSt} {r : RefineSt}
    (h : CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2) level st)
    (hn0 : 0 < ctx.n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1)
    (hlab : st.lab = r.lab) (hptn : st.ptn = r.ptn) :
    CheapOk ctx (initialPartition G).1
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (level + 1) st := by
  apply h.next
  intro hncl
  rw [hncl, hlab, hptn]
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hgb hsymm hloop hS
    hreach hinit

/-- Admitting a checked scatter between reached labellings preserves the
root automorphism ledger. -/
theorem AutosOk.pushFmperm {ctx : Ctx} {G : Colored n k}
    {st : SearchSt} {lab₁ lab₂ gamma : Array Nat}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hs₂ : lab₂.size = n) (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → gamma[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g gamma ctx.n = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (pushAuto st (fmperm gamma ctx.n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmperm_of_reach hn hn0 hgb hs₁ hr₁ hs₂ hr₂ hsc hca

/-- Recording the scan-free pair justified by a small-cell subtree
preserves the root automorphism ledger. -/
theorem AutosOk.pushFmptn {ctx : Ctx} {G : Colored ctx.n k}
    {st : SearchSt} {level : Nat} {r : RefineSt}
    (hn0 : 0 < ctx.n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hprev : AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hS : SubtreeOk ctx level r) (hreach : CellsReach G r.lab)
    (hinit : ∀ q : Nat,
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ 1) :
    AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (pushAuto st (fmptn r.lab r.ptn level ctx.n)).autos := by
  apply autosOk_pushAuto hprev
  exact pairOk_fmptn_of_subtree hn0 hlevel hgsz hgb hsymm hloop hS
    hreach hinit

/-- A successful code-one admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeAuto {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx
      (firstScatter ctx.n st.firstlab st.lab) = true) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  have hinj := labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach
  have hfirstOk := labOk_of_reach hrefs.firstSize hrefs.firstReach
  have hsc : ∀ i, i < ctx.n →
      (firstScatter ctx.n st.firstlab st.lab)[st.firstlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hfirstOk j (by rw [hrefs.firstSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (firstScatter ctx.n st.firstlab st.lab) ctx.n = true := by
    apply checkAutom_scatter_of_isautom
      (firstScatter_size ctx.n st.firstlab st.lab)
      hrefs.firstSize
      (isPerm_of_cellsReach hrefs.firstSize hn0 hrefs.firstReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega)) hsymm hloop hgb hpass
  rw [processnode_auto_autos heq hsent hnc hpass]
  exact hprev.pushFmperm rfl hn0 hgb hrefs.firstSize hrefs.firstReach
    hok.labSize hok.reach hsc hca

/-- A successful code-two admission preserves the root automorphism
ledger. -/
theorem AutosOk.processnodeRowTie {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  have hcanonOk := labOk_of_reach hrefs.canonSize hrefs.canonReach
  have hinj := labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach
  have hsc : ∀ i, i < ctx.n →
      (canonScatter ctx.n st.canonlab st.lab)[st.canonlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    rw [canonScatter_eq_firstScatter]
    apply firstScatter_get
      (fun a b ha hb hab => hinj a b (by omega) (by omega) hab)
      (fun j hj => hcanonOk j (by rw [hrefs.canonSize]; omega))
    omega
  have hca : checkAutom ctx.g
      (canonScatter ctx.n st.canonlab st.lab) ctx.n = true := by
    apply checkAutom_scatter_of_leafRows_eq
      (by rw [canonScatter_eq_firstScatter]; exact
        firstScatter_size ctx.n st.canonlab st.lab)
      hrefs.canonSize
      (isPerm_of_cellsReach hrefs.canonSize hn0 hrefs.canonReach)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)
      (fun i hi => hsc i (by omega)) hgb
      (rows_eq_of_testcanlab_tie hcanong htie)
  rw [processnode_rowTie_autos hef hnc hcc hge htie]
  exact hprev.pushFmperm rfl hn0 hgb hrefs.canonSize hrefs.canonReach
    hok.labSize hok.reach hsc hca

/-- The shared code-three/code-four tail preserves the ledger whenever
its optional implicit pair is valid. -/
theorem AutosOk.pruneAutos {ctx : Ctx} {G : Colored n k}
    {level : Nat} {st : SearchSt}
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n (pruneAutos ctx level st) := by
  unfold Hex.GraphIso.Nauty.pruneAutos
  split
  · exact hprev
  · exact autosOk_pushAuto hprev (hpair (by assumption))

private theorem processnode_plain_autos {ctx : Ctx}
    {level numcells : Nat} {st : SearchSt}
    (hfast : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0))
    (hnc : ¬((numcells == ctx.n) = true)) :
    (processnode ctx level numcells st).2.autos = st.autos := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.autos)]
  simp [hfast, hnc]

/-- Off the first path, `processnode` preserves the root ledger in every
comparison-machine outcome. -/
theorem AutosOk.processnodeOff {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2)
    (hef : ¬((st.eqlevFirst == level) = true)) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  have hef' : st.eqlevFirst ≠ level := fun he => hef (beq_iff_eq.mpr he)
  have hprune := hprev.pruneAutos hpair
  rcases hcode.tri with hzero | ⟨j, hj1, hjc, hjb, heqlev, hpre, hcase⟩
  · have hcc : st.compCanon = 0 := hzero.1
    rcases hnc : (numcells == ctx.n) with _ | _
    · rw [processnode_plain_autos (by rw [hcc]; omega)
          (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == ctx.n) = true := hnc
      rcases Decidable.em (level < st.canonlevel) with hlt | hge
      · rw [processnode_shortInstall_autos hef hnc' hcc hlt]
        exact hprune
      · let row := (testcanlab ctx
          (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        rcases Int.lt_trichotomy row 0 with hrow | hrow | hrow
        · rw [processnode_rowReject_autos hef hnc' hcc hge hrow]
          exact hprune
        · exact hprev.processnodeRowTie hn hn0 hgb hok hrefs hcanong
            hef hnc' hcc hge hrow
        · rw [processnode_rowInstall_autos hef hnc' hcc hge hrow]
          exact hprune
  · rcases hcase with hdown | hup
    · have hcc : st.compCanon = -1 := hdown.1
      rw [processnode_fast_autos ⟨hef', by rw [hcc]; omega⟩]
      exact hprune
    · have hcc : st.compCanon = 1 := hup.1
      rcases hnc : (numcells == ctx.n) with _ | _
      · rw [processnode_plain_autos (by rw [hcc]; omega)
            (by simp [hnc])]
        exact hprev
      · have hnc' : (numcells == ctx.n) = true := hnc
        rw [processnode_upInstall_autos hef hnc' hcc]
        exact hprune

/-- A failed first-path generator gate reduces to the ordinary off-path
ledger proof once canonical-labelling validity discharges the reused
workspace overwrite. -/
theorem AutosOk.processnodeGateFail {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2)
    (heq : (st.eqlevFirst == level) = true)
    (hnc : (numcells == ctx.n) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter ctx.n st.firstlab st.lab) = false) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  subst n
  let off := { st with eqlevFirst := level + 1 }
  have hoff : AutosOk ctx.g
      (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells off).2.autos := by
    apply AutosOk.processnodeOff rfl hn0 hgb (st := off) (cs := cs)
      (bs := bs)
    · exact ⟨hok.labSize, hok.ptnSize, hok.reach, hok.init1, hok.vals,
        hok.count, hok.bc, hok.canon⟩
    · exact ⟨hrefs.firstSize, hrefs.firstReach, hrefs.canonSize,
        hrefs.canonReach⟩
    · change CanongInv ctx st.canong st.canonlab st.samerows
      exact hcanong
    · change CodeCmpInv ctx.n cs bs st.canoncode st.canonlevel
        st.eqlevCanon st.compCanon
      exact hcode
    · change AutosOk ctx.g
        (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n st.autos
      exact hprev
    · change level ≠ st.noncheaplevel →
        PairOk ctx.g
          (initPtn ctx.n (ctx.n + 2) (initialPartition G).2)
          (initialPartition G).1 1 ctx.n
          (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
          (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2
      exact hpair
    · simp [off]
  rw [processnode_gateFail_autos hrefs.canonSize
    (labOk_of_reach hrefs.canonSize hrefs.canonReach)
    (labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach)
    heq hnc hfail]
  exact hoff

/-- `processnode` preserves the root automorphism ledger in every leaf,
internal, generator, and comparison-prune outcome. -/
theorem AutosOk.processnode {ctx : Ctx} {G : Colored n k}
    {level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcode : CodeCmpInv n cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hprev : AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n st.autos)
    (hpair : level ≠ st.noncheaplevel →
      PairOk ctx.g
        (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 1 ctx.n
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).1
        (fmptn st.lab st.ptn st.noncheaplevel ctx.n).2) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  rcases heq : (st.eqlevFirst == level) with _ | _
  · exact hprev.processnodeOff hn hn0 hgb hok hrefs hcanong hcode
      hpair (by
        intro htrue
        rw [heq] at htrue
        exact Bool.noConfusion htrue)
  · rcases hnc : (numcells == ctx.n) with _ | _
    · rw [processnode_plain_autos
        (by intro h; exact h.1 (beq_iff_eq.mp heq)) (by simp [hnc])]
      exact hprev
    · have hnc' : (numcells == ctx.n) = true := hnc
      rcases hsent : (st.firstcode[level + 1]! == codeSentinel) with _ | _
      · apply hprev.processnodeGateFail hn hn0 hgb hok hrefs hcanong hcode
          hpair heq hnc'
        exact Or.inl (by simpa only [beq_eq_false_iff_ne] using hsent)
      · have hsent' : st.firstcode[level + 1]! = codeSentinel :=
          beq_iff_eq.mp hsent
        rcases hpass : isautom ctx
            (firstScatter ctx.n st.firstlab st.lab) with _ | _
        · apply hprev.processnodeGateFail hn hn0 hgb hok hrefs hcanong
            hcode hpair heq hnc'
          exact Or.inr hpass
        · exact hprev.processnodeAuto hn hn0 hgb hsymm hloop hok hrefs
            heq hsent' hnc' hpass

/-- The stable search invariant now discharges the last independent
ledger premise of `processnode`: the runtime bound selects the frozen
pair carried by `CheapOk`. -/
theorem RunInv.processnodeAutos {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (h : RunInv G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn hn0 hgb hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- The prepared state also discharges the root-ledger premise of a leaf
event; unlike `RunInv`, it permits the positive comparison sign produced
by the immediately preceding code comparison. -/
theorem RunPrep.processnodeAutos {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (h : RunPrep G ctx tcLevel level cs bs fs numcells st best trail)
    (hbound : st.noncheaplevel ≤ level) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 ctx.n
      (processnode ctx level numcells st).2.autos := by
  apply h.autosOk.processnode hn hn0 hgb hsymm hloop h.searchOk
    h.leafRefs h.canongInv h.codeInv
  intro hne
  exact h.cheap.ready hbound hne

/-- An ordinary off-first-path discrete leaf turns the prepared state
into an event state whose incumbent is exactly the maximum of the old
incumbent and that leaf.  The return disjunction is retained for the
node outcome split. -/
theorem RunPrep.leaf {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
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
    · rw [hnew] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn hn0 hgb hsymm hloop hbound
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew]
      exact hlevel

/-- A first-path-agreeing leaf whose generator admission guard fails has
the same exact event invariant as an ordinary compared leaf. -/
theorem RunPrep.leafFirst {ctx : Ctx} {G : Colored n k}
    {tcLevel level numcells : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = cs.length)
    (hbound : st.noncheaplevel ≤ level)
    (heq : (st.eqlevFirst == level) = true)
    (hfail : st.firstcode[level + 1]! ≠ codeSentinel ∨
      isautom ctx (firstScatter ctx.n st.firstlab st.lab) = false)
    (hnc : (numcells == ctx.n) = true)
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
    · rw [hnew] at hlt
      omega
  refine ⟨bs', ?_, hmax, hreturn⟩
  refine ⟨hmachines, ?_, hcanong, ?_, ?_, h.cheap.processnode,
    h.leafRefs.processnode h.searchOk, hguides, h.trailOk.processnode,
    ?_, ?_, hbs', rfl⟩
  · rw [hfirstCode, heqFirst]
    exact h.firstInv
  · exact h.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
      h.searchOk h.canongInv h.genTraceOk
  · exact h.processnodeAutos hn hn0 hgb hsymm hloop hbound
  · rw [hgcaFirst]
    exact h.firstPositive
  · rcases processnode_canonGuide ctx cs.length numcells st with
      hold | hnew
    · rw [hold.1]
      exact h.canonPositive
    · rw [hnew]
      exact hlevel

end Hex.GraphIso.Nauty
