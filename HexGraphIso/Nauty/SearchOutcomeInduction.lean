/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLocatedProof
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
    {rlab rptn : Array Nat} {tcLevel level numcells : Nat}
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
    (hne : cs ≠ []) :
    RunInv G ctx rlab rptn tcLevel level cs cs cs numcells
      (Nauty.firstterminal level st)
      (some (pathLeafKey ctx cs st.lab)) trail := by
  subst level
  have hstate := firstterminal_state cs.length st
  have hstore := firstterminal_store cs.length st
  refine ⟨hok.firstterminal,
    firstterminal_codeInv hcanonSize hbound hcodes hlt,
    firstterminal_firstCodeInv hfirstSize hbound hcodes hlt,
    firstterminal_canongInv hcanong, ?_, ?_, ?_,
    LeafRefsOk.firstterminal hok, ?_, ?_, hne, ?_⟩
  · intro γ hγ
    rw [hstore.1, hgen] at hγ
    simp at hγ
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

/-! # Event state and recovery -/

/-- State returned by a node event before its caller applies `recover`.
The second comparison-machine case is the row-rejection reset: the
mutable sign is negative while the retained proof is deliberately stated
at sign zero, exactly as required by `recover_codeInv_reset`. -/
structure RunEvent (G : Colored n k) (ctx : Ctx)
    (rlab rptn : Array Nat) (tcLevel current : Nat)
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
  autosOk : AutosOk ctx.g rptn rlab 1 ctx.n st.autos
  leafRefs : LeafRefsOk G st
  guides : GuideStore ctx tcLevel current st best trail
  bestCodes : bs ≠ []
  incumbent : best = some (incKey ctx bs st.canonlab)

/-- A stable state is already a valid event state. -/
theorem RunInv.event {G : Colored n k} {ctx : Ctx}
    {rlab rptn : Array Nat} {tcLevel level numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunInv G ctx rlab rptn tcLevel level cs bs fs numcells st best
      trail) :
    RunEvent G ctx rlab rptn tcLevel level cs bs fs st best trail :=
  ⟨Or.inl ⟨h.nonpositive, h.codeInv⟩, h.firstInv, h.canongInv,
    h.genTraceOk, h.autosOk, h.leafRefs, h.guides, h.bestCodes,
    h.incumbent⟩

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
    {rlab rptn : Array Nat} {tcLevel current level inf numcells : Nat}
    {cs bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : RunEvent G ctx rlab rptn tcLevel current cs bs fs st best trail)
    (hle : level ≤ current) (hpath : level ≤ cs.length)
    (hok : SearchOk G level numcells (Nauty.recover ctx.n inf level st))
    (hstab : ∀ γ ∈ (Nauty.recover ctx.n inf level st).genTrace,
      CellStab (Nauty.recover ctx.n inf level st).ptn level
        (Nauty.recover ctx.n inf level st).lab γ) :
    RunInv G ctx rlab rptn tcLevel level (cs.take level) bs fs numcells
      (Nauty.recover ctx.n inf level st) best trail := by
  have hm := recover_machines
    (nn := n) (N := ctx.n) (inf := inf) (cs := cs) (bs := bs)
    (fs := fs) (st := st) (lvl := level)
    (h.machines.elim Or.inl (fun hr => Or.inr hr.2)) h.firstInv hpath
  have hstore := recover_store ctx.n inf level st
  have hframes := recover_frames ctx.n inf level st
  have hnp : st.compCanon ≤ 0 := h.machines.elim (fun hl => hl.1)
    (fun hr => Int.le_of_lt hr.1)
  refine ⟨hok, hm.1, hm.2, canongInv_recover h.canongInv, hstab,
    genTraceOk_of_eq hstore.1 h.genTraceOk,
    autosOk_of_eq hstore.2 h.autosOk, h.leafRefs.recover,
    h.guides.recover hle, recover_nonpositive hnp, h.bestCodes, ?_⟩
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

end Hex.GraphIso.Nauty
