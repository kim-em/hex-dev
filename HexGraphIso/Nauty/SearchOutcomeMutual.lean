/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexGraphIso.Nauty.SearchOutcomeResult
import all HexGraphIso.Nauty.Search

public section

/-!
The live hypotheses shared by the corrected mutual search induction.

These clauses deliberately describe a state at which search may continue.
GCA ordering is not a result-side invariant: the first-child loop raises
`gcaFirst` before an early unwind, so a returned state need not satisfy it.
-/

namespace Hex.GraphIso.Nauty

/-- Every vertex recorded as fixed occupies a singleton cell of the
current partition.  This is the executable path fact that makes erasing a
completed child's temporary fixed vertex restore its parent set exactly. -/
@[expose] def FixedCells (ctx : Ctx) (level : Nat) (st : SearchSt) : Prop :=
  ∀ v, v < ctx.n → elem st.fixedpts v = true →
    ∃ q, q < ctx.n ∧ st.lab[q]! = v ∧ IsCell st.ptn level q 1

namespace FixedCells

/-- The initial search has no fixed vertices. -/
theorem root {G : Colored n k} :
    FixedCells { n := n, g := rowsOf G } 1
      (rootSt n (initialPartition G).1 (initialPartition G).2) := by
  intro v hv hm
  simp [rootSt, elem] at hm

/-- A vertex in a non-singleton target cell is not already fixed. -/
theorem fresh {ctx : Ctx} {level tc len o : Nat} {st : SearchSt}
    (h : FixedCells ctx level st) (hok : LabOk st.lab ctx.n)
    (hinj : LabInj st.lab ctx.n) (hsize : st.lab.size = ctx.n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n) (ho : o < len) :
    elem st.fixedpts st.lab[tc + o]! = false := by
  rcases hm : elem st.fixedpts st.lab[tc + o]! with _ | _
  · rfl
  · have hv : st.lab[tc + o]! < ctx.n := by
      exact hok (tc + o) (by omega)
    obtain ⟨q, hq, hqv, hsingle⟩ := h _ hv hm
    have heq : q = tc + o := by
      apply LabInj.eq_of_getElem! hinj hq (by omega)
      exact hqv
    subst q
    rcases isCell_disj_or_eq hsingle hcell with heq | hleft | hright
    · omega
    · omega
    · omega

/-- Reordering vertices within unchanged cells preserves fixed
singletons. -/
theorem ofCellsPerm {ctx : Ctx} {level : Nat} {st out : SearchSt}
    (h : FixedCells ctx level st) (hfixed : out.fixedpts = st.fixedpts)
    (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab) :
    FixedCells ctx level out := by
  intro v hv hm
  rw [hfixed] at hm
  obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hm
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hqv]
    exact (cellsPerm_singleton hperm hsingle).symm
  · rw [hptn]
    exact hsingle

/-- A parent-level search effect preserves fixed singletons when it
preserves the fixed-point bitset. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx} {level numcells : Nat}
    {st out : SearchSt} (h : FixedCells ctx level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    FixedCells ctx level out :=
  h.ofCellsPerm hfixed (heffect.ptnEq hok hout) heffect.perm

/-- Refinement preserves every existing fixed singleton. -/
theorem refine {ctx : Ctx} {level active numcells : Nat} {st : SearchSt}
    (h : FixedCells ctx level st) (hsize : st.lab.size = ctx.n)
    (hpsize : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    FixedCells ctx level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro v hv hm
  obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hm
  refine ⟨q, hq, ?_, ?_⟩
  · exact (refine_fixes_singleton (by rw [hpsize]; exact Nat.le_refl _)
      (by rw [hsize, hpsize]) hend hsingle).trans hqv
  · exact isCell_refine_one (by rw [hpsize])
      (by rw [hsize, hpsize]) hend hsingle

/-- Individualizing a fresh target vertex adds exactly one fixed
singleton and preserves every older fixed singleton. -/
theorem breakout {ctx : Ctx} {level tc len o : Nat} {st : SearchSt}
    (h : FixedCells ctx level st) (hinj : LabInj st.lab ctx.n)
    (hsize : st.lab.size = ctx.n)
    (hpsize : st.ptn.size = ctx.n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n) (ho : o < len) :
    FixedCells ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + o]! } := by
  have hinjSize : LabInj st.lab st.lab.size := by
    rw [hsize]
    exact hinj
  intro v hv hm
  rw [elem_insert] at hm
  rcases (Bool.or_eq_true _ _).mp hm with hold | hnew
  · obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hold
    have hne : q ≠ tc := by
      intro heq
      subst q
      rcases isCell_disj_or_eq hsingle hcell with heq | hleft | hright
      · omega
      · omega
      · omega
    have hout := singleton_outside_cell hsingle hcell hne ho
    refine ⟨q, hq, ?_, ?_⟩
    · exact (breakout_misses_singleton (ptn := st.ptn)
        (level := level) hinjSize (by rw [hsize]; omega) hout).trans hqv
    · rw [breakout_ptn]
      exact isCell_set_miss hsingle hcell hlen
  · have heq : st.lab[tc + o]! = v := beq_iff_eq.mp hnew
    refine ⟨tc, by omega, ?_, ?_⟩
    · rw [breakout_at_target hinjSize (by rw [hsize]; omega), heq]
    · exact isCell_breakout_target (lab := st.lab)
        (tv := st.lab[tc + o]!) (by rw [hpsize]; omega) hcell.2.1

end FixedCells

/-- Passing a fix test for a larger fixed set implies passing it for any
pointwise smaller set. -/
theorem fixTest_mono {small large fix : Nat}
    (hsub : ∀ v, elem small v = true → elem large v = true)
    (hfix : (large &&& fix == large) = true) :
    (small &&& fix == small) = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro v
  change elem (small &&& fix) v = elem small v
  rw [elem_and]
  rcases hs : elem small v with _ | _
  · simp
  · simp only [Bool.true_and]
    exact elem_of_and_eq hfix (hsub v hs)

/-- The bounded automorphism workspace is valid at the current frame for
every entry whose fixed set covers the current search path. -/
@[expose] def LocalAutos (ctx : Ctx) (level : Nat) (st : SearchSt) : Prop :=
  ∀ p ∈ st.autos.toList,
    (st.fixedpts &&& p.1 == st.fixedpts) = true →
      PairOk ctx.g st.ptn st.lab level ctx.n p.1 p.2

namespace LocalAutos

/-- An empty workspace is locally valid. -/
theorem empty {ctx : Ctx} {level : Nat} {st : SearchSt}
    (h : st.autos = #[]) : LocalAutos ctx level st := by
  intro p hp
  rw [h] at hp
  simp at hp

/-- Cell stabilization is independent of the ordering chosen inside each
cell. -/
theorem reindexStab {ptn lab lab' gamma : Array Nat} {level n : Nat}
    (h : CellStab ptn level lab gamma)
    (hperm : cellsPerm ptn level lab lab')
    (hpsize : ptn.size = n) (hsize : lab.size = n)
    (hsize' : lab'.size = n) (hend : ptn[ptn.size - 1]! ≤ level) :
    CellStab ptn level lab' gamma := by
  apply cellStab_of_scatter hpsize hsize' hsize hend
      (cellsPerm_symm hperm)
      (cellsPerm_trans (cellsPerm_symm hperm) h)
  intro i hi
  rw [getElem!_map_of_lt _ _ (by rw [hsize]; exact hi)]

/-- A locally valid pair remains valid after reordering the frame within
its cells. -/
theorem reindexPair {ctx : Ctx} {ptn lab lab' : Array Nat}
    {level fix mcr : Nat}
    (h : PairOk ctx.g ptn lab level ctx.n fix mcr)
    (hperm : cellsPerm ptn level lab lab')
    (hpsize : ptn.size = ctx.n) (hsize : lab.size = ctx.n)
    (hsize' : lab'.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    PairOk ctx.g ptn lab' level ctx.n fix mcr := by
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfix, hstab, hlt⟩ := h v hv hmcr
  exact ⟨gamma, hcheck, hfix,
    reindexStab hstab hperm hpsize hsize hsize' hend, hlt⟩

/-- Local ledger validity transports across unchanged partition cells and
a within-cell labelling permutation. -/
theorem ofCellsPerm {ctx : Ctx} {level : Nat} {st out : SearchSt}
    (h : LocalAutos ctx level st) (hautos : out.autos = st.autos)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = ctx.n) (hsize : st.lab.size = ctx.n)
    (hsize' : out.lab.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    LocalAutos ctx level out := by
  intro p hp hfix
  rw [hautos] at hp
  rw [hfixed] at hfix
  have hpair := h p hp hfix
  rw [hptn]
  exact reindexPair hpair hperm hpsize hsize hsize' hend

/-- The conditional local ledger descends through one
individualization.  A pair applicable to the enlarged fixed set fixes the
selected vertex, exactly the premise needed by `cellStab_breakout`. -/
theorem breakout {ctx : Ctx} {level tc len o : Nat} {st : SearchSt}
    (h : LocalAutos ctx level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size) (hsize : st.lab.size = st.ptn.size)
    (hlab : LabOk st.lab ctx.n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    LocalAutos ctx (level + 1)
      { st with
        lab := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + o]! } := by
  intro p hp hfix
  have hsub : ∀ v, elem st.fixedpts v = true →
      elem (insert st.fixedpts st.lab[tc + o]!) v = true := by
    intro v hv
    rw [elem_insert, hv]
    rfl
  have hparent := fixTest_mono hsub hfix
  have hpair := h p hp hparent
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hpair v hv hmcr
  have hselected : elem p.1 st.lab[tc + o]! = true := by
    apply elem_of_and_eq hfix
    rw [elem_insert]
    simp
  have hselectedBound : st.lab[tc + o]! < ctx.n :=
    hlab _ (by rw [hsize]; omega)
  exact ⟨gamma, hcheck, hfixes,
    cellStab_breakout hstab hcell hrange hsize ho hlen hend hvals
      (hfixes _ hselectedBound hselected), hlt⟩

/-- The conditional local ledger is preserved by equitable refinement. -/
theorem refine {ctx : Ctx} {level active numcells : Nat} {st : SearchSt}
    (h : LocalAutos ctx level st) (hgsz : ctx.g.size = ctx.n)
    (hsize : st.lab.size = ctx.n) (hlab : LabOk st.lab ctx.n)
    (hpsize : st.ptn.size = ctx.n) (hactive : active < 2 ^ ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, elem active v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    LocalAutos ctx level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro p hp hfix
  have hpair := h p hp hfix
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hpair v hv hmcr
  exact ⟨gamma, hcheck, hfixes,
    cellStab_refine (n := ctx.n) rfl hstab hgsz hcheck hsize hlab
      hpsize hactive hend hstarts, hlt⟩

end LocalAutos

/-- A root-stabilizing checked automorphism that fixes every vertex on the
current individualized path stabilizes the current partition.  Keeping the
root frame explicit lets the existing root autos ledger supply the same
witness at every pruning site. -/
@[expose] def PathStab (ctx : Ctx) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt) : Prop :=
  ∀ gamma, checkAutom ctx.g gamma ctx.n = true →
    CellStab rootPtn 1 rootLab gamma →
    (∀ u, u < ctx.n → elem st.fixedpts u = true → gamma[u]! = u) →
    CellStab st.ptn level st.lab gamma

namespace PathStab

/-- A frame is its own path-stabilization seed. -/
theorem same {ctx : Ctx} {st : SearchSt} :
    PathStab ctx st.ptn st.lab 1 st := by
  intro gamma _ hstab _
  exact hstab

/-- Reordering the current labelling within unchanged cells preserves path
stabilization. -/
theorem ofCellsPerm {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level : Nat} {st out : SearchSt}
    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = ctx.n) (hsize : st.lab.size = ctx.n)
    (hsize' : out.lab.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  intro gamma hcheck hroot hfix
  rw [hfixed] at hfix
  rw [hptn]
  exact LocalAutos.reindexStab (h gamma hcheck hroot hfix) hperm
    hpsize hsize hsize' hend

/-- A parent-level search effect preserves path stabilization when it
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt}
    (hn : ctx.n = n)
    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  subst n
  exact h.ofCellsPerm hfixed (heffect.ptnEq hok hout) heffect.perm
    hok.ptnSize hok.labSize hout.labSize hend

/-- Equitable refinement preserves path stabilization. -/
theorem refine {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level active numcells : Nat} {st : SearchSt}
    (h : PathStab ctx rootPtn rootLab level st)
    (hgsz : ctx.g.size = ctx.n)
    (hsize : st.lab.size = ctx.n) (hlab : LabOk st.lab ctx.n)
    (hpsize : st.ptn.size = ctx.n) (hactive : active < 2 ^ ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, elem active v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro gamma hcheck hroot hfix
  exact cellStab_refine (n := ctx.n) rfl
    (h gamma hcheck hroot hfix) hgsz hcheck hsize hlab hpsize hactive
    hend hstarts

/-- Individualization extends path stabilization because an automorphism
fixing the enlarged path fixes the selected target vertex. -/
theorem breakout {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level tc len o : Nat} {st : SearchSt}
    (h : PathStab ctx rootPtn rootLab level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size)
    (hsize : st.lab.size = st.ptn.size) (hlab : LabOk st.lab ctx.n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    PathStab ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + o]! } := by
  intro gamma hcheck hroot hfix
  have hparent : ∀ u, u < ctx.n → elem st.fixedpts u = true →
      gamma[u]! = u := by
    intro u hu hm
    apply hfix u hu
    rw [elem_insert, hm]
    rfl
  have hselected : gamma[st.lab[tc + o]!]! = st.lab[tc + o]! := by
    apply hfix _ (hlab _ (by rw [hsize]; omega))
    rw [elem_insert]
    simp
  exact cellStab_breakout (h gamma hcheck hroot hparent) hcell hrange
    hsize ho hlen hend hvals hselected

/-- The root autos ledger and path stabilization reconstruct the
conditional ledger consumed by the two pruning filters. -/
theorem toLocal {ctx : Ctx} {rootPtn rootLab : Array Nat}
    {level : Nat} {st : SearchSt}
    (h : PathStab ctx rootPtn rootLab level st)
    (hroot : AutosOk ctx.g rootPtn rootLab 1 ctx.n st.autos) :
    LocalAutos ctx level st := by
  intro p hp hfix v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ :=
    hroot p hp v hv hmcr
  refine ⟨gamma, hcheck, hfixes, ?_, hlt⟩
  apply h gamma hcheck hstab
  intro u hu hmem
  exact hfixes u hu (elem_of_and_eq hfix hmem)

end PathStab

/-! # Fixed-point frame equations -/

theorem pushAuto_fixedpts (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).fixedpts = st.fixedpts := by
  rw [pushAuto]
  split <;> rfl

/-- Leaf processing never changes the individualized path. -/
theorem processnode_fixedpts (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.fixedpts = st.fixedpts := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.fixedpts),
    pushAuto_fixedpts, ite_self]

/-- Comparison preparation never changes the individualized path. -/
theorem otherNodePrep_fixedpts (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).fixedpts = st.fixedpts := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.fixedpts, ite_self]

/-- Recovery never changes the individualized path. -/
theorem recover_fixedpts (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).fixedpts = st.fixedpts := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.fixedpts, ite_self]

/-- First-leaf installation never changes the individualized path. -/
theorem firstterminal_fixedpts (level : Nat) (st : SearchSt) :
    (firstterminal level st).fixedpts = st.fixedpts := by
  rw [firstterminal]
  rfl

/-- First-path sweep cleanup never changes the individualized path. -/
theorem firstFinish_fixedpts (level size index : Nat) (st : SearchSt) :
    (firstFinish level size index st).fixedpts = st.fixedpts := by
  rw [firstFinish]
  split <;> rfl

/-- The two path facts threaded only by the corrected mutual induction:
fixed vertices are singleton cells, and root-valid automorphisms fixing
them stabilize the current cells. -/
structure PathOk (ctx : Ctx) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt) : Prop where
  fixed : FixedCells ctx level st
  stab : PathStab ctx rootPtn rootLab level st

namespace PathOk

/-- The nonempty root seeds both path facts. -/
theorem root {G : Colored n k} :
    PathOk { n := n, g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (rootSt n (initialPartition G).1 (initialPartition G).2) := by
  constructor
  · exact FixedCells.root
  · simpa only [rootSt] using
      (PathStab.same (ctx := { n := n, g := rowsOf G })
        (st := rootSt n (initialPartition G).1
          (initialPartition G).2))

/-- Node-entry refinement preserves both path facts. -/
theorem refine {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab : Array Nat} {level active numcells : Nat}
    {st : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = ctx.n)
    (hok : SearchOk G level numcells st)
    (hactive : active < 2 ^ ctx.n)
    (hstarts : ∀ v : Nat, elem active v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  subst n
  have hend := searchOk_end hn0 hok hlevel
  have hlab : LabOk st.lab ctx.n :=
    labOk_of_reach hok.labSize hok.reach
  constructor
  · exact h.fixed.refine hok.labSize hok.ptnSize hend
  · exact h.stab.refine hgsz hok.labSize hlab hok.ptnSize hactive
      hend hstarts

/-- A loop child extends both path facts by its selected fresh vertex. -/
theorem breakout {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab rsLab rsPtn : Array Nat}
    {tcLevel specFuel level numcells tc len tcell currentOffset : Nat}
    {codes bs fs : List Nat} {cursor : Option Nat}
    {base st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcurrent : currentOffset < len)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (Nauty.breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! } := by
  have hn := hinv.nodeCount
  subst n
  have hok := hinv.run.searchOk
  have hend := searchOk_end hinv.nonempty hok hinv.positive
  have hlab : LabOk st.lab ctx.n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab ctx.n :=
    labInj_of_reach hok.labSize hinv.nonempty hok.reach
  have hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1 := by
    intro q heq
    rw [hinv.ptnEq] at heq
    rcases hinv.values q with hle | hinf
    · omega
    · have hbound := hinv.fuelBound
      omega
  constructor
  · exact h.fixed.breakout hinj hok.labSize hok.ptnSize
      hinv.currentCell hinv.lenTwo hinv.range hcurrent
  · exact h.stab.breakout hinv.currentCell
      (by rw [hok.ptnSize]; exact hinv.range)
      (hok.labSize.trans hok.ptnSize.symm) hlab hcurrent hinv.lenTwo
      hend hvals

/-- Recovered parent state preserves both path facts once child cleanup
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : PathOk ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    PathOk ctx rootPtn rootLab level out := by
  constructor
  · exact h.fixed.ofSearchOut hfixed hok hout heffect
  · exact h.stab.ofSearchOut hn hfixed hok hout heffect
      (searchOk_end hn0 hok hlevel)

/-- The path facts and root ledger supply the exact local ledger needed
by a pruning filter. -/
theorem autos {G : Colored n k} {ctx : Ctx}
    {level numcells tcLevel : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hrun : RunInv G ctx tcLevel level cs bs fs numcells st best trail) :
    LocalAutos ctx level st :=
  hpath.stab.toLocal hrun.autosOk

end PathOk

/-- Reference history, ordered live guides, and stabilization of every
ancestor frame to which the current node may return. -/
structure Live (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  history : RefTrail ctx level st trail
  order : st.gcaFirst ≤ st.gcaCanon
  stable : ReturnStab trail (Int.ofNat st.gcaFirst) st

namespace Live

/-- `Live` depends only on the two reference controls and labellings and
on the recorded-generator store. -/
theorem stateEq {ctx : Ctx} {level : Nat} {st st' : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (hfirstGca : st'.gcaFirst = st.gcaFirst)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanonGca : st'.gcaCanon = st.gcaCanon)
    (hcanon : st'.canonlab = st.canonlab)
    (hgen : st'.genTrace = st.genTrace) :
    Live ctx level st' trail := by
  constructor
  · exact h.history.stateEq hfirstGca hfirst hcanonGca hcanon
  · rw [hfirstGca, hcanonGca]
    exact h.order
  · rw [hfirstGca]
    exact h.stable.ofGenTraceEq hgen

/-- Target-cell accounting changes no live field. -/
theorem setTctotal {ctx : Ctx} {level value : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with tctotal := value } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Parking the cheap-automorphism boundary changes no live field. -/
theorem park {ctx : Ctx} {level boundary : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with noncheaplevel := boundary } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Fixed-point cleanup changes no live field. -/
theorem setFixed {ctx : Ctx} {level fixedpts : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with fixedpts := fixedpts } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Clearing the one-shot short-prune flag changes no live field. -/
theorem clearShort {ctx : Ctx} {level : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with needshortprune := false } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Refinement and the off-path comparison step preserve the complete live
package. -/
theorem otherLeaf {ctx : Ctx} {level numcells : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level (otherLeafSt ctx level numcells st) trail :=
  ⟨h.history.otherLeaf, RefTrail.otherLeaf_order h.order, by
    simpa only [RefTrail.otherLeaf_gcaFirst] using h.stable.otherLeaf⟩

/-- A leaf event preserves reference history and live GCA ordering.  Its
return-indexed generator stabilization is supplied separately by the
admission classifier. -/
theorem processnode {ctx : Ctx} {level numcells : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (htrail : TrailOk ctx level st trail) (hfirst : st.gcaFirst ≤ level) :
    RefTrail ctx level (Nauty.processnode ctx level numcells st).2 trail ∧
      (Nauty.processnode ctx level numcells st).2.gcaFirst ≤
        (Nauty.processnode ctx level numcells st).2.gcaCanon :=
  ⟨h.history.processnode htrail,
    RefTrail.processnode_order h.order hfirst⟩

end Live

/-- The live state of an off-path sweep.  `gcaFirst` stays strictly above
the divergence ancestor, so a child push introduces no new stabilization
obligation at the current frame. -/
structure OtherLive (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop extends Live ctx level st trail where
  firstBelow : st.gcaFirst < level

/-- The live state of a first-path sweep.  Once generators exist, the
guiding child has already been absorbed, and every recorded generator
stabilizes this frozen frame; before that point the store is empty and the
same clause is vacuous. -/
structure FirstLive (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) (rsLab rsPtn : Array Nat) : Prop
    extends Live ctx level st trail where
  frameStab : ∀ γ ∈ st.genTrace.toList,
    CellStab rsPtn level rsLab γ

namespace OtherOutcome

/-- Cleaning and recovering a completed off-path child reconstructs both
the parent's stable run invariant and its off-path live package. -/
theorem recover {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel childNumcells numcells level inf fixedpts : Nat}
    {codes fs : List Nat} {child out : SearchSt}
    {best outBest : Option Key} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out childNumcells best outBest receiptTrail eventTrail r)
    (hreturn : r = Int.ofNat level) (hpath : codes.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hfirst : child.gcaFirst < level)
    (hok : SearchOk G level numcells
      (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })) :
    ∃ bs,
      RunInv G ctx tcLevel level codes bs fs numcells
          (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })
          outBest eventTrail ∧
        OtherLive ctx level
          (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })
          eventTrail := by
  have hfirstOut : out.gcaFirst < level := by
    rw [h.firstGuide]
    exact hfirst
  have hfirstClean : ({ out with fixedpts := fixedpts } : SearchSt).gcaFirst ≤
      level := Nat.le_of_lt hfirstOut
  obtain ⟨bs, hrun, hstable, hhistory⟩ :=
    h.node.event.setFixed fixedpts |>.recoverRun hreturn hpath hlevel hinf
      hfirstClean hok
  refine ⟨bs, hrun, ?_⟩
  constructor
  · constructor
    · exact hhistory
    · exact RefTrail.recover_order (by simpa only using h.order)
        hfirstClean
    · exact hstable
  · rw [(recover_frames ctx.n inf level
      { out with fixedpts := fixedpts }).2.2.2.2.2.2.1]
    exact hfirstOut

/-- Resolving a returning off-path child advances the evolving sweep.
The impossible orbit-return arm is discharged by the strict first-guide
bound, so no current-child `cosetindex` equation is needed. -/
theorem cover {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len tcell tv offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st child out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : nextElem tcell cursor = some tv)
    (hoffset : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hfirst : child.gcaFirst < level)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1)) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest := by
  rcases h.node.parentReturn hfuel hstay with hfull |
      ⟨payload, hloc, _⟩
  · exact hinv.cover.advanceKey hnext hfull heq
  · apply hinv.cover.offPathUnwind
      (h.node.receipt.sound hfuel).grows hnext hloc
      (FrameTrail.push_self trail level _) hoffset htv
    · rw [h.firstGuide]
      exact hfirst
    · exact hinv.frozenLabSize
    · rw [← hinv.baseLab, hinv.baseOk.labSize]
      exact labInj_of_reach hinv.baseOk.labSize hinv.nonempty
        hinv.baseOk.reach
    · exact hinv.range

/-- After recovery, the first guide remains strictly older and the
canonical guide names either an earlier covered child or the child just
absorbed.  Thus both current-frame reference obligations are restored. -/
theorem refs {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len tcell tv offset
      currentOffset inf fixedpts : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest)
    (hfuel : runFuel ≠ 0)
    (hnext : nextElem tcell cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv) :
    FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len numcells
      (Nauty.recover ctx.n inf level { out with fixedpts := fixedpts })
      outBest := by
  let child : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
  let cleaned : SearchSt := { out with fixedpts := fixedpts }
  have hinc : IncGrows best outBest :=
    (h.node.receipt.sound hfuel).grows
  constructor
  · intro heq
    have hfirstRec :=
      (recover_frames ctx.n inf level cleaned).2.2.2.2.2.2.1
    have hfirstChild : child.gcaFirst = st.gcaFirst := rfl
    have hfirstOut : out.gcaFirst = st.gcaFirst := by
      exact h.firstGuide.trans hfirstChild
    rw [hfirstRec] at heq
    change out.gcaFirst = level at heq
    rw [hfirstOut] at heq
    exact (Nat.ne_of_lt hlive.firstBelow heq).elim
  · intro heq
    have hcanonRec := recover_gcaCanon ctx.n inf level cleaned
    have hcanonLab := (recover_frames ctx.n inf level cleaned).1
    rcases h.canonGuide with hold | hnew
    · have hcanonChild : child.gcaCanon = st.gcaCanon := rfl
      have hcanonOut : out.gcaCanon = st.gcaCanon :=
        hold.1.trans hcanonChild
      have hcanonEq : st.gcaCanon = level := by
        rw [hcanonRec] at heq
        change (if level < out.gcaCanon then level else out.gcaCanon) =
          level at heq
        rw [hcanonOut] at heq
        rw [ite_eq_right (Nat.not_lt_of_ge hinv.run.canonBound)] at heq
        exact heq
      obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
        (hinv.refs.grow hinc).canon hcanonEq
      refine ⟨o, ho, hdone, ?_, ?_⟩
      · rw [hcanonLab]
        change out.canonlab[tc]! = rsLab[tc + o]!
        rw [hold.2]
        exact hatRef
      · rw [hcanonLab]
        change cellsPerm rsPtn level rsLab out.canonlab
        rw [hold.2]
        exact hperm
    · have hmem : elem tcell rsLab[tc + offset]! = true := by
        rw [htv]
        exact nextElem_mem hnext
      have hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells outBest offset :=
        hcover.past offset hoffset hmem (by
          simp only [After, htv]
          omega)
      have hstSize : st.lab.size = ctx.n := by
        rw [hinv.nodeCount]
        exact hinv.run.searchOk.labSize
      have hstPtnSize : st.ptn.size = ctx.n := by
        rw [hinv.nodeCount]
        exact hinv.run.searchOk.ptnSize
      have hcurrentPos : tc + currentOffset < st.lab.size := by
        rw [hstSize]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcurrent tc)
          hinv.range
      have htcPtn : tc < st.ptn.size := by
        rw [hstPtnSize]
        exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
      have hrangePtn : tc + len ≤ st.ptn.size := by
        rw [hstPtnSize]
        exact hinv.range
      have hstInj : LabInj st.lab st.lab.size := by
        rw [hinv.run.searchOk.labSize]
        exact labInj_of_reach hinv.run.searchOk.labSize hinv.nonempty
          hinv.run.searchOk.reach
      have hchildAt : child.lab[tc]! = tv := by
        change (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1[tc]! = tv
        rw [breakout_at_target hstInj hcurrentPos, hat]
      have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) := by
        exact breakout_ptn st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!
      have hchildCell : IsCell child.ptn (level + 1) tc 1 := by
        rw [hchildPtn]
        exact isCell_breakout_target (lab := st.lab)
          (tv := st.lab[tc + currentOffset]!) htcPtn
          hinv.currentCell.2.1
      have houtAt : out.canonlab[tc]! = tv := by
        rw [← hchildAt]
        exact (cellsPerm_singleton hnew.2 hchildCell).symm
      have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
        apply breakout_searchOk hinv.nonempty hinv.run.searchOk hinv.positive
          hinv.currentCell hinv.lenTwo
          (by rw [← hinv.nodeCount]; exact hinv.range) hcurrent
        · rfl
        · exact hchildPtn
        · rfl
      have hfine : cellsPerm st.ptn level child.lab out.canonlab := by
        apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
        · rw [hchildPtn, Array.size_set!]
        · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
        · rw [h.node.event.canonSize, hchildOk.ptnSize,
            ← hinv.nodeCount]
        · exact hnew.2
        · exact searchOk_end hinv.nonempty hchildOk (by omega)
        · exact searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
        · intro q hq
          rw [hchildPtn]
          rcases Decidable.em (tc = q) with rfl | hne
          · rw [Array.getElem!_set!_self _ _ _ htcPtn]
            exact Nat.le_refl _
          · rw [Array.getElem!_set!_ne _ _ _ _ hne]
            omega
      have hbreak : cellsPerm st.ptn level st.lab child.lab := by
        change cellsPerm st.ptn level st.lab
          (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
        exact breakout_cellsPerm hinv.currentCell hrangePtn
          (by rw [hinv.run.searchOk.labSize, hinv.run.searchOk.ptnSize])
          hcurrent
      have hperm : cellsPerm rsPtn level rsLab out.canonlab := by
        rw [hinv.ptnEq] at hbreak hfine
        exact cellsPerm_trans hinv.labPerm (cellsPerm_trans hbreak hfine)
      refine ⟨offset, hoffset, hdone, ?_, ?_⟩
      · rw [hcanonLab]
        change out.canonlab[tc]! = rsLab[tc + offset]!
        rw [houtAt, htv]
      · rw [hcanonLab]
        exact hperm

/-- An ordinary off-path child return with no requested pruning rebuilds
the complete invariant for the recursive tail of the same sweep. -/
theorem next {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells tc len tcell tv offset
      currentOffset inf : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt}
    {best outBest : Option Key} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out)
    (hinf : inf = n + 2) (hpath : codes.length = level)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : nextElem tcell cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).1
            ptn := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.1
            active := (breakout st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.2
            fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
          (numcells + 1))
    (hshort : out.needshortprune = false) :
    let cleaned : SearchSt :=
      { out with fixedpts := erase out.fixedpts tv }
    let recovered := Nauty.recover ctx.n inf level cleaned
    ∃ bs',
      LoopInv G ctx tcLevel specFuel level codes bs' fs numcells rsLab rsPtn
          tc len tcell (some tv) base recovered outBest eventTrail ∧
        OtherLive ctx level recovered eventTrail := by
  dsimp only
  let child : SearchSt :=
    { st with
      lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
  let cleaned : SearchSt := { out with fixedpts := erase out.fixedpts tv }
  let recovered := Nauty.recover ctx.n inf level cleaned
  have hreturn : r = Int.ofNat level := h.node.parentEq hfuel hstay
  have hfirst : child.gcaFirst < level := by
    change st.gcaFirst < level
    exact hlive.firstBelow
  have hcoverage := h.cover hinv hfuel hstay hnext hoffset htv hfirst heq
  have hrecovered := hinv.recoverChild hinf hcurrent hout
  have heffect : SearchOut G level level base recovered := by
    simpa only [cleaned, recovered, hat] using hrecovered.1
  have hok : SearchOk G level numcells recovered := by
    simpa only [cleaned, recovered, hat] using hrecovered.2
  have hinfLevel : level < inf := by
    rw [hinf]
    have hle : level ≤ n := Nat.le_trans hinv.run.searchOk.bc
      (bcount_le st.ptn level n)
    omega
  obtain ⟨bs', hrun, hlive'⟩ := h.recover hreturn hpath hinv.positive
    hinfLevel hfirst hok
  have hrefs := h.refs hinv hlive hcoverage hfuel hnext hoffset hcurrent
    htv hat (inf := inf) (fixedpts := erase out.fixedpts tv)
  have hshort' : recovered.needshortprune = false := by
    unfold recovered cleaned
    rw [recover_needshortprune, hshort]
  refine ⟨bs', ?_, hlive'⟩
  exact {
    nodeCount := hinv.nodeCount
    nonempty := hinv.nonempty
    positive := hinv.positive
    baseOk := hinv.baseOk
    run := hrun
    effect := heffect
    baseLab := hinv.baseLab
    basePtn := hinv.basePtn
    equitable := hinv.equitable
    cell := hinv.cell
    lenTwo := hinv.lenTwo
    range := hinv.range
    values := hinv.values
    members := hinv.members
    cover := hcoverage
    refs := hrefs
    shortClear := hshort'
    fuelBound := hinv.fuelBound }

end OtherOutcome

/-- The bookkeeping between an off-path node's refinement and its fresh
child sweep preserves the live package and the strict first-reference
bound. -/
theorem NodeInv.otherLive {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells len : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    let pre := otherLeafSt ctx level numcells st
    let base : SearchSt := { pre with tctotal := pre.tctotal + len }
    let start := if cheapautom base.ptn level ctx.n then base
      else { base with noncheaplevel := level + 1 }
    OtherLive ctx level start trail := by
  dsimp only
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt := { pre with tctotal := pre.tctotal + len }
  have hpre : Live ctx level pre trail := by
    simpa only [pre] using hlive.otherLeaf (numcells := numcells)
  have hbase : Live ctx level base trail := by
    simpa only [base] using hpre.setTctotal (value := pre.tctotal + len)
  have hbelow : base.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  split
  · exact ⟨hbase, hbelow⟩
  · exact ⟨hbase.park, hbelow⟩

/-- A loop child inherits reference history and stabilization through its
live first-reference GCA.  The current frozen frame is required only when
that GCA is exactly the loop level. -/
theorem LoopInv.childLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) (offset currentOffset : Nat)
    (hframe : st.gcaFirst = level → ∀ γ ∈ st.genTrace.toList,
      CellStab rsPtn level rsLab γ) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
        cosetindex := coset }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hstable : ReturnStab (trail.push level entry)
      (Int.ofNat st.gcaFirst) st := by
    apply hlive.stable.push
    intro hle γ hγ
    have hbound := hinv.run.firstBound
    have heq := Nat.le_antisymm hbound (Int.ofNat_le.mp hle)
    exact hframe heq γ hγ
  constructor
  · simpa only [entry] using
      RefTrail.LoopInv.childHistory hinv hlive.history offset currentOffset
  · simpa only using hlive.order
  · unfold ReturnStab at hstable ⊢
    exact hstable

/-- An off-path loop's strict first-reference bound discharges the only
new-frame premise of `childLive`. -/
theorem LoopInv.otherChildLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail) (offset currentOffset : Nat) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  apply hinv.childLive hlive.toLive offset currentOffset
  intro heq
  exact (Nat.ne_of_lt hlive.firstBelow heq).elim

/-- A first-path loop carries stabilization of its frozen frame directly,
including the initial empty-store phase. -/
theorem LoopInv.firstChildLive {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : FirstLive ctx level st trail rsLab rsPtn)
    (offset currentOffset : Nat) :
    Live ctx (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
        cosetindex := coset }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) :=
  hinv.childLive hlive.toLive offset currentOffset fun _ => hlive.frameStab

/-- A non-first leaf event whose branch does not append a generator
produces the complete result-side package.  The caller supplies the strict
return bound because `processnode` itself also has a non-unwinding result
at the current level. -/
theorem RunPrep.leafEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true)
    (hreturn : (processnode ctx level numcells st).1 ≤
      Int.ofNat level - 1)
    (hgen : (processnode ctx level numcells st).2.genTrace = st.genTrace)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn hn0 hgb hsymm hloop
    hlevel hpath hbound hef hnc
  refine ⟨bs', ?_, hmax⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast
  · omega
  · have hs := hlive.stable.ofGenTraceEq hgen
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-one admission with a nonpositive incumbent comparison is a
fully verified generator event.  The semantic loop proof supplies the
nonpositivity premise from coverage of the guiding child. -/
theorem RunPrep.firstEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbelow : st.gcaFirst < level) (hnp : st.compCanon ≤ 0)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == ctx.n) = true)
    (hpass : isautom ctx
      (firstScatter ctx.n st.firstlab st.lab) = true)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    EventOut G ctx tcLevel stem fs
      (processnode ctx level numcells st).2 best trail
      (processnode ctx level numcells st).1 := by
  obtain ⟨hreturn, hcomp, heqCanon, hcode, hcanonlevel, hcanonlab,
      hcanong, hsamerows⟩ := processnode_auto heq hsent hnc hpass
  have hframes := processnode_frames ctx level numcells st
  have hgcaCanon := processnode_auto_gcaCanon heq hsent hnc hpass
  have hevent : RunEvent G ctx tcLevel level codes bs fs
      (processnode ctx level numcells st).2 best trail := by
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, hprep.bestCodes, ?_⟩
    · rw [hcomp]
      exact hnp
    · rw [hcomp, heqCanon, hcode, hcanonlevel]
      exact hprep.codeInv
    · rw [hframes.2.2.1, hframes.2.2.2.1]
      exact hprep.firstInv
    · rw [hcanong, hcanonlab, hsamerows]
      exact hprep.canongInv
    · exact hprep.leafRefs.processnodeGen hn hn0 hgb hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.autosOk.processnodeAuto hn hn0 hgb hsymm hloop
        hprep.searchOk hprep.leafRefs heq hsent hnc hpass
    · exact hprep.cheap.processnode
    · exact hprep.leafRefs.processnode hprep.searchOk
    · apply hprep.guides.processnode (IncGrows.refl best)
        hframes.2.2.2.2.2.2.1 hframes.2.2.2.2.1
      intro _
      exact ⟨hgcaCanon, hcanonlab⟩
    · exact hprep.trailOk.processnode
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstPositive
    · rw [hgcaCanon]
      exact hprep.canonPositive
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstBound
    · rw [hgcaCanon]
      exact hprep.canonBound
    · rw [hcanonlab]
      exact hprep.incumbent
  apply EventOut.intro level codes bs hevent hpath hstem hpast
  · rw [hreturn]
    exact Int.ofNat_le.mpr (Nat.le_of_lt hbelow)
  · have hs := hlive.history.processnodeFirstStab hn hn0
      hprep.trailOk hprep.leafRefs hlive.stable hbelow heq hsent hnc hpass
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-two row tie produces a verified event for either its canonical
return or its special first-ancestor orbit return. -/
theorem RunPrep.tiedEvent {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == ctx.n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcanonBelow : st.gcaCanon < level)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) ∧
        some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab) = best := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn hn0 hgb hsymm hloop
    hlevel hpath hbound hef hnc
  have hcinv : CodeCmpInv n codes bs st.canoncode st.canonlevel
      st.eqlevCanon 0 := by
    simpa only [hcc] using hprep.codeInv
  have hlen : codes.length = bs.length := by
    have hle := codeInv_tied_le hcinv
    have hblen := hcinv.blen
    omega
  have hcodes : codes = bs := codeInv_eq_of_tied hcinv hlen
  have hrows : leafRows ctx st.canonlab = leafRows ctx st.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hkey : pathLeafKey ctx codes st.lab =
      incKey ctx bs st.canonlab := by
    unfold pathLeafKey incKey
    rw [hcodes, ← hrows]
  have houtBest : some (incKey ctx bs'
      (processnode ctx level numcells st).2.canonlab) = best := by
    rw [hmax, hkey, keyMax_eq_left (keyLe_refl _)]
    exact hprep.incumbent.symm
  have hreturns := (processnode_rowTie hef hnc hcc hge htie).1
  have hreturned : (processnode ctx level numcells st).1 ≤
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_le.mpr
        (Nat.le_trans hlive.order hprep.canonBound)
    · rw [hcanon]
      exact Int.ofNat_le.mpr hprep.canonBound
  refine ⟨bs', ?_, hmax, houtBest⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast hreturned
  · have hs := hlive.history.processnodeTiedStab hn hn0 hprep.trailOk
      hprep.leafRefs hlive.order hlive.stable hcanonBelow hef hnc hcc hge
      htie
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A discrete code-one branch closes the complete node outcome.  Its
guide supplies the located unwind receipt, while `firstEvent` supplies
the result-state invariants. -/
theorem NodeInv.firstLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hnp : (otherLeafSt ctx level numcells st).compCanon ≤ 0)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter ctx.n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
    ∃ target,
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 =
        Int.ofNat target ∧
      target < level ∧
      ∃ payload : Unwind ctx tcLevel target
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 best,
        payload.Located trail := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hbelow : leaf.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  have hevent : EventOut G ctx tcLevel codes fs
      (processnode ctx level ctx.n leaf).2 best trail
      (processnode ctx level ctx.n leaf).1 := by
    apply hprep.firstEvent rfl hn0 hgb hsymm hloop hfull hstem (by omega)
      hbelow hnp
      heq hsent (by simp) hpass hlive'
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_firstReceipt hnum hprep.guides hprep.trailOk
      hprep.firstPositive hbelow hgsz hprep.leafRefs.firstSize
      (isPerm_of_cellsReach hprep.leafRefs.firstSize hn0
        hprep.leafRefs.firstReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hsymm hloop hgb heq hsent hpass
  have hreturn := (processnode_auto (ctx := ctx) (level := level)
    (numcells := ctx.n) (st := leaf) heq hsent (by simp) hpass).1
  have hearly : (processnode ctx level ctx.n leaf).1 <
      Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hbelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  obtain ⟨payload, hloc⟩ := hprep.guides.firstUnwind
    (numcells := ctx.n) hprep.trailOk
    hprep.firstPositive hbelow hgsz hprep.leafRefs.firstSize
    (isPerm_of_cellsReach hprep.leafRefs.firstSize hn0
      hprep.leafRefs.firstReach)
    hprep.searchOk.labSize
    (isPerm_of_cellsReach hprep.searchOk.labSize hn0
      hprep.searchOk.reach)
    hsymm hloop hgb heq hsent (by simp) hpass
  constructor
  · constructor
    · exact hreceipt
    · rw [hout]
      exact hevent
    · exact TrailExt.refl level trail
  · refine ⟨leaf.gcaFirst, ?_, hbelow, ?_⟩
    · rw [hout, hreturn]
    · rw [hout]
      exact ⟨payload, hloc⟩

/-- A discrete code-two row tie closes the complete node outcome for both
the canonical-guide and first-ancestor orbit return arms. -/
theorem NodeInv.tiedLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hcoset : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.cosetindex < ctx.n)
    (horbit : OrbSound (OrbConn (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList ctx.n)
      (processnode ctx level ctx.n
        (otherLeafSt ctx level numcells st)).2.orbits ctx.n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
    ∃ target,
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 =
        Int.ofNat target ∧
      target < level ∧
      ∃ payload : Unwind ctx tcLevel target
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 best,
        payload.Located trail := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcanonBelow : leaf.gcaCanon < level := by
    change (otherLeafSt ctx level numcells st).gcaCanon < level
    rw [RefTrail.otherLeaf_gcaCanon]
    exact hnode.canonBelow
  have hfirstBelow : leaf.gcaFirst < level :=
    Nat.lt_of_le_of_lt hlive'.order hcanonBelow
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, -, houtBest⟩ := hprep.tiedEvent rfl hn0 hgb
    hsymm hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hcc hge
    htie hcanonBelow hlive'
  rw [houtBest] at hevent
  have hrows : leafRows ctx leaf.canonlab = leafRows ctx leaf.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_tiedReceipt hnum hprep.guides hprep.trailOk
      hprep.canonPositive hcanonBelow hgsz hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hgb hrows hef hcc hge htie hprep.firstPositive hfirstBelow hcoset
      horbit
  have hreturns := (processnode_rowTie (ctx := ctx) (level := level)
    (numcells := ctx.n) (st := leaf) hef (by simp) hcc hge htie).1
  have hearly : (processnode ctx level ctx.n leaf).1 <
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_lt.mpr hfirstBelow
    · rw [hcanon]
      exact Int.ofNat_lt.mpr hcanonBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  obtain ⟨target, hreturn, hbelow, payload, hloc⟩ :=
    hprep.guides.tiedUnwind (numcells := ctx.n) hprep.trailOk
      hprep.canonPositive hcanonBelow hgsz hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hgb hrows hef (by simp) hcc hge htie hprep.firstPositive
      hfirstBelow hcoset horbit
  constructor
  · constructor
    · exact hreceipt
    · rw [hout]
      exact hevent
    · exact TrailExt.refl level trail
  · refine ⟨target, ?_, hbelow, ?_⟩
    · rw [hout]
      exact hreturn
    · rw [hout]
      exact ⟨payload, hloc⟩

/-- An early non-generator leaf absorbs its singleton subtree and returns
the explicit local-prune outcome. -/
theorem NodeInv.plainLeaf {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      outBest = some (incMax best
        (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  have hreturn : (processnode ctx level ctx.n leaf).1 ≤
      Int.ofNat level - 1 := Int.le_sub_one_iff.mpr hearly
  obtain ⟨bs', hevent, hmax⟩ := hprep.leafEvent rfl hn0 hgb hsymm
    hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hreturn hgen
    hlive'
  let outKey := incKey ctx bs'
    (processnode ctx level ctx.n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (processnode ctx level ctx.n leaf).2 numcells best (some outKey)
      (processnode ctx level ctx.n leaf).1 := by
    apply NodeReceipt.pruned (NodeSound.ofExact houtFull)
      (processnode ctx level ctx.n leaf).1 rfl hearly
    · apply processnode_installed hlevel
      apply Nat.ne_of_gt
      rw [hprep.codeInv.blen]
      cases bs with
      | nil => exact (hprep.bestCodes rfl).elim
      | cons _ _ => simp
    · simpa only [outKey] using hevent.read
    · exact houtFull
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  refine ⟨some outKey, ?_, houtFull⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hevent
  · exact TrailExt.refl level trail

/-- A non-generator leaf that does not unwind completes after the empty
child sweep and returns the exact singleton-subtree maximum. -/
theorem NodeInv.plainLeafDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u v, u < ctx.n → v < ctx.n →
      (ctx.g[u]!).testBit v = (ctx.g[v]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      outBest = some (incMax best
        (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
  subst n
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs ctx.n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf rfl hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf rfl hn0 hgb hsymm
    hloop hlevel hfull hcheap' hef (by simp)
  let outKey := incKey ctx bs'
    (processnode ctx level ctx.n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  let final := leafFinish ctx level
    (processnode ctx level ctx.n leaf).2
  have hread : stInc ctx final = some outKey := by
    change stInc ctx (leafFinish ctx level
      (processnode ctx level ctx.n leaf).2) = some outKey
    rw [stInc_leafFinish]
    simpa only [outKey] using hevent.read
  have hfinalEvent : EventOut G ctx tcLevel codes fs final
      (some outKey) trail (Int.ofNat level - 1) := by
    apply EventOut.intro level full bs' hevent.leafFinish hfull hstem
      (by omega)
    · omega
    · have hs := ReturnStab.leafFinish (ctx := ctx) (level := level)
        (hlive'.stable.ofGenTraceEq hgen)
      have hfirst : final.gcaFirst = leaf.gcaFirst := by
        unfold final Nauty.leafFinish
        split <;> simp only <;> split <;>
          exact (processnode_frames ctx level ctx.n leaf).2.2.2.2.2.2.1
      rw [hfirst]
      exact hs.lower (by omega)
    · exact (hlive'.history.processnode hprep.trailOk).leafFinish
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st final numcells best (some outKey)
      (Int.ofNat level - 1) := by
    apply NodeReceipt.complete (NodeSound.ofExact houtFull) rfl
    · exact canonlevel_ne_zero_of_stInc hread
    · exact hread
    · exact houtFull
  have hout := otherNode_leaf_done_state ctx inf tcLevel fuel level
    numcells st hnum hdone
  refine ⟨some outKey, ?_, houtFull⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hfinalEvent
  · exact TrailExt.refl level trail

/-! # Completed child sweeps -/

/-- An empty positive-fuel first-path sweep closes the coupled loop
outcome.  The comparison sign is explicit: a freshly prepared node may
enter its first child with sign one, whereas every state that reaches the
end of a real sweep has already absorbed a child and restored a
nonpositive sign. -/
theorem LoopInv.firstDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 index : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact firstLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell index
      cursor _ st best trail hinstalled hread hinv.cover hnext
  · simpa only [firstChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

/-- An empty positive-fuel off-path sweep closes the coupled loop outcome
with the same frozen-frame coverage and result event. -/
theorem LoopInv.otherDone {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tcell
      tv1 : Nat}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key} {base st : SearchSt}
    {best : Option Key}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : nextElem tcell cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact otherLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell cursor _
      st best trail hinstalled hread hinv.cover hnext
  · simpa only [otherChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

end Hex.GraphIso.Nauty
