/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Autos
public import HexGraphIso.Nauty.Invariant.Singleton
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

/-- Every vertex recorded as fixed occupies a singleton cell of the
current partition.  This is the executable path fact that makes erasing a
completed child's temporary fixed vertex restore its parent set exactly. -/
@[expose] def FixedCells (level : Nat) (st : SearchSt n) : Prop :=
  ∀ v, v < n → st.fixedpts.mem v = true →
    ∃ q, q < n ∧ st.lab[q]! = v ∧ IsCell st.ptn level q 1

namespace FixedCells

/-- A vertex in a non-singleton target cell is not already fixed. -/
theorem fresh {level tc len o : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hok : LabOk st.lab n)
    (hinj : LabInj st.lab n) (hsize : st.lab.size = n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    st.fixedpts.mem st.lab[tc + o]! = false := by
  rcases hm : st.fixedpts.mem st.lab[tc + o]! with _ | _
  · rfl
  · have hv : st.lab[tc + o]! < n := by
      exact hok (tc + o) (by omega)
    obtain ⟨q, hq, hqv, hsingle⟩ := h _ hv hm
    have heq : q = tc + o := by
      exact hinj q (tc + o) hq (by omega) hqv
    subst q
    rcases isCell_disj_or_eq hsingle hcell with heq | hleft | hright
    · omega
    · omega
    · omega

/-- Reordering vertices within unchanged cells preserves fixed
singletons. -/
theorem ofCellsPerm {level : Nat} {st out : SearchSt n}
    (h : FixedCells level st) (hfixed : out.fixedpts = st.fixedpts)
    (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab) :
    FixedCells level out := by
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
theorem ofEffect {G : Colored n k} {level : Nat} {st out : SearchSt n}
    (h : FixedCells level st) (hfixed : out.fixedpts = st.fixedpts)
    (heffect : SearchOut G level level st out) : FixedCells level out := by
  intro v hv hm
  rw [hfixed] at hm
  obtain ⟨q, hq, hqv, hc⟩ := h v hv hm
  exact ⟨q, hq, (heffect.atSingleton hc).trans hqv, isCell_of_low heffect.low hc⟩

/-- Fixed singleton cells are present in the implicit pair at every
deeper comparison level. -/
theorem fmptn {level saved : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) (hsaved : level ≤ saved) :
    st.fixedpts.subset (Nauty.fmptn st.lab st.ptn saved n).1 = true := by
  apply VSet.subset_iff.mpr
  intro v hv
  obtain ⟨q, hq, hqv, hc⟩ := h v (VSet.mem_lt hv) hv
  have hm := isCell_mem_cells (isCell_one_mono hc hsaved)
    (by rw [hsize]; exact Nat.le_refl _) (Nat.le_trans hend hsaved) hq
  have hm' : (q, q) ∈ cells st.ptn saved n := by simpa using hm
  have hf := fmptn_singleton (lab := st.lab) hm' (by rw [hqv]; exact VSet.mem_lt hv)
  rwa [hqv] at hf

/-- A parent-level search effect preserves fixed singletons between
valid partition states. -/
theorem ofSearchOut {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt n} (h : FixedCells level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (_hok : SearchOk G level numcells st)
    (_hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    FixedCells level out :=
  h.ofEffect hfixed heffect

/-- Refinement preserves every existing fixed singleton. -/
theorem refine {ctx : Ctx n} {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hsize : st.lab.size = n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    FixedCells level
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
theorem breakout {level tc len o : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hinj : LabInj st.lab n)
    (hsize : st.lab.size = n)
    (hpsize : st.ptn.size = n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    FixedCells (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  have hinjSize : LabInj st.lab st.lab.size := by
    rw [hsize]
    exact hinj
  intro v hv hm
  rw [VSet.mem_insert] at hm
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
    · exact (breakout_misses_singleton (n := n) (ptn := st.ptn)
        (level := level) hinjSize (by rw [hsize]; omega) hout).trans hqv
    · rw [breakout_ptn]
      exact isCell_set_miss hsingle hcell hlen
  · have heq : st.lab[tc + o]! = v :=
      beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hnew).1
    refine ⟨tc, by omega, ?_, ?_⟩
    · rw [breakout_at_target hinjSize (by rw [hsize]; omega), heq]
    · exact isCell_breakout_target (n := n) (lab := st.lab)
        (tv := st.lab[tc + o]!) (by rw [hpsize]; omega) hcell.2.1

end FixedCells

/-- Passing a fix test for a larger fixed set implies passing it for any
pointwise smaller set. -/
theorem fixTest_mono {small large fix : VSet n}
    (hsub : ∀ v, small.mem v = true → large.mem v = true)
    (hfix : large.subset fix = true) :
    small.subset fix = true :=
  VSet.subset_iff.mpr fun v hv => VSet.subset_iff.mp hfix v (hsub v hv)

/-- The bounded automorphism workspace is valid at the current frame for
every entry whose fixed set covers the current search path. -/
@[expose] def LocalAutos (ctx : Ctx n) (level : Nat) (st : SearchSt n) : Prop :=
  ∀ p ∈ st.autos.toList,
    st.fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2

namespace LocalAutos

/-- An empty workspace is locally valid. -/
theorem empty {ctx : Ctx n} {level : Nat} {st : SearchSt n}
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
theorem reindexPair {ctx : Ctx n} {ptn lab lab' : Array Nat}
    {level : Nat} {fix mcr : VSet n}
    (h : PairOk ctx.g ptn lab level fix mcr)
    (hperm : cellsPerm ptn level lab lab')
    (hpsize : ptn.size = n) (hsize : lab.size = n)
    (hsize' : lab'.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    PairOk ctx.g ptn lab' level fix mcr := by
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfix, hstab, hlt⟩ := h v hv hmcr
  exact ⟨gamma, hcheck, hfix,
    reindexStab hstab hperm hpsize hsize hsize' hend, hlt⟩

/-- Local ledger validity transports across unchanged partition cells and
a within-cell labelling permutation. -/
theorem ofCellsPerm {ctx : Ctx n} {level : Nat} {st out : SearchSt n}
    (h : LocalAutos ctx level st) (hautos : out.autos = st.autos)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = n) (hsize : st.lab.size = n)
    (hsize' : out.lab.size = n)
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
theorem breakout {ctx : Ctx n} {level tc len o : Nat} {st : SearchSt n}
    (h : LocalAutos ctx level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size) (hsize : st.lab.size = st.ptn.size)
    (hlab : LabOk st.lab n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    LocalAutos ctx (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  intro p hp hfix
  have hsub : ∀ v, st.fixedpts.mem v = true →
      (st.fixedpts.insert st.lab[tc + o]!).mem v = true := by
    intro v hv
    exact VSet.mem_insert_mono _ _ hv
  have hparent := fixTest_mono hsub hfix
  have hpair := h p hp hparent
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hpair v hv hmcr
  have hselected : p.1.mem st.lab[tc + o]! = true :=
    VSet.subset_iff.mp hfix _
      (VSet.mem_insert_self _ (hlab _ (by rw [hsize]; omega)))
  have hselectedBound : st.lab[tc + o]! < n :=
    hlab _ (by rw [hsize]; omega)
  exact ⟨gamma, hcheck, hfixes,
    cellStab_breakout (n := n) hstab hcell hrange hsize ho hlen hend hvals
      (hfixes _ hselectedBound hselected), hlt⟩

/-- The conditional local ledger is preserved by equitable refinement. -/
theorem refine {ctx : Ctx n} {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : LocalAutos ctx level st) (hgsz : ctx.g.size = n)
    (hsize : st.lab.size = n) (hlab : LabOk st.lab n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, active.mem v = true →
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
    cellStab_refine (n := n) hstab hgsz hcheck hsize hlab
      hpsize hend hstarts, hlt⟩

end LocalAutos

/-- A root-stabilizing checked automorphism that fixes every vertex on the
current individualized path stabilizes the current partition.  Keeping the
root frame explicit lets the existing root autos ledger supply the same
witness at every pruning site. -/
@[expose] def PathStab (ctx : Ctx n) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt n) : Prop :=
  ∀ gamma, checkAutom ctx.g gamma = true →
    CellStab rootPtn 1 rootLab gamma →
    (∀ u, u < n → st.fixedpts.mem u = true → gamma[u]! = u) →
    CellStab st.ptn level st.lab gamma

namespace PathStab

/-- A frame is its own path-stabilization seed. -/
theorem same {ctx : Ctx n} {st : SearchSt n} :
    PathStab ctx st.ptn st.lab 1 st := by
  intro gamma _ hstab _
  exact hstab

/-- Reordering the current labelling within unchanged cells preserves path
stabilization. -/
theorem ofCellsPerm {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st out : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = n) (hsize : st.lab.size = n)
    (hsize' : out.lab.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  intro gamma hcheck hroot hfix
  rw [hfixed] at hfix
  rw [hptn]
  exact LocalAutos.reindexStab (h gamma hcheck hroot hfix) hperm
    hpsize hsize hsize' hend

/-- A parent-level search effect preserves path stabilization when it
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt n}

    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  exact h.ofCellsPerm hfixed (heffect.ptnEq hok hout) heffect.perm
    hok.ptnSize hok.labSize hout.labSize hend

/-- Equitable refinement preserves path stabilization. -/
theorem refine {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hgsz : ctx.g.size = n)
    (hsize : st.lab.size = n) (hlab : LabOk st.lab n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro gamma hcheck hroot hfix
  exact cellStab_refine (n := n)
    (h gamma hcheck hroot hfix) hgsz hcheck hsize hlab hpsize
    hend hstarts

/-- Individualization extends path stabilization because an automorphism
fixing the enlarged path fixes the selected target vertex. -/
theorem breakout {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level tc len o : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size)
    (hsize : st.lab.size = st.ptn.size) (hlab : LabOk st.lab n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    PathStab ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  intro gamma hcheck hroot hfix
  have hparent : ∀ u, u < n → st.fixedpts.mem u = true →
      gamma[u]! = u := by
    intro u hu hm
    exact hfix u hu (VSet.mem_insert_mono _ _ hm)
  have hselected : gamma[st.lab[tc + o]!]! = st.lab[tc + o]! := by
    exact hfix _ (hlab _ (by rw [hsize]; omega))
      (VSet.mem_insert_self _ (hlab _ (by rw [hsize]; omega)))
  exact cellStab_breakout (n := n) (h gamma hcheck hroot hparent) hcell hrange
    hsize ho hlen hend hvals hselected

/-- The root autos ledger and path stabilization reconstruct the
conditional ledger consumed by the two pruning filters. -/
theorem toLocal {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hroot : AutosOk ctx.g rootPtn rootLab 1 st.autos) :
    LocalAutos ctx level st := by
  intro p hp hfix v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ :=
    hroot p hp v hv hmcr
  refine ⟨gamma, hcheck, hfixes, ?_, hlt⟩
  apply h gamma hcheck hstab
  intro u hu hmem
  exact hfixes u hu (VSet.subset_iff.mp hfix _ hmem)

end PathStab

/-- The two path facts carried by the mutual induction: fixed vertices are
singleton cells, and root-valid automorphisms fixing them stabilize the
current cells. -/
structure PathOk (ctx : Ctx n) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt n) : Prop where
  fixed : FixedCells level st
  stab : PathStab ctx rootPtn rootLab level st

namespace PathOk

/-- Node-entry refinement preserves both path facts. -/
theorem refine {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level : Nat} {active : VSet n} {numcells : Nat}
    {st : SearchSt n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n)
    (hok : SearchOk G level numcells st)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  have hend := searchOk_end hn0 hok hlevel
  have hlab : LabOk st.lab n := by
    intro i hi
    exact cellsReach_lt hok.reach i (by have := hok.labSize; omega)
  constructor
  · exact h.fixed.refine hok.labSize hok.ptnSize hend
  · exact h.stab.refine hgsz hok.labSize hlab hok.ptnSize
      hend hstarts

/-- Recovered parent state preserves both path facts once child cleanup
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : PathOk ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    PathOk ctx rootPtn rootLab level out := by
  constructor
  · exact h.fixed.ofSearchOut hfixed hok hout heffect
  · exact h.stab.ofSearchOut hfixed hok hout heffect
      (searchOk_end hn0 hok hlevel)

end PathOk

end Hex.GraphIso.Nauty
