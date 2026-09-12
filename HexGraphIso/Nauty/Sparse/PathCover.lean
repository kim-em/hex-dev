/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ChildPath
public import HexGraphIso.Nauty.Sparse.RefinedSmall
public import HexGraphIso.Nauty.Generation.VisitCover
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- Coverage of a native reference carrying its saved uniformity boundary.
The abstract ledger accounts for visited children and descending filters;
its occurrence predicate describes native sparse child calls. -/
abbrev PathCover (G : Hex.SparseGraph n) (tcLevel boundary level : Nat) (st : RefineSt n)
    (tc len : Nat) (targets : List Nat) (key : Key n) (cell : VSet n)
    (cursor : Option Nat) : Prop :=
  Nauty.Generation.VisitCover (ChildPath G tcLevel boundary level st tc targets key)
    st.lab tc len cell cursor

namespace PathCover

variable {G : Hex.SparseGraph n} {tcLevel boundary level tc len : Nat} {st : RefineSt n}
  {targets : List Nat} {key : Key n} {cell cell' : VSet n} {cursor : Option Nat}

theorem start (hlab : ∀ o, o < len → st.lab[tc + o]! < n) :
    PathCover G tcLevel boundary level st tc len targets key (windowSet n st.lab tc len) none :=
  Nauty.Generation.VisitCover.start hlab

theorem advance (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    {tv : Nat} (hnext : cell.nextElem cursor = some tv)
    (hcur : ∀ o, o < len → st.lab[tc + o]! = tv →
      ¬ ChildPath G tcLevel boundary level st tc targets key o) :
    PathCover G tcLevel boundary level st tc len targets key cell (some tv) :=
  Nauty.Generation.VisitCover.advance h hnext hcur

/-- A removed child retains its reference in a strictly smaller original
child; previous removals are handled by the shared well-founded ledger. -/
theorem filterDesc (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    (hstep : ∀ o, ChildLive st.lab tc len cell cursor o →
      cell'.mem st.lab[tc + o]! = true ∨ ∃ j, j < len ∧
        ChildPath G tcLevel boundary level st tc targets key o =
          ChildPath G tcLevel boundary level st tc targets key j ∧ st.lab[tc + j]! < st.lab[tc + o]!)
    (hsub : ∀ v, cell'.mem v = true → cell.mem v = true) :
    PathCover G tcLevel boundary level st tc len targets key cell' cursor :=
  Nauty.Generation.VisitCover.filterDesc h hstep hsub

/-- Checked cell stabilizers preserve the full native reference, including
all target positions, codes and boundary uniformity. -/
theorem filterAutom (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (hdrop : ∀ o, ChildLive st.lab tc len cell cursor o →
      cell'.mem st.lab[tc + o]! = false → ∃ gamma, checkAutom (Graph.context G).g gamma = true ∧
        CellStab st.ptn level st.lab gamma ∧ gamma[st.lab[tc + o]!]! < st.lab[tc + o]!)
    (hsub : ∀ v, cell'.mem v = true → cell.mem v = true) :
    PathCover G tcLevel boundary level st tc len targets key cell' cursor := by
  have hmem := mem_cells_of_isCell (nn := n) (Nat.le_of_eq hr.spec.node.ptnSize.symm)
    hr.spec.node.ptnEnd hc (by omega) (by rw [hr.spec.node.ptnSize]; exact hb)
  apply Nauty.Generation.VisitCover.filterAutom (st := st.toPartition) h hr.iter hmem
    (by omega) (by omega) ?_ hdrop hsub
  intro gamma o j hcheck hstab ho hj hmove
  exact ChildPath.carried hr hc hb hn ho hj hcheck hstab hmove

/-- The literal long-prune filter preserves reference coverage using its
checked active pairs. The frozen state is interpreted only for proofs. -/
theorem longprune (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    {fixedpts : VSet n} {autos : Array (VSet n × VSet n)}
    (haut : ∀ p ∈ autos.toList, fixedpts.subset p.1 = true →
      PairOk (Graph.context G).g st.ptn st.lab level p.1 p.2) :
    PathCover G tcLevel boundary level st tc len targets key
      (Nauty.longprune cell fixedpts autos) cursor := by
  apply filterAutom h hr hc hb hn ?_ (fun _ hm => longprune_subset hm)
  intro o ho hm
  exact longprune_drop (perm_bound hr.spec.label (by have := ho.1; omega)) ho.2.1 hm haut

/-- The literal short-prune filter preserves reference coverage, including
an implicit pair, when its receiver contract supplies pair validity. -/
theorem shortprune (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) {out : State n}
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk (Graph.context G).g st.ptn st.lab level fix mcr) :
    PathCover G tcLevel boundary level st tc len targets key (Nauty.shortprune cell out) cursor := by
  apply filterAutom h hr hc hb hn ?_ (fun _ hm => shortprune_subset (st := out.frame) hm)
  intro o ho hm
  exact shortprune_drop (st := out.frame) (perm_bound hr.spec.label (by have := ho.1; omega))
    ho.2.1 hm hlast

theorem finish (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    (hnext : cell.nextElem cursor = none) :
    ∀ o, o < len → ¬ ChildPath G tcLevel boundary level st tc targets key o :=
  Nauty.Generation.VisitCover.finish h hnext

/-- An earlier original child cannot retain a reference, even after an
older filter removed it from the live target set. -/
theorem smaller (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    {tv o : Nat} (hnext : cell.nextElem cursor = some tv)
    (ho : o < len) (hlt : st.lab[tc + o]! < tv) :
    ¬ ChildPath G tcLevel boundary level st tc targets key o :=
  Nauty.Generation.VisitCover.smaller h hnext ho hlt

/-- A recorded stabilizing carrier transfers reference absence to the
current child, including an interrupted child that was not exhausted. -/
theorem carrier (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    {tv oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : cell.nextElem cursor = some tv) (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (href : oRef < len) (habsent : ¬ ChildPath G tcLevel boundary level st tc targets key oRef)
    (hcarrier : CellCarrier (Graph.context G) st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    PathCover G tcLevel boundary level st tc len targets key cell (some tv) := by
  apply Nauty.Generation.VisitCover.carrier h hnext (by omega) href habsent hcarrier hatRef hatCur
  intro gamma o j hcheck hstab ho hj hmove
  exact ChildPath.carried hr hc hb hn ho hj hcheck hstab hmove

/-- A carrier from an earlier child advances the absence ledger using
the ranked reference coverage retained through all previous filters. -/
theorem reference (h : PathCover G tcLevel boundary level st tc len targets key cell cursor)
    {tv oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : cell.nextElem cursor = some tv) (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (href : oRef < len) (hearlier : st.lab[tc + oRef]! < tv)
    (hcarrier : CellCarrier (Graph.context G) st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    PathCover G tcLevel boundary level st tc len targets key cell (some tv) :=
  carrier h hnext hr hc hb hn href (smaller h hnext href hearlier) hcarrier hatRef hatCur

end PathCover
end Hex.GraphIso.Nauty.Sparse.Generation
