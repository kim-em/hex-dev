/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Shape
public import HexGraphIso.Nauty.Policy.Boundary
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The small-cell shape descends through the actual individualized
child and its refinement; it depends only on the parent partition. -/
theorem child_shape {G : Colored n k} {ctx : Ctx n} {level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hshape : NodeShape n level st.ptn) :
    NodeShape n (level + 1)
      ((child first level tc tv st).refined ctx (level + 1) (numcells + 1)).ptn := by
  let r : RefineSt n := ⟨st.lab, st.ptn, st.active, numcells, 0, 0, 0⟩
  have hi : IterOk ctx level r := hok.iter hn0 hlevel rfl rfl
  have hchild := (reachPolicy G ctx 0 hn0).child first level numcells tc tv cell st
    hlevel hok htarget htv
  have hlevel' : level < n := by
    have := hchild.1.bc
    have := bcount_le (Generic.Policy.child (n := n) first level tc tv st).ptn (level + 1) n
    omega
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨hc, hlen, hrange⟩ := hcell (mem_ne_empty htv)
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hmem tv htv)
  have hm : (tc, tc + len - 1) ∈ cells r.ptn level n :=
    isCell_mem_cells hc (Nat.le_of_eq hok.ptnSize.symm) (searchOk_end hn0 hok hlevel) (by omega)
  have hs := nodeShape_child (o := o) hi hlevel' hm (by omega) (by omega) hshape
  change st.lab[tc + o]! = tv at hv
  change NodeShape n (level + 1) (childSt ctx level r tc st.lab[tc + o]!).ptn at hs
  rw [hv] at hs
  cases first <;> exact hs

/-- An off-path sweep retaining a cheap boundary has passed its actual
cheap-cell test at the current partition. -/
theorem cheap_shape {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (heq : Equitable ctx level st.lab st.ptn)
    (hcheap : (cheapCheck false level st).noncheaplevel ≤ level) : NodeShape n level st.ptn := by
  have hguard : cheapautom st.ptn level n = true := by
    unfold cheapCheck at hcheap
    cases hg : cheapautom st.ptn level n with
    | true => rfl
    | false =>
      simp only [Bool.not_false, Bool.true_or, hg, Bool.and_self, ite_true] at hcheap
      omega
  let r : RefineSt n := ⟨st.lab, st.ptn, st.active, numcells, 0, 0, 0⟩
  exact (subtreeOk_of_cheapautom (r := r) (hok.iter hn0 hlevel rfl rfl) heq hok.count.symm hguard).shape

/-- Recovery retains a parent's small-cell shape whenever the returning
child has not replaced its saved boundary by a deeper one. -/
theorem recover_shape {G : Colored n k} {level numcells : Nat} {st out : Search n}
    (hok : SearchOk G level numcells st)
    (hout : SearchOut G level level st out)
    (hs : st.noncheaplevel ≤ level → NodeShape n level st.ptn)
    (hb : out.noncheaplevel = st.noncheaplevel ∨ level + 1 ≤ out.noncheaplevel)
    (hr : (recoverLevels level (recoverPtn (n + 2) level out)).noncheaplevel ≤ level) :
    NodeShape n level (recoverLevels level (recoverPtn (n + 2) level out)).ptn := by
  rw [recover_ptn_eq hok hout]
  apply hs
  rw [recover_noncheap] at hr
  split at hr <;> omega

end Hex.GraphIso.Nauty
