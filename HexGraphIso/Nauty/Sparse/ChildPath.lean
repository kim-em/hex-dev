/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefPath
public import HexGraphIso.Nauty.Sparse.ReadyPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- A reference occurrence in a frozen native child. Fresh scratch fixes
the witness state; `ChildPath.reorder` transfers it to the exact cached
child used by a recovered search frame. -/
@[expose] def ChildPath (G : Hex.SparseGraph n) (tcLevel boundary level : Nat)
    (st : RefineSt n) (tc : Nat) (targets : List Nat) (key : Key n) (o : Nat) : Prop :=
  RefPath G tcLevel boundary (level + 1)
    (st.child (.ofGraph G) level tc st.lab[tc + o]! (Scratch.fresh n)) targets key

namespace ChildPath

/-- Cell reordering and independent bounded scratch preserve the entire
reference occurrence, including its saved uniformity boundary. -/
theorem reorder {G : Hex.SparseGraph n} {tcLevel boundary level tc len a b : Nat}
    {s t : RefineSt n} {targets : List Nat} {key : Key n} {scratch : Scratch}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready G level t)
    (hp : t.ptn = s.ptn) (he : cellsPerm s.ptn level t.lab s.lab)
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len) (hsc : Scratch.Bounded n scratch)
    (hmove : t.lab[tc + b]! = s.lab[tc + a]!) :
    ChildPath G tcLevel boundary level s tc targets key a ↔
      RefPath G tcLevel boundary (level + 1)
        (t.child (.ofGraph G) level tc t.lab[tc + b]! scratch) targets key := by
  have hid : (renamingOf (Perm.id n)).toFun = id := by
    funext v
    simp [renamingOf]
  have hm : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [hid, Array.map_id]
    exact he
  have hc' : IsCell t.ptn level tc len := by rw [hp]; exact hc
  have hnc : t.numcells = s.numcells := by rw [ht.spec.count, hs.spec.count, hp]
  have hf : Scratch.Bounded n (Scratch.fresh n) :=
    (Scratch.fresh_valid n s.lab s.ptn (level + 1)).toBounded
  have hchild := child_equiv G G (Perm.id n) (by simp) hs ht hp hnc hm
    hc hb hn ha hb' (Scratch.fresh n) scratch hf hsc (by simpa only [hid, id_eq] using hmove)
  exact RefPath.map_iff G G (Perm.id n) (by simp)
    (hs.child hc hb hn ha _ hf) (ht.child hc' hb hn hb' _ hsc) hchild

/-- The frozen occurrence is equivalent to the same chosen child with
the actual bounded scratch supplied by the executable. -/
theorem cached {G : Hex.SparseGraph n} {tcLevel boundary level tc len o : Nat}
    {st : RefineSt n} {targets : List Nat} {key : Key n} {scratch : Scratch}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ho : o < len) (hs : Scratch.Bounded n scratch) :
    ChildPath G tcLevel boundary level st tc targets key o ↔
      RefPath G tcLevel boundary (level + 1)
        (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) targets key :=
  reorder hr hr rfl (cellsPerm_refl _ _ _) hc hb hn ho ho hs rfl

/-- Every checked stabilizer carries frozen child occurrences in both
directions, without a generation-completeness hypothesis. -/
theorem carried {G : Hex.SparseGraph n} {tcLevel boundary level tc len a b : Nat}
    {st : RefineSt n} {targets : List Nat} {key : Key n} {gamma : Array Nat}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len)
    (hcheck : checkAutom (Graph.context G).g gamma = true)
    (hstab : CellStab st.ptn level st.lab gamma)
    (hmove : gamma[st.lab[tc + a]!]! = st.lab[tc + b]!) :
    ChildPath G tcLevel boundary level st tc targets key a ↔
      ChildPath G tcLevel boundary level st tc targets key b := by
  have hf := (Scratch.fresh_valid n st.lab st.ptn (level + 1)).toBounded
  exact RefPath.carried_iff hr hc hb hn ha hb' hf hf hcheck hstab hmove

end ChildPath
end Hex.GraphIso.Nauty.Sparse.Generation
