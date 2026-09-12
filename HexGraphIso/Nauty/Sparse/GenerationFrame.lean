/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstContext
public import HexGraphIso.Nauty.Generation.Stabilizer
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- A true sparse automorphism fixing the individualized vertices
stabilizes the executed current partition. The raw array is interpreted
by the existing path invariant; no graph search is performed here. -/
theorem path_stab {G : GraphIso.Sparse.Colored n k} {level : Nat} {st : State n}
    (h : PathInv G level st) (hn : 0 < n) {p : Perm n}
    (hp : GraphIso.Sparse.IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v) :
    CellStab st.ptn level st.lab (renamingArray (renamingOf p)) := by
  have ha : Automorphism G (renamingArray (renamingOf p)) :=
    ⟨by simp [renamingArray], p, hp, fun v => by rw [renamingArray_get _ v.isLt, renamingOf_lt p v.isLt]⟩
  apply h.stab _ ha.checked (ha.colors hn)
  intro v hv hm
  rw [renamingArray_get _ hv, renamingOf_lt p hv, hfix ⟨v, hv⟩ hm]

/-- The true point stabilizer preserves every current target cell. -/
theorem window_stable {G : GraphIso.Sparse.Colored n k} {level tc len : Nat} {st : State n}
    (h : PathInv G level st) (hlab : LabOk st.lab n) (hc : IsCell st.ptn level tc len)
    (hr : tc + len ≤ st.lab.size) {p : Perm n} (hp : GraphIso.Sparse.IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v)
    (v : Fin n) (hv : (windowSet n st.lab tc len).mem v.val = true) :
    (windowSet n st.lab tc len).mem (p.get v).val = true := by
  have hn : 0 < n := by have := v.isLt; omega
  have hh := windowSet_carry (path_stab h hn hp hfix) hc hr hlab hv
  rwa [renamingArray_get _ v.isLt, renamingOf_lt p v.isLt] at hh

/-- A discrete reached partition has trivial point stabilizer. This
provides the terminal case for generation along the actual first path. -/
theorem terminal {G : GraphIso.Sparse.Colored n k} {level : Nat} {st : State n}
    (h : PathInv G level st) (hr : Ready G level n st) (hn : 0 < n) (hl : 1 ≤ level)
    {p : Perm n} (hp : GraphIso.Sparse.IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v) : p = Perm.id n := by
  have hs := path_stab h hn hp hfix
  have hd : discreteAt st.ptn level n = true :=
    (discreteAt_iff_bcount hr.ok.ptnSize.symm (searchOk_end hn hr.ok hl)).mpr hr.ok.count.symm
  have hf := Nauty.Generation.discrete_fixes hs hr.ok.labSize
    (isPerm_of_cellsReach hr.ok.labSize hn hr.ok.reach) hr.ok.ptnSize (searchOk_end hn hr.ok hl) hd
  apply Perm.ext
  intro v
  have he := hf v.val v.isLt
  rw [renamingArray_get _ v.isLt, renamingOf_lt p v.isLt] at he
  simpa only [Perm.get_id] using (Fin.ext he : p.get v = v)

/-- An actual first discrete visit generates the whole remaining point
stabilizer with the empty word, since every such automorphism is identity. -/
theorem first_terminal {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Max.Frame n} {parents : Max.Parents n} (h : Max.FirstInput G tcLevel f parents)
    (hd : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1 = n)
    {base : List (Fin n)} (hbase : ∀ b : Fin n, f.entry.fixedpts.mem b.val = true ↔ b ∈ base)
    {gs : List (Perm n)} {p : Perm n} (hp : GraphIso.Sparse.IsIso G G p) (hfix : Perm.Fixes base p) :
    Perm.Generated gs p := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hr := (h.entry.frame.node.prepare (tcLevel := tcLevel) hn h.entry.frame.positive).1
  have hr' : Ready G f.level n r.2.2.2.2 := by rw [hd] at hr; exact hr
  have hpath : PathInv G f.level r.2.2.2.2 :=
    ((h.path.visit h.entry.frame.node).record (f.code G.graph)).target true tcLevel r.1
  have he := terminal hpath hr' hn h.entry.frame.positive hp (fun v hv => by
    apply hfix v ((hbase v).mp ?_)
    have hf : r.2.2.2.2.fixedpts = f.entry.fixedpts :=
      target_fixed true (.ofGraph G.graph) tcLevel f.level r.1
        (recordFirst f.level (f.code G.graph) (visit (.ofGraph G.graph) f.level f.numcells f.entry).2.2)
    rwa [← hf])
  rw [he]
  exact .id

end Hex.GraphIso.Nauty.Sparse.Generation
