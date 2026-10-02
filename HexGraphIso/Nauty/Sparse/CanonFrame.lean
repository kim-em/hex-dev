/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Reach
public import HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Canonical-reference provenance for the native state. Only partition,
label and ancestor fields enter this shared proof predicate. -/
abbrev CanonOut (level : Nat) (st out : State n) : Prop :=
  Nauty.CanonOut level st.frame out.frame

namespace CanonOut

variable {level : Nat} {st mid out : State n}

theorem refl (level : Nat) (st : State n) : CanonOut level st st :=
  Nauty.CanonOut.refl level st.frame

theorem fields (h : CanonOut level st mid) (hc : out.canonlab = mid.canonlab)
    (hg : out.gcaCanon = mid.gcaCanon) : CanonOut level st out :=
  Nauty.CanonOut.fields h hc hg

theorem trans {G : GraphIso.Sparse.Colored n k} (h : CanonOut level st mid)
    (hnext : CanonOut level mid out) (hf : FrameOut G level level st mid) : CanonOut level st out :=
  Nauty.CanonOut.trans h hnext hf.effect

/-- Actual cached refinement transports the reference to its entry cells.
The proof uses native label permutations and literal preserved boundaries. -/
theorem visit {G : GraphIso.Sparse.Colored n k} {numcells : Nat}
    (hi : NodeInv G level numcells st)
    (h : CanonOut level (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 out) :
    CanonOut level st out := by
  let r := (Sparse.visit (.ofGraph G.graph) level numcells st).2.2
  have hend : st.ptn[n - 1]! ≤ level := by simpa only [hi.spec.node.ptnSize] using hi.spec.node.ptnEnd
  have ht := refineWith_state G.graph level st.lab st.ptn st.active numcells st.canong.scratch
    hi.spec.label hi.spec.node.ptnSize hend hi.spec.node.starts hi.scratch
  have hrs : r.lab.size = n := by
    have hp : r.lab.toList.Perm (List.range n) := ht.1
    simpa only [Array.length_toList, List.length_range] using hp.length_eq
  have hps : r.ptn.size = n := ht.2.1
  have hclosed : ∀ q, st.ptn[q]! ≤ level → r.ptn[q]! = st.ptn[q]! := ht.2.2.1.closed
  have hlast : r.ptn[r.ptn.size - 1]! ≤ level := by rw [hps, hclosed _ hend]; exact hend
  apply Nauty.CanonOut.lift (st := st.frame) (mid := r.frame) h (Nat.le_refl _) rfl rfl
    (hrs.trans hi.spec.node.labSize.symm) (cellsPerm_symm ht.2.2.2.1)
  intro lab hsize hperm
  exact cellsPerm_coarsen (hi.spec.node.ptnSize.trans hps.symm) (hrs.trans hps.symm)
    (hsize.trans (hrs.trans hps.symm)) hperm hlast hi.spec.node.ptnEnd
    (fun q hq => by rw [hclosed q hq]; exact hq)

/-- Native individualization uses the shared breakout literally; its
newly stored reference therefore lies in the parent's ordered cells. -/
theorem child {G : GraphIso.Sparse.Colored n k} {numcells tc tv : Nat} {cell : VSet n}
    (first : Bool) (hn : 0 < n) (hl : 1 ≤ level) (hi : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (h : CanonOut (level + 1) ((policy (n := n)).child first level tc tv st) out) :
    CanonOut level st out := by
  change Nauty.CanonOut (level + 1) _ _ at h
  rw [State.child_frame] at h
  exact Nauty.CanonOut.child (ctx := Graph.context G.graph) first hn hl hi.ok ht hv h

/-- The actual parent recovery clamps the ancestor while retaining its label. -/
theorem recover (h : CanonOut level st out) (inf : Nat) :
    CanonOut level st ((policy (n := n)).recover inf level out) := by
  change Nauty.CanonOut level st.frame _
  rw [State.recover_frame, ← recover_eq]
  exact Nauty.CanonOut.recover h inf

theorem afterSweep (h : CanonOut level st out) (first : Bool) (size index : Nat) :
    CanonOut level st ((policy (n := n)).afterSweep first level size index out) := by
  change CanonOut level st (if first then { Nauty.afterSweep first level size index out with
    order := (Nauty.afterSweep first level size index out).order * index }
    else Nauty.afterSweep first level size index out)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.fields rfl rfl

end CanonOut

/-- Leaf installation is the only native leaf action that raises the
canonical ancestor or replaces the reference by the current label. -/
theorem canon_leaf (leaf : Leaf) (level : Nat) (st : State n) :
    CanonOut level st (leafExit leaf level st).2 := by
  dsimp only [CanonOut, State.frame]
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact ⟨Nat.min_le_right _ _, Or.inl ⟨Nat.le_refl _, rfl⟩⟩
    | exact ⟨by change min level st.gcaCanon ≤ _; rw [admit_canon]; exact Nat.min_le_right _ _,
        Or.inl ⟨Nat.le_of_eq (admit_canon _), (admit_frame _).2.2.2⟩⟩
    | exact ⟨by change min level st.gcaCanon ≤ _; rw [pruneReturn_canon]; exact Nat.min_le_right _ _,
        Or.inl ⟨Nat.le_of_eq (pruneReturn_canon level _), (pruneReturn_frame level _).2.2.2⟩⟩
    | exact ⟨by change min level st.gcaCanon ≤ _; rw [pruneReturn_canon]; exact Nat.min_le_left _ _,
        Or.inr ⟨by change level ≤ _; rw [pruneReturn_canon]; exact Nat.le_refl _,
          congrArg Array.size (pruneReturn_frame level _).2.2.2,
          by change cellsPerm st.ptn level st.lab _; rw [(pruneReturn_frame level _).2.2.2]
             exact cellsPerm_refl _ _ _⟩⟩

end Hex.GraphIso.Nauty.Sparse
