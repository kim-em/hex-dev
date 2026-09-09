/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CanonScatter
public import HexGraphIso.Nauty.Policy.ExitBound
public import HexGraphIso.Nauty.Policy.Short
public import HexGraphIso.Nauty.Policy.Filters
public import HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.ExitBound
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Short
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.Fixed
import all HexGraphIso.Nauty.Policy.Scratch
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

/-! Short returns retain their emitting partition and workspace until a
loop consumes them. Explicit pairs use the frozen canonical ancestor to
justify the receiving fix test. -/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The leaf action of an actual prepared node returns to a strict ancestor. -/
theorem NodePre.leaf_bound {k : Nat} {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells target : Nat} {short : Bool} {st : Search n}
    (hin : NodePre G ctx tcLevel level numcells st) :
    let p := prepareOther ctx tcLevel level numcells st
    let c := classify ctx level p.1 p.2.2.2.2.2
    (leafExit c.1 level c.2).1 = .unwind target short → target < level := by
  intro p c he
  apply leafExit_bound (st := c.2) (leaf := c.1) ?_ ?_ ?_ he
  · have hg := (gcaPolicy ctx 0 tcLevel).classify level p.1 p.2.2.2.2.2
    change c.2.gcaFirst = p.2.2.2.2.2.gcaFirst at hg
    rw [hg]
    change (chooseTarget false ctx tcLevel level _ (compareCodes level _ _)).2.2.2.gcaFirst < level
    rw [chooseTarget_fields]
    have hc := (gcaPolicy ctx 0 tcLevel).compare level
      (visit ctx level numcells st).2.1 (visit ctx level numcells st).2.2
    change (compareCodes level _ _).gcaFirst = _ at hc
    rw [hc]
    exact hin.ancestor
  · change (classify ctx level p.1 p.2.2.2.2.2).2.gcaCanon < level
    rw [classify_canon]
    change (chooseTarget false ctx tcLevel level _ (compareCodes level _ _)).2.2.2.gcaCanon < level
    rw [target_canon, compare_canon]
    exact hin.canonAncestor
  · change (classify ctx level p.1 p.2.2.2.2.2).2.noncheaplevel ≤ level
    rw [classify_noncheap]
    change (chooseTarget false ctx tcLevel level _ (compareCodes level _ _)).2.2.2.noncheaplevel ≤ level
    rw [target_noncheap, compare_noncheap]
    exact hin.cheapBound

/-- An actual off-path node unwinds to a strict ancestor, including returns
transported from any number of descendant sweeps. -/
theorem NodePre.node_bound {k : Nat} {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells : Nat} {st : Search n}
    (hin : NodePre G ctx tcLevel level numcells st) (inf : Nat) :
    ∀ target short, (node false ctx inf tcLevel fuel level numcells st).1 =
      .unwind target short → target < level := by
  rw [node_eq_generic]
  cases fuel with
  | zero => simp [Generic.node]
  | succ fuel =>
    rw [Generic.node]
    apply Generic.bound_node (fuel := fuel) ?_ ctx tcLevel false level numcells st hin.positive
    · intro _
      dsimp only
      intro target short he
      exact hin.leaf_bound he
    · intro first level numcells tc tv1 cursor cell index st _
      exact Generic.sweep_bound first ctx inf tcLevel fuel (n + 1)
        level numcells tc tv1 cursor cell index st

/-- A first-path node needs only a positive level to bound its unwind;
its terminal return and its sweep both leave the node. -/
theorem first_node_bound (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) (hlevel : 1 ≤ level) :
    ∀ target short, (node true ctx inf tcLevel fuel level numcells st).1 =
      .unwind target short → target < level := by
  rw [node_eq_generic]
  cases fuel with
  | zero => simp [Generic.node]
  | succ fuel =>
    rw [Generic.node]
    apply Generic.bound_node (fuel := fuel) ?_ ctx tcLevel true level numcells st hlevel
    · intro he; cases he
    · intro first level numcells tc tv1 cursor cell index st _
      exact Generic.sweep_bound first ctx inf tcLevel fuel (n + 1)
        level numcells tc tv1 cursor cell index st

/-- A short return retains its emitting leaf's state, apart from the
fixed-point cleanup and first-path controls updated by enclosing loops. -/
def LeafReturn (target : Nat) (out : Search n) : Prop :=
  ∃ leaf level st, (∃ ctx numcells before, classify ctx level numcells before = (leaf, st)) ∧
    (leafExit leaf level st).1 = .unwind target true ∧
    out = { (leafExit leaf level st).2 with
      fixedpts := out.fixedpts, gcaFirst := out.gcaFirst, stabvertex := out.stabvertex }

/-- The nauty cleanup operations retain the state of a short return's origin. -/
theorem shortPolicy : Generic.ShortPolicy (n := n) (LeafReturn (n := n)) where
  leaf := by
    intro ctx level numcells before c target he
    exact ⟨c.1, level, c.2, ⟨ctx, numcells, before, rfl⟩, he, rfl⟩
  afterFirst := by
    intro level tv target out h
    obtain ⟨leaf, depth, st, hc, he, hs⟩ := h
    refine ⟨leaf, depth, st, hc, he, ?_⟩
    change afterChildFirst level tv out = _
    rw [hs]
    rfl

  leave := by
    intro tv target out h
    obtain ⟨leaf, depth, st, hc, he, hs⟩ := h
    refine ⟨leaf, depth, st, hc, he, ?_⟩
    change { out with fixedpts := out.fixedpts.erase tv } = _
    rw [hs]
    rfl

/-- The receiving loop reads the emitting leaf's admitted pair in its
own fields. Its target is the canonical ancestor for an explicit pair,
and is bounded by the cheap boundary's parent for an implicit pair. -/
theorem LeafReturn.admission {target : Nat} {out : Search n}
    (h : LeafReturn target out) (hcap : 0 < out.wsCap) :
    (out.autos.back? = some (fmperm out.workperm n) ∧ target = out.gcaCanon ∧
      out.workperm ∈ out.genTrace ∧
      (out.workperm.size = n → out.canonlab.size = n →
        out.canonlab.toList.Perm (List.range n) →
        ∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!)) ∨
      (out.autos.back? = some (fmptn out.lab out.ptn out.noncheaplevel n) ∧
        target ≤ out.noncheaplevel - 1) := by
  obtain ⟨leaf, level, st, ⟨ctx, numcells, before, hclass⟩, he, hs⟩ := h
  have hc := congrArg Search.wsCap hs
  change out.wsCap = (leafExit leaf level st).2.wsCap at hc
  rw [leafExit_capacity] at hc
  have hb := congrArg Search.autos hs
  change out.autos = (leafExit leaf level st).2.autos at hb
  rcases leafExit_short_pair (hc ▸ hcap) he with ⟨rfl, hp⟩ | ⟨ha, hp⟩
  · have hw : out.workperm = st.workperm :=
      (congrArg Search.workperm hs).trans (leafExit_workperm .autoCanon level st)
    have hcanon : out.canonlab = st.canonlab :=
      (congrArg Search.canonlab hs).trans (autoCanon_ref level st)
    have hlab : out.lab = st.lab :=
      (congrArg Search.lab hs).trans (leafExit_frame .autoCanon level st).1
    refine Or.inl ⟨?_, ?_, ?_, ?_⟩
    · rwa [hb, hw]
    · exact (leafExit_canon_target he).trans (congrArg Search.gcaCanon hs).symm
    · have ht := congrArg Search.genTrace hs
      change out.genTrace = (leafExit .autoCanon level st).2.genTrace at ht
      rw [ht, leafExit_trace, hw]
      simp
    · intro hwork hsize hperm
      have hm := classify_canon_out (ctx := ctx) (level := level) (numcells := numcells)
        (st := before) (by rw [hclass])
      rw [hclass] at hm
      simp only [hw, hcanon, hlab] at hwork hsize hperm ⊢
      exact hm hwork hsize hperm
  · have hl : out.lab = st.lab := (congrArg Search.lab hs).trans (leafExit_frame leaf level st).1
    have hptn : out.ptn = st.ptn := (congrArg Search.ptn hs).trans (leafExit_frame leaf level st).2.1
    have hn : out.noncheaplevel = st.noncheaplevel :=
      (congrArg Search.noncheaplevel hs).trans (leafExit_noncheap leaf level st)
    refine Or.inr ⟨?_, ?_⟩
    · rwa [hb, hl, hptn, hn]
    · rw [hn]
      exact leafExit_cheap_bound ha he

/-- At a receiving loop, an implicit pair frozen below the parent fixes
every vertex of the parent path, even before partition recovery. -/
theorem short_implicit_fix {k : Nat} {G : Colored n k}
    {level numcells : Nat} {base out : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells base) (hfixed : FixedCells level base)
    (hframe : SearchOut G level level base out) (hf : out.fixedpts = base.fixedpts)
    (hsaved : level ≤ out.noncheaplevel) :
    out.fixedpts.subset (fmptn out.lab out.ptn out.noncheaplevel n).1 = true := by
  have hsize : out.ptn.size = n := hframe.ptnSize.trans hok.ptnSize
  have hend := searchOk_end hn0 hok hlevel
  have hlow := hframe.low (base.ptn.size - 1) (Or.inl hend)
  have heout : out.ptn[out.ptn.size - 1]! ≤ level := by
    rw [hframe.ptnSize, hlow]
    exact hend
  exact (hfixed.ofEffect hf hframe).fmptn hsize heout hsaved

/-- A node's short-prune payload comes from an actual leaf emission,
including when the return crosses several intermediate loops. -/
theorem node_origin (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) {target : Nat}
    (he : (node first ctx inf tcLevel fuel level numcells st).1 = .unwind target true) :
    LeafReturn target (node first ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic] at he ⊢
  exact Generic.node_short shortPolicy first ctx inf tcLevel fuel level numcells st target he

/-- A sweep transports the emitting leaf's workspace and partition until
the target loop consumes the short-prune request. -/
theorem sweep_origin (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : Search n) {target : Nat}
    (he : (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 =
      .unwind target true) :
    LeafReturn target
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  rw [sweep_eq_generic] at he ⊢
  exact Generic.sweep_short shortPolicy first ctx inf tcLevel fuel cfuel level numcells tc tv1
    cursor cell index st target he

end Hex.GraphIso.Nauty
