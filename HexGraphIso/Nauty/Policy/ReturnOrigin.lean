/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Short
public import HexGraphIso.Nauty.Policy.Filters
public import HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Short
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.Fixed
import all HexGraphIso.Nauty.Policy.Scratch
import all HexGraphIso.Nauty.Search.Engine

public section

/-! Short returns retain their emitting partition and workspace until a
loop consumes them. Explicit pairs use the frozen canonical ancestor to
justify the receiving fix test. -/

namespace Hex.GraphIso.Nauty.Engine

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

/-- A short return retains its emitting leaf's state, apart from the
fixed-point cleanup and first-path controls updated by enclosing loops. -/
def LeafReturn (target : Nat) (out : Search n) : Prop :=
  ∃ leaf level st, (leafExit leaf level st).1 = .unwind target true ∧
    out = { (leafExit leaf level st).2 with
      fixedpts := out.fixedpts, gcaFirst := out.gcaFirst, stabvertex := out.stabvertex }

/-- The nauty cleanup operations retain the state of a short return's origin. -/
theorem shortPolicy : Generic.ShortPolicy (n := n) (LeafReturn (n := n)) where
  leaf leaf level st target he := ⟨leaf, level, st, he, rfl⟩
  afterFirst := by
    intro level tv target out h
    obtain ⟨leaf, depth, st, he, hs⟩ := h
    refine ⟨leaf, depth, st, he, ?_⟩
    change afterChildFirst level tv out = _
    rw [hs]
    rfl

  leave := by
    intro tv target out h
    obtain ⟨leaf, depth, st, he, hs⟩ := h
    refine ⟨leaf, depth, st, he, ?_⟩
    change { out with fixedpts := out.fixedpts.erase tv } = _
    rw [hs]
    rfl

/-- The receiving loop reads the emitting leaf's admitted pair in its
own fields. Its target is the canonical ancestor for an explicit pair,
and is bounded by the cheap boundary's parent for an implicit pair. -/
theorem LeafReturn.admission {target : Nat} {out : Search n}
    (h : LeafReturn target out) (hcap : 0 < out.wsCap) :
    (out.autos.back? = some (fmperm out.workperm n) ∧ target = out.gcaCanon) ∨
      (out.autos.back? = some (fmptn out.lab out.ptn out.noncheaplevel n) ∧
        target ≤ out.noncheaplevel - 1) := by
  obtain ⟨leaf, level, st, he, hs⟩ := h
  have hc := congrArg Search.wsCap hs
  change out.wsCap = (leafExit leaf level st).2.wsCap at hc
  rw [leafExit_capacity] at hc
  have hb := congrArg Search.autos hs
  change out.autos = (leafExit leaf level st).2.autos at hb
  rcases leafExit_short_pair (hc ▸ hcap) he with ⟨rfl, hp⟩ | ⟨ha, hp⟩
  · have hw : out.workperm = st.workperm :=
      (congrArg Search.workperm hs).trans (leafExit_workperm .autoCanon level st)
    refine Or.inl ⟨?_, ?_⟩
    · rwa [hb, hw]
    · exact (leafExit_canon_target he).trans (congrArg Search.gcaCanon hs).symm
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
    (hok : SearchOk G level numcells base.view) (hfixed : FixedCells level base.view)
    (hframe : SearchOut G level level base.view out.view) (hf : out.fixedpts = base.fixedpts)
    (hsaved : level ≤ out.noncheaplevel) :
    out.fixedpts.subset (fmptn out.lab out.ptn out.noncheaplevel n).1 = true := by
  have hsize : out.view.ptn.size = n := hframe.ptnSize.trans hok.ptnSize
  have hend := searchOk_end hn0 hok hlevel
  have hlow := hframe.low (base.view.ptn.size - 1) (Or.inl hend)
  have heout : out.view.ptn[out.view.ptn.size - 1]! ≤ level := by
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

/-- An actual off-path child supplies its newest pair to the receiving
loop. An implicit pair already satisfies that loop's fix test; an explicit
pair identifies its target for the canonical-ancestor argument. -/
theorem SweepPre.short_admission {k : Nat} {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv target : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n)
    (he : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2)
    (hreceive : level ≤ target) :
    let raw := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    (out.autos.back? = some (fmperm out.workperm n) ∧ target = out.gcaCanon) ∨
      (out.autos.back? = some (fmptn out.lab out.ptn out.noncheaplevel n) ∧
        out.fixedpts.subset (fmptn out.lab out.ptn out.noncheaplevel n).1 = true) := by
  intro raw out
  have htv := h.cursor_mem tv rfl
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    h.positive h.partition h.target htv
  dsimp only [policy, Generic.Policy.child] at hch
  have hfx := fixed_child first hn0 h.partition h.path.fixed h.target htv
  have hr := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0
    (by omega) hch.1
  have hf := node_fixed (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0
    (by omega) hch.1 hfx.2
  have hframe := hch.2 _ (by simpa only [Nat.add_sub_cancel] using hr)
  have hout : SearchOut G level level st.view out.view := hframe.congr rfl rfl rfl rfl
  have hfixed : out.fixedpts = st.fixedpts := by
    apply fixed_restore (base := st) (out := raw) ?_ hfx.1
    exact hf.trans (by cases first <;> rfl)
  have horigin : LeafReturn target out := shortPolicy.leave tv target raw
    (node_origin false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) he)
  rcases horigin.admission hi.workspace.1 with ha | ⟨hb, ht⟩
  · exact Or.inl ha
  · exact Or.inr ⟨hb,
      short_implicit_fix hn0 h.positive h.partition h.path.fixed hout hfixed (by omega)⟩

end Hex.GraphIso.Nauty.Engine
