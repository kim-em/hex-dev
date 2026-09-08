/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPush
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.FilterCover
import all HexGraphIso.Nauty.Policy.ShortPair
import all HexGraphIso.Nauty.Policy.ChildFrame
import all HexGraphIso.Nauty.Policy.CanonRef
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Advancing the executable cursor retains exactly the larger survivors. -/
theorem Remaining.next {cell : VSet n} {tv v : Nat} :
    Remaining (cell.nextElem (some tv)) cell v ↔ cell.mem v = true ∧ tv < v := by
  constructor
  · rintro ⟨hv, w, hw, hwv⟩
    have hh := (VSet.nextElem_some hw).2.1
    change tv + 1 ≤ w at hh
    exact ⟨hv, by omega⟩
  · rintro ⟨hv, htv⟩
    cases he : cell.nextElem (some tv) with
    | none =>
      have hh := VSet.nextElem_none he v (by change tv + 1 ≤ v; omega)
      rw [hv] at hh
      cases hh
    | some w =>
      refine ⟨hv, w, rfl, ?_⟩
      by_cases hn : w ≤ v
      · exact hn
      · have hh := (VSet.nextElem_some he).2.2 v (by change tv + 1 ≤ v; omega) (by omega)
        rw [hv] at hh
        cases hh

/-- Reception uses the child's coverage clause at precisely its stop
level, then absorbs that child into the sweep's prior coverage. -/
theorem SweepInput.received {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hr : let p : Parent n := ⟨l, st, tv, bs, fs⟩
      Generic.Result ((p.child ctx tcLevel).key ctx tcLevel)
        ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) level
        (Witness ctx tcLevel ((parents.push p).frames ctx tcLevel)) (.unwind level short)) :
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (fun v => Remaining (some tv) cell v ∧ tv < v) (out.best ctx) := by
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hg := hr.bounded.grows
  have hb : (p.child ctx tcLevel).entry.key ctx bs = st.key ctx bs := by
    dsimp only [p, Parent.child]
    cases hf : l.first <;> rfl
  change Generic.Grows ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) at hg
  rw [hb] at hg
  have hc : Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) (out.best ctx) := by
    simpa only [Generic.ExitCover, ↓reduceIte] using hr.coverage.2
  rw [p.key h.suspend] at hc
  change Generic.Covers (l.key ctx tcLevel tv) (out.best ctx) at hc
  dsimp only [Loop.key] at hc
  rw [← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hc
  apply (h.coverage.grow hg).visit (tv := tv) ?_ hc
  rintro v ⟨_, w, hw, hv⟩
  cases hw
  exact hv

/-- A local pair valid in the sweep's current ordering is also valid
in its frozen ordering, with the same carrier and fixed vertices. -/
theorem SweepInput.pair {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 index : Nat} {cursor : Option Nat}
    {cell fix mcr : VSet n} {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 cursor cell index
      st l bs fs parents) (hp : PairOk ctx.g st.ptn st.lab level fix mcr) :
    PairOk ctx.g (l.prepare ctx tcLevel).2.2.2.2.ptn
      (l.prepare ctx tcLevel).2.2.2.2.lab level fix mcr := by
  intro v hv hm
  obtain ⟨γ, ha, hf, hs, hlt⟩ := hp v hv hm
  refine ⟨γ, ha, hf, ?_, hlt⟩
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have he := h.effect.ptn_eq h.base h.partition
  change st.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn at he
  rw [he] at hs
  apply cellStab_of_scatter h.base.ptnSize h.base.labSize h.partition.labSize
    (searchOk_end hn0 h.base (by rw [h.level_eq]; exact h.node.positive))
    h.effect.perm (cellsPerm_trans h.effect.perm hs)
  intro i hi
  have hsz : st.lab.size = n := h.partition.labSize
  rw [getElem!_map_of_lt _ _ (by rw [hsz]; exact hi)]
  rfl

/-- A received short return supplies a valid pair in the frozen parent
frame from its actual checked output and the parent's reference guide. -/
theorem SweepInput.short_pair {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcall : Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) = (.unwind level true, out)) :
    ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g (l.prepare ctx tcLevel).2.2.2.2.ptn
        (l.prepare ctx tcLevel).2.2.2.2.lab level fix mcr := by
  intro fix mcr hp
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hi := (h.push hgsz hsymm hloop).stored hgsz hsymm hloop
  dsimp only [Parent.child] at hi
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hi
  have hr := return_pair h.partition hn0 hl h.path h.target (h.cursor_mem tv rfl)
    (by omega : level < level + 1) (congrArg Prod.fst hcall) hi (Nat.le_refl level)
    (h.canonical.rebase h.effect)
  dsimp only at hr
  rw [hcall] at hr
  exact h.pair (hr (fix, mcr) hp)

/-- The actual received short filter preserves prior coverage after the
child's stop-level coverage has been incorporated. -/
theorem SweepInput.short_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcall : Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) = (.unwind level true, out))
    (hr : let p : Parent n := ⟨l, st, tv, bs, fs⟩
      Generic.Result ((p.child ctx tcLevel).key ctx tcLevel)
        ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) level
        (Witness ctx tcLevel ((parents.push p).frames ctx tcLevel)) (.unwind level true)) :
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (fun v => (Remaining (some tv) cell v ∧ tv < v) ∧ (shortprune cell out).mem v = true)
      (out.best ctx) := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hd : level ≤ n := by rw [h.level_eq]; exact h.node.depth
  apply filter_pair h.base hn0 hl hgsz h.window h.range (by omega) (h.received hr)
  · rintro v ⟨hv, _⟩
    exact h.subset v hv.1
  · rintro v ⟨hv, _⟩
    exact hv.1
  · exact h.short_pair hgsz hsymm hloop hcall

/-- The long filter after an actual child uses the restored parent fixed
set to interpret every admitted pair in the original target frame. -/
theorem SweepInput.long_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell smaller : VSet n}
    {st out : Search n} {exit : Generic.Exit} {l : Loop n} {bs fs : List Nat}
    {parents : Parents n} {live : Nat → Prop} {best : Option (Key n)}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcall : Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) = (exit, out))
    (hc : CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2 live best)
    (hsub : ∀ v, live v →
      (windowSet n (l.prepare ctx tcLevel).2.2.2.2.lab tc (l.prepare ctx tcLevel).2.2.2.1).mem v = true)
    (hmem : ∀ v, live v → smaller.mem v = true) :
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (fun v => live v ∧ (Nauty.longprune smaller (out.fixedpts.erase tv) out.autos).mem v = true)
      best := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hd : level ≤ n := by rw [h.level_eq]; exact h.node.depth
  have hi := (h.push hgsz hsymm hloop).stored hgsz hsymm hloop
  dsimp only [Parent.child] at hi
  rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq, hcall] at hi
  have hf := child_frame (first := first) h.partition hn0 hl h.path.fixed h.target
    (h.cursor_mem tv rfl) (first && tv == tv1) (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  dsimp only at hf
  rw [hcall] at hf
  have hfixed : out.fixedpts.erase tv = st.fixedpts := hf.2
  apply ChildCover.pruned hc (labOk_of_reach h.base.labSize h.base.reach)
    h.window (by change tc + _ ≤ (l.prepare ctx tcLevel).2.2.2.2.view.lab.size
                 rw [h.base.labSize]; exact h.range) hsub
  · intro γ ha hs v hv
    exact congrArg (prefixKey (l.codes ctx))
      (h.base.vertex_key hn0 hl hgsz ha hs h.window h.range hv (by omega) tcLevel)
  · intro v hv hdrop
    apply longprune_drop (windowSet_lt (hsub v hv)) (hmem v hv) hdrop
    intro pair hp hfix
    apply h.pair
    intro w hw hm
    obtain ⟨γ, ha, hfixedγ, hroot, hlt⟩ := hi.pairs pair hp w hw hm
    refine ⟨γ, ha, hfixedγ, ?_, hlt⟩
    apply h.path.stab γ ha hroot
    intro u hu hum
    apply hfixedγ u hu
    rw [hfixed] at hfix
    exact VSet.subset_iff.mp hfix u hum

/-- Reception composes child coverage, both actual filters, and cursor
advance in the frozen target frame for either short-return flag. -/
theorem SweepInput.filtered {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcall : Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) = (.unwind level short, out))
    (hr : let p : Parent n := ⟨l, st, tv, bs, fs⟩
      Generic.Result ((p.child ctx tcLevel).key ctx tcLevel)
        ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) level
        (Witness ctx tcLevel ((parents.push p).frames ctx tcLevel)) (.unwind level short)) :
    let small := if short then shortprune cell out else cell
    let filtered := if !first && tv == tv1 then
      Nauty.longprune small (out.fixedpts.erase tv) out.autos else small
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (Remaining (filtered.nextElem (some tv)) filtered) (out.best ctx) := by
  intro small filtered
  let live := fun v => Remaining (some tv) cell v ∧ tv < v
  have hs : CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (fun v => live v ∧ small.mem v = true) (out.best ctx) := by
    cases short with
    | true => exact h.short_cover hgsz hsymm hloop hcall hr
    | false =>
      apply (h.received hr).filter
      intro v hv
      exact ⟨v, ⟨hv, hv.1.1⟩, rfl, Nat.le_refl _⟩
  have hf : CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (fun v => (live v ∧ small.mem v = true) ∧ filtered.mem v = true) (out.best ctx) := by
    dsimp only [filtered]
    split
    · apply h.long_cover hgsz hsymm hloop hcall hs
      · intro v hv
        exact h.subset v hv.1.1.1
      · intro v hv
        exact hv.2
    · apply hs.filter
      intro v hv
      exact ⟨v, ⟨hv, hv.2⟩, rfl, Nat.le_refl _⟩
  apply hf.filter
  intro v hv
  exact ⟨v, Remaining.next.mpr ⟨hv.2, hv.1.1.2⟩, rfl, Nat.le_refl _⟩

/-- Partition recovery changes neither the installed codes nor their labelling. -/
theorem recover_best (ctx : Ctx n) (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).best ctx = st.best ctx := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- At the receiving level, the actual sweep calls its suffix with
coverage produced by the child induction hypothesis, both filters, and
recovery. First-child cleanup and either short flag are included. -/
theorem SweepInput.receive_call {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : Engine.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Engine.child first level tc tv st) = (.unwind level short, out))
    (next : Generic.SweepFn (Search n) n) :
    let ctx : Ctx n := { g := rowsOf G }
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let small := if short then shortprune cell left else cell
    let filtered := if !first && tv == tv1 then
      Nauty.longprune small left.fixedpts left.autos else small
    let ready := recoverLevels level (recoverPtn (n + 2) level left)
    let nextIndex := if first && ready.orbits[tv]! == tv1 then index + 1 else index
    Generic.sweepStep (n + 2) (Generic.nodeCall ctx (n + 2) tcLevel fuel) next
      first level numcells tc tv1 tv cell index st =
        next first level numcells tc tv1 (filtered.nextElem (some tv)) filtered nextIndex ready ∧
    CellCover ctx tcLevel (n - level) level numcells tc (l.prepare ctx tcLevel).2.2.2.1
      (l.codes ctx) (l.prepare ctx tcLevel).2.2.2.2
      (Remaining (filtered.nextElem (some tv)) filtered) (ready.best ctx) := by
  intro ctx middle left small filtered ready nextIndex
  have hc : Generic.nodeCall ctx (n + 2) tcLevel fuel (first && tv == tv1)
      (level + 1) (numcells + 1) (Engine.child first level tc tv st) =
        (.unwind level short, out) := by
    simpa only [Generic.nodeCall, ← node_eq_generic] using hcall
  constructor
  · unfold Generic.sweepStep
    dsimp only [policy, Generic.Policy.orbit, Generic.Policy.child,
      Generic.Policy.afterChildFirst, Generic.Policy.leaveChild]
    simp only [hvisit, ↓reduceIte, hc, Generic.advance, Nat.lt_irrefl,
      ↓reduceIte, Id.run_pure, apply_ite Id.run]
    dsimp only [Generic.resume, policy, Generic.Policy.shortprune, Generic.Policy.longprune,
      Generic.Policy.recover, Generic.Policy.orbit, left, middle, small, filtered, ready, nextIndex]
    split <;> cases short <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> rfl
  · have hr := h.child_result hn
    dsimp only at hr
    rw [hcall] at hr
    have hcover := h.filtered (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hcall hr
    have ha : left.autos = out.autos := by dsimp only [left, middle]; split <;> rfl
    have hf : left.fixedpts = out.fixedpts.erase tv := by dsimp only [left, middle]; split <;> rfl
    have hb : ready.best ctx = out.best ctx := by
      rw [recover_best]
      dsimp only [left, middle]
      split <;> rfl
    rw [hb]
    dsimp only [filtered, small]
    simp only [Engine.shortprune, ha, hf]
    simpa only [Engine.shortprune] using hcover

end Hex.GraphIso.Nauty.Engine.Max
