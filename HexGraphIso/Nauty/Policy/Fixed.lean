/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FixedState
public import HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.FixedState
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Calls restore the fixed-point set they received. Freshness is supplied
by singleton cells at each individualization site. -/
def fixedContract (G : Colored n k) : Generic.Contract (Search n) n where
  nodePre _ _ level numcells st :=
    1 ≤ level ∧ SearchOk G level numcells st.view ∧ FixedCells level st.view
  nodePost _ _ _ _ st result := result.2.fixedpts = st.fixedpts
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ SearchOk G level numcells st.view ∧
      Generic.Target Search.view level tc cell st ∧
      (∀ v, cursor = some v → cell.mem v = true) ∧ FixedCells level st.view
  sweepPost _ _ _ _ _ _ _ _ _ _ st result := result.2.2.fixedpts = st.fixedpts

/-- The local node operations preserve fixed vertices, and its child
sweep restores the same set on every exit. -/
theorem fixed_node {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {next : Generic.SweepFn (Search n) n} (hn0 : 0 < n)
    (hnext : (fixedContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (hfixed : FixedCells level st.view) :
    (Generic.nodeStep ctx tcLevel next first level numcells st).2.fixedpts = st.fixedpts := by
  let reach := reachPolicy G ctx tcLevel hn0
  have hv := reach.visit level numcells st hlevel hok
  have hvf := fixed_visit (ctx := ctx) hn0 hlevel hok hfixed
  have hve : (Generic.Policy.visit ctx level numcells st).2.2.fixedpts = st.fixedpts := rfl
  unfold Generic.nodeStep
  generalize hr : Generic.Policy.visit ctx level numcells st = r at hv hve ⊢
  change FixedCells level (Generic.Policy.visit ctx level numcells st).2.2.view at hvf
  rw [hr] at hvf
  obtain ⟨nc, code, refined⟩ := r
  obtain ⟨hokR, _⟩ := hv
  let compared := if first then Generic.Policy.recordFirst (n := n) level code refined
    else Generic.Policy.compareCodes (n := n) level code refined
  have hcomp : Generic.Local G Search.view level nc refined compared := by
    cases first
    · exact reach.compare level code nc refined hokR
    · exact reach.record level code nc refined hokR
  have hce : compared.fixedpts = refined.fixedpts := by
    cases first
    · exact compare_fixed level code refined
    · rfl
  have hcf := hvf.ofSearchOut hce hokR hcomp.ok hcomp.effect
  have ht := reach.target first level nc compared hlevel hcomp.ok
  have hte := target_fixed first ctx tcLevel level nc compared
  change (Generic.Policy.chooseTarget first ctx tcLevel level nc compared).2.2.2.fixedpts = _ at hte
  change (Id.run (do
      let (tc, tcell, size, st) := Generic.Policy.chooseTarget first ctx tcLevel level nc compared
      let mut st := st
      if first then
        if nc == n then
          return (Generic.Exit.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level st)
      else
        let (leaf, st') := Generic.Policy.classify ctx level nc st
        let (exit, st') := Generic.Policy.leafExit (n := n) leaf level st'
        st := st'
        match exit with
        | .done => pure ()
        | _ => return (exit, st)
      st := Generic.Policy.cheapCheck (n := n) first level st
      let tv := tcell.nextElem none
      let (exit, index, st') := next first level nc tc.toNat (tv.getD 0) tv tcell 0 st
      match exit with
      | .done => return (Generic.Exit.unwind (level - 1) false,
          Generic.Policy.afterSweep (n := n) first level size index st')
      | _ => return (exit, st'))).2.fixedpts = st.fixedpts
  generalize htval : Generic.Policy.chooseTarget first ctx tcLevel level nc compared = t at ht hte ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨htlocal, htarget⟩ := ht
  have htf := hcf.ofSearchOut hte hcomp.ok htlocal.ok htlocal.effect
  have htargetEq := hte.trans (hce.trans hve)
  have hfinish : ∀ prepared, SearchOk G level nc prepared.view →
      Generic.Target Search.view level tc.toNat cell prepared → FixedCells level prepared.view →
      prepared.fixedpts = st.fixedpts →
      (let ready := Generic.Policy.cheapCheck (n := n) first level prepared
       let tv := cell.nextElem none
       let r := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
       (Id.run (match r.1 with
       | .done => pure (Generic.Exit.unwind (level - 1) false,
           Generic.Policy.afterSweep (n := n) first level size r.2.1 r.2.2)
       | _ => pure (r.1, r.2.2))).2.fixedpts) = st.fixedpts := by
    intro prepared hp ht hf he
    have hc := reach.cheap first level nc prepared hp
    have hcheap := cheap_fixed first level prepared
    have hn := hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hlevel, hc.ok, ht.of_out hc.effect, (fun _ hv => VSet.nextElem_mem hv),
        hf.ofSearchOut hcheap hp hc.ok hc.effect⟩
    change (next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) first level prepared)).2.2.fixedpts = _ at hn
    dsimp only
    generalize hs : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Generic.Policy.cheapCheck (n := n) first level prepared) = result at hn ⊢
    obtain ⟨exit, index, out⟩ := result
    have hout := hn.trans (hcheap.trans he)
    cases exit with
    | done => exact (afterSweep_fixed first level size index out).trans hout
    | fuel => exact hout
    | unwind => exact hout
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact htargetEq
    · exact hfinish targeted htlocal.ok htarget htf htargetEq
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hcl := reach.classify level nc targeted htlocal.ok
    have hcle := classify_fixed ctx level nc targeted
    change (Generic.Policy.classify ctx level nc targeted).2.fixedpts = _ at hcle
    generalize hcval : Generic.Policy.classify ctx level nc targeted = classified at hcl hcle ⊢
    obtain ⟨leaf, classified⟩ := classified
    have hclf := htf.ofSearchOut hcle htlocal.ok hcl.ok hcl.effect
    have hle := reach.leaf leaf level nc classified hcl.ok
    have hlee := leaf_fixed leaf level classified
    change (Generic.Policy.leafExit (n := n) leaf level classified).2.fixedpts = _ at hlee
    generalize hlval : Generic.Policy.leafExit (n := n) leaf level classified = result at hle hlee ⊢
    obtain ⟨exit, out⟩ := result
    have hef := hclf.ofSearchOut hlee hcl.ok hle.ok hle.effect
    have he := hlee.trans (hcle.trans htargetEq)
    cases exit with
    | done => exact hfinish out hle.ok ((htarget.of_out hcl.effect).of_out hle.effect) hef he
    | unwind => exact he
    | fuel => exact he

/-- A completed child's fixed set remains restored through pruning and
parent recovery, including every nonlocal return. -/
theorem fixed_advance {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n} (hn0 : 0 < n)
    (hnext : (fixedContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (base out : Search n) (exit : Exit)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells base.view)
    (htarget : Generic.Target Search.view level tc cell base)
    (hfixed : FixedCells level base.view)
    (hout : SearchOut G level level base.view out.view) (hf : out.fixedpts = base.fixedpts) :
    (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2.fixedpts =
      base.fixedpts := by
  unfold Generic.advance
  let reach := reachPolicy G ctx tcLevel hn0
  have hr := reach.recover level numcells base out hlevel hok hout
  have hrf := fixed_recover (ctx := ctx) hn0 hlevel hok hfixed hout hf
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && Generic.Policy.orbit (n := n) (Generic.Policy.recover (n := n) (n + 2) level out) tv == tv1
          then index + 1 else index)
        (Generic.Policy.recover (n := n) (n + 2) level out)).2.2.fixedpts = base.fixedpts := by
    intro smaller hsub
    have hn := hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
      (if first && Generic.Policy.orbit (n := n) (Generic.Policy.recover (n := n) (n + 2) level out) tv == tv1
        then index + 1 else index) (Generic.Policy.recover (n := n) (n + 2) level out)
      ⟨hlevel, hr.ok, (htarget.subset hsub).of_out hr.effect,
        (fun _ hv => VSet.nextElem_mem hv), hrf⟩
    exact hn.trans ((recover_fixed (n + 2) level out).trans hf)
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2.fixedpts =
        base.fixedpts := by
    intro smaller hsub
    unfold Generic.resume
    split
    · exact hcontinue _ (fun v hv => hsub v (reach.long smaller out v hv))
    · exact hcontinue _ hsub
  cases exit with
  | fuel => exact hf
  | done => exact hlong cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hf
    · cases short with
      | false =>
        simpa only [Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong cell (fun _ hv => hv)
      | true =>
        simpa only [ite_true, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong _ (fun v hv => reach.short cell out v hv)

/-- Erasing a fresh child's temporary fixed vertex restores its parent set. -/
theorem fixed_restore {tv : Nat} {base out : Search n}
    (hf : out.fixedpts = base.fixedpts.insert tv) (hfresh : base.fixedpts.mem tv = false) :
    out.fixedpts.erase tv = base.fixedpts := by
  rw [hf]
  apply VSet.ext
  intro v
  by_cases he : tv = v
  · subst v
    simp only [VSet.mem_erase, beq_self_eq_true, Bool.not_true, Bool.and_false, hfresh]
  · simp only [VSet.mem_erase, VSet.mem_insert, beq_eq_false_iff_ne.mpr he,
      Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true]

/-- One sweep iteration adds a fresh fixed vertex, recursively restores
the child's set, then removes precisely that temporary vertex. -/
theorem fixed_sweep {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n} (hn0 : 0 < n)
    (hdescend : (fixedContract G).nodeValid fuel (Generic.nodeCall ctx (n + 2) tcLevel fuel))
    (hnext : (fixedContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (htarget : Generic.Target Search.view level tc cell st) (htv : cell.mem tv = true)
    (hfixed : FixedCells level st.view) :
    (Generic.sweepStep (n + 2) (Generic.nodeCall ctx (n + 2) tcLevel fuel) next
      first level numcells tc tv1 tv cell index st).2.2.fixedpts = st.fixedpts := by
  let reach := reachPolicy G ctx tcLevel hn0
  have hc := reach.child first level numcells tc tv cell st hlevel hok htarget htv
  have hcf := fixed_child first hn0 hok hfixed htarget htv
  have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1)
    (Generic.Policy.child (n := n) first level tc tv st) ⟨by omega, hc.1, hcf.2⟩
  change (Generic.node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child first level tc tv st)).2.fixedpts = (child first level tc tv st).fixedpts at hd
  rw [← node_eq_generic] at hd
  have ho := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) (first && tv == tv1)
    hn0 (by omega) hc.1
  have heffect := hc.2 _ (by simpa only [Nat.add_sub_cancel] using ho)
  unfold Generic.sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · simp only [Generic.nodeCall, ← node_eq_generic]
    generalize hcall : node (first && tv == tv1) ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st) = result at hd heffect ⊢
    obtain ⟨exit, out⟩ := result
    have hrestore : out.fixedpts.erase tv = st.fixedpts := by
      apply fixed_restore (base := st) (out := out) _ hcf.1
      exact hd.trans (by cases first <;> rfl)
    have hleave : ∀ returned : Search n, SearchOut G level level st.view returned.view →
        SearchOut G level level st.view (Generic.Policy.leaveChild (n := n) tv returned).view :=
      fun returned hr => (reach.leave tv returned).out hr
    split
    · apply fixed_advance (ctx := ctx) (tcLevel := tcLevel) hn0 hnext first level numcells tc tv1 tv index cell st _ exit
        hlevel hok htarget hfixed (hleave _ ((reach.afterChild level tv1 out).out heffect))
      exact hrestore
    · exact fixed_advance (ctx := ctx) (tcLevel := tcLevel) hn0 hnext first level numcells tc tv1 tv index cell st _ exit
        hlevel hok htarget hfixed (hleave _ heffect) hrestore
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hlevel, hok, htarget, (fun _ hv => VSet.nextElem_mem hv), hfixed⟩

/-- Fixed-point restoration follows the same policy-parameterized recursion. -/
theorem fixedPolicy (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (hn0 : 0 < n) :
    Generic.CallPolicy ctx (n + 2) tcLevel (fixedContract G) where
  node_zero := fun _ _ _ _ _ => rfl
  node_step := fun _ hn first level numcells st hin =>
    fixed_node hn0 hn first level numcells st hin.1 hin.2.1 hin.2.2
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_step := fun _ _ hd hn first level numcells tc tv1 tv cell index st hin =>
    fixed_sweep hn0 hd hn first level numcells tc tv1 tv index cell st
      hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2.1 tv rfl) hin.2.2.2.2

/-- Every actual call restores its incoming fixed-point set, even when
it returns past several ancestors or exhausts operational fuel. -/
theorem node_fixed {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) (hfixed : FixedCells level st.view) :
    (node first ctx (n + 2) tcLevel fuel level numcells st).2.fixedpts = st.fixedpts := by
  rw [node_eq_generic]
  exact Generic.node_calls (fixedPolicy G ctx tcLevel hn0) first fuel level numcells st
    ⟨hlevel, hok, hfixed⟩

end Hex.GraphIso.Nauty.Engine
