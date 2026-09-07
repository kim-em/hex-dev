/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.HistoryState
public import HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- An off-path node carries the pending history of its actual refinement. -/
structure NodePre (G : Colored n k) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) : Prop where
  positive : 1 ≤ level
  partition : SearchOk G level numcells st.view
  stored : RunInv G ctx st
  ancestor : st.gcaFirst < level
  history : let r := visit ctx level numcells st
    History ctx tcLevel level (level - 1) r.1 r.2.2

/-- A later-sibling sweep retains the parent history and its recorded target. -/
structure SweepPre (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (first : Bool)
    (level numcells tc tv1 : Nat) (cursor : Option Nat) (cell : VSet n) (st : Search n) : Prop where
  past : Generic.Past first tv1 cursor
  positive : 1 ≤ level
  partition : SearchOk G level numcells st.view
  target : Generic.Target Search.view level tc cell st
  cursor_mem : ∀ v, cursor = some v → cell.mem v = true
  stored : RunInv G ctx st
  ancestor : st.gcaFirst ≤ level
  history : History ctx tcLevel level level numcells st
  recorded : Recorded ctx tcLevel level tc st

/-- The off-path induction preserves all installed data, including the checked generator trace. -/
def safetyContract (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) : Generic.Contract (Search n) n where
  nodePre _ first level numcells st := first = false ∧ NodePre G ctx tcLevel level numcells st
  nodePost _ _ _ _ _ result := RunInv G ctx result.2
  sweepPre _ _ first level numcells tc tv1 cursor cell _ st :=
    SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st
  sweepPost _ _ _ _ _ _ _ _ _ _ _ result := RunInv G ctx result.2.2

/-- Refinement, comparison and classification meet the off-path node contract. -/
theorem safety_node {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hnext : (safetyContract G ctx tcLevel).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : Search n) (hin : NodePre G ctx tcLevel level numcells st) :
    RunInv G ctx (Generic.nodeStep ctx tcLevel next false level numcells st).2 := by
  have hv := ((reachPolicy G ctx tcLevel hn0).visit level numcells st hin.positive hin.partition).1
  dsimp only [policy, Generic.Policy.visit] at hv
  have hvi := hin.stored.visit level numcells
  have hvh := hin.history
  have hvg : (visit ctx level numcells st).2.2.gcaFirst < level := hin.ancestor
  have hcode := refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  change (visit ctx level numcells st).2.1 < codeSentinel at hcode
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.compareCodes, Generic.Policy.chooseTarget,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hvval : visit ctx level numcells st = r at hv hvi hvh hvg hcode ⊢
  obtain ⟨nc, code, refined⟩ := r
  simp only [Bool.false_eq_true, ite_false]
  let compared := compareCodes level code refined
  have hci := hvi.compare level code
  have hch := hvh.compare hin.positive hcode
  have hcp := ((reachPolicy G ctx tcLevel hn0).compare level code nc refined hv).ok
  have hcg : compared.gcaFirst < level := by
    rw [show compared.gcaFirst = refined.gcaFirst from (gcaPolicy ctx 0 tcLevel).compare level code refined]
    exact hvg
  have ht := (reachPolicy G ctx tcLevel hn0).target false level nc compared hin.positive hcp
  dsimp only [policy, Generic.Policy.chooseTarget] at ht
  have hti := hci.target tcLevel level nc
  have hth := hch.target
  have htg : (chooseTarget false ctx tcLevel level nc compared).2.2.2.gcaFirst < level := by
    rw [show (chooseTarget false ctx tcLevel level nc compared).2.2.2.gcaFirst = compared.gcaFirst from
      (gcaPolicy ctx 0 tcLevel).target level nc compared]
    exact hcg
  have hrecord : nc < n → Recorded ctx tcLevel level (chooseTarget false ctx tcLevel level nc compared).1.toNat
      (chooseTarget false ctx tcLevel level nc compared).2.2.2 :=
    fun hnc => hch.recorded hnc hin.positive hgsz hsymm hloop
  generalize htval : chooseTarget false ctx tcLevel level nc compared = t at ht hti hth htg hrecord ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  change targeted.gcaFirst < level at htg
  obtain ⟨htlocal, htarget⟩ := ht
  have hcli := hti.classify level nc
  have hclp := ((reachPolicy G ctx tcLevel hn0).classify level nc targeted htlocal.ok).ok
  dsimp only [policy, Generic.Policy.classify] at hclp
  have hclv := classify_store hti.cache (level := level) (numcells := nc)
  have hcheck := hth.checked hti hn0 htlocal.ok hgsz hsymm hloop
  have hcolor := classify_stab hn0 hti.scratch hti.firstSize hti.firstReach
    hti.canonical.1 hti.canonical.2 htlocal.ok.reach (ctx := ctx) (level := level) (numcells := nc)
  generalize hcval : classify ctx level nc targeted = c at hcli hclp hclv hcheck hcolor ⊢
  obtain ⟨leaf, classified⟩ := c
  have hli := hcli.leaf leaf hclp hclv.2 hcheck hcolor
  generalize hlval : leafExit leaf level classified = result at hli ⊢
  obtain ⟨exit, out⟩ := result
  cases exit with
  | fuel => exact hli
  | unwind => exact hli
  | done =>
    have hleaf : leaf = .internal := (leafExit_done leaf level classified).mp (congrArg Prod.fst hlval)
    subst leaf
    have hcfirst : (classify ctx level nc targeted).1 = .internal := congrArg Prod.fst hcval
    have hclassified : classified = targeted :=
      (Prod.mk.inj (hcval.symm.trans (classify_internal_state hcfirst))).2
    subst classified
    have hout : out = targeted := (Prod.mk.inj (hlval.symm.trans
      (show leafExit .internal level targeted = (.done, targeted) from rfl))).2
    subst out
    have hnc : nc < n := by
      have hne := ((classify_internal ctx level nc targeted).mp hcfirst).2
      have hb := bcount_le targeted.ptn level n
      have hc := htlocal.ok.count
      change nc = bcount targeted.ptn level n at hc
      omega
    have hcheap := (reachPolicy G ctx tcLevel hn0).cheap false level nc targeted htlocal.ok
    have hnextPre : SweepPre G ctx tcLevel false level nc tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell (cheapCheck false level targeted) :=
      ⟨(by intro hf; cases hf), hin.positive, hcheap.ok, htarget.of_out hcheap.effect,
        (fun _ hv => VSet.nextElem_mem hv), hti.cheap false level,
        (by rw [show (cheapCheck false level targeted).gcaFirst = targeted.gcaFirst from
              (gcaPolicy ctx 0 tcLevel).cheap false level targeted]; omega),
        hth.cheap false (by change targeted.gcaFirst ≤ level; omega),
        (hrecord hnc).cheap false (by change targeted.gcaFirst ≤ level; omega)⟩
    have hn := hnext false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck false level targeted) hnextPre
    generalize hsval : next false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck false level targeted) = s at hn ⊢
    obtain ⟨exit, index, result⟩ := s
    cases exit with
    | fuel => exact hn
    | unwind => exact hn
    | done => exact hn.afterSweep false level size index

/-- Pruning removes target vertices; every resumed cursor receives the recovered history. -/
theorem safety_advance {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hnext : (safetyContract G ctx tcLevel).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (out : Search n) (exit : Exit)
    (hstored : RunInv G ctx out)
    (hready : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell
      (recoverLevels level (recoverPtn (n + 2) level out))) :
    RunInv G ctx (Id.run (do
      let mut cell := cell
      match exit with
      | .fuel => return (Generic.Exit.fuel, index, out)
      | .unwind target short =>
        if target < level then return (exit, index, out)
        if short then cell := shortprune cell out
      | .done => pure ()
      if !first && tv == tv1 then cell := Nauty.longprune cell out.fixedpts out.autos
      let st := recoverLevels level (recoverPtn (n + 2) level out)
      let index := if first && st.orbits[tv]! == tv1 then index + 1 else index
      return next first level numcells tc tv1 (cell.nextElem (some tv)) cell index st)).2.2 := by
  have htv : first = true → tv1 < tv := fun hf => hready.past hf tv rfl
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      RunInv G ctx (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && (recoverLevels level (recoverPtn (n + 2) level out)).orbits[tv]! == tv1
          then index + 1 else index)
        (recoverLevels level (recoverPtn (n + 2) level out))).2.2 := by
    intro smaller hsub
    exact hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨Generic.Past.next htv, hready.positive, hready.partition, hready.target.subset hsub,
        (fun _ hv => VSet.nextElem_mem hv), hready.stored, hready.ancestor, hready.history, hready.recorded⟩
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      RunInv G ctx (Id.run (do
        let mut cell := smaller
        if !first && tv == tv1 then cell := Nauty.longprune cell out.fixedpts out.autos
        let st := recoverLevels level (recoverPtn (n + 2) level out)
        let index := if first && st.orbits[tv]! == tv1 then index + 1 else index
        return next first level numcells tc tv1 (cell.nextElem (some tv)) cell index st)).2.2 := by
    intro smaller hsub
    split
    · exact hcontinue _ (fun v hv => hsub v (Nauty.longprune_subset hv))
    · exact hcontinue _ hsub
  cases exit with
  | fuel => exact hstored
  | done => exact hlong cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hstored
    · cases short with
      | false =>
        simpa only [Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong cell (fun _ hv => hv)
      | true =>
        simpa only [ite_true, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong (shortprune cell out) (fun v hv => Nauty.shortprune_subset (st := out.view) hv)

/-- Each later sibling calls an off-path child and resumes with the parent's recovered history. -/
theorem safety_sweep {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hdescend : (safetyContract G ctx tcLevel).nodeValid fuel
      (Generic.nodeCall ctx (n + 2) tcLevel fuel))
    (hnext : (safetyContract G ctx tcLevel).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : Search n)
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st) :
    RunInv G ctx (Generic.sweepStep (n + 2) (Generic.nodeCall ctx (n + 2) tcLevel fuel)
      next first level numcells tc tv1 tv cell index st).2.2 := by
  have htv : cell.mem tv = true := hin.cursor_mem tv rfl
  have hpast : first = true → tv1 < tv := fun hf => hin.past hf tv rfl
  have hflag : (first && tv == tv1) = false := by
    cases first with
    | false => rfl
    | true =>
      have := hpast rfl
      simp only [Bool.true_and, beq_eq_false_iff_ne]
      omega
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hin.positive hin.partition hin.target htv
  dsimp only [policy, Generic.Policy.child] at hch
  have hnodePre : NodePre G ctx tcLevel (level + 1) (numcells + 1) (child first level tc tv st) :=
    ⟨(by have := hin.positive; omega), hch.1, hin.stored.child first level tc tv,
      (by cases first <;> change st.gcaFirst < level + 1 <;> have := hin.ancestor <;> omega),
      (by simpa only [Nat.add_sub_cancel] using
        hin.history.child first hgsz hin.positive hin.partition hin.target htv hin.recorded)⟩
  have hd := hdescend false (level + 1) (numcells + 1) (child first level tc tv st) ⟨rfl, hnodePre⟩
  change RunInv G ctx (Generic.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child first level tc tv st)).2 at hd
  rw [← node_eq_generic] at hd
  have ho := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) false hn0
    (by have := hin.positive; omega) hch.1
  have hframe := hch.2 _ (by simpa only [Nat.add_sub_cancel] using ho)
  have hhist := hin.history.child_return (fuel := fuel) first hin.ancestor hin.positive
    hin.partition hin.target htv
  dsimp only at hhist
  have hgca : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2.gcaFirst = st.gcaFirst := by
    rw [node_gca]
    cases first <;> rfl
  unfold Generic.sweepStep
  dsimp only [Generic.nodeCall, policy, Generic.Policy.child, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild, Generic.Policy.orbit, Generic.Policy.shortprune,
    Generic.Policy.longprune, Generic.Policy.recover]
  simp only [hflag, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run, apply_ite Prod.snd]
  split
  · rw [← node_eq_generic]
    generalize hcall : node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st) = result at hd hframe hhist hgca ⊢
    obtain ⟨exit, out⟩ := result
    let left := { out with fixedpts := out.fixedpts.erase tv }
    have hleft : RunInv G ctx left := hd.leave tv
    have hleftFrame : SearchOut G level level st.view left.view := hframe.congr rfl rfl rfl rfl
    have hr := (reachPolicy G ctx tcLevel hn0).recover level numcells st left
      hin.positive hin.partition hleftFrame
    have hready : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell
        (recoverLevels level (recoverPtn (n + 2) level left)) :=
      ⟨hin.past, hin.positive, hr.ok, hin.target.of_out hr.effect, hin.cursor_mem,
        hleft.recover (n + 2) level,
        (by rw [show (recoverLevels level (recoverPtn (n + 2) level left)).gcaFirst = left.gcaFirst from
              (gcaPolicy ctx (n + 2) tcLevel).recover level left]
            change out.gcaFirst ≤ level
            change out.gcaFirst = st.gcaFirst at hgca
            rw [hgca]
            exact hin.ancestor),
        hhist.1, hhist.2 hin.recorded⟩
    exact safety_advance hnext first level numcells tc tv1 tv index cell left exit hleft hready
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨Generic.Past.next hpast, hin.positive, hin.partition, hin.target,
        (fun _ hv => VSet.nextElem_mem hv), hin.stored, hin.ancestor, hin.history, hin.recorded⟩

/-- The live histories discharge the generic induction rules for every off-path call. -/
theorem safetyPolicy (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.CallPolicy ctx (n + 2) tcLevel (safetyContract G ctx tcLevel) where
  node_zero := fun _ _ _ _ hin => hin.2.stored
  node_step := by
    intro fuel next first level numcells st hin
    obtain ⟨rfl, hin⟩ := hin
    exact safety_node hn0 hgsz hsymm hloop next level numcells st hin
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ hin => hin.stored
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ hin => hin.stored
  sweep_step := fun _ _ hd hn first level numcells tc tv1 tv cell index st hin =>
    safety_sweep hn0 hgsz hd hn first level numcells tc tv1 tv index cell st hin

/-- Every off-path call preserves the installed canonical data and checked generator trace. -/
theorem node_safe {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hin : NodePre G ctx tcLevel level numcells st) :
    RunInv G ctx (node false ctx (n + 2) tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic]
  exact Generic.node_calls (safetyPolicy G ctx tcLevel hn0 hgsz hsymm hloop)
    false fuel level numcells st ⟨rfl, hin⟩

/-- A sweep past the first child preserves the same invariant through all exits. -/
theorem sweep_safe {G : Colored n k} {ctx : Ctx n} {first : Bool}
    {tcLevel fuel cfuel level numcells tc tv1 index : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st) :
    RunInv G ctx (sweep first ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  rw [sweep_eq_generic]
  exact Generic.sweep_calls (safetyPolicy G ctx tcLevel hn0 hgsz hsymm hloop)
    first fuel cfuel level numcells tc tv1 cursor cell index st hin

end Hex.GraphIso.Nauty.Engine
