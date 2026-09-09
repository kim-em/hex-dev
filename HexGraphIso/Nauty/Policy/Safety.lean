/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

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
  have hp := hin.prepare hn0 hgsz hsymm hloop
  dsimp only [prepareOther] at hp
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.compareCodes, Generic.Policy.chooseTarget,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hvval : visit ctx level numcells st = r at hp ⊢
  obtain ⟨nc, code, refined⟩ := r
  simp only [Bool.false_eq_true, ite_false]
  dsimp only at hp
  generalize htval : chooseTarget false ctx tcLevel level nc (compareCodes level code refined) = t at hp ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨_, _, _, hli, hready⟩ := hp
  generalize hcval : classify ctx level nc targeted = c at hli ⊢
  obtain ⟨leaf, classified⟩ := c
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
    have hnextPre := hready hcfirst
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
      (Nauty.recover (n + 2) level out)) :
    RunInv G ctx (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2 := by
  unfold Generic.advance
  dsimp only [policy, Generic.Policy.shortprune, Generic.Policy.longprune, Generic.Policy.recover,
    Generic.Policy.orbit]
  have htv : first = true → tv1 < tv := fun hf => hready.past hf tv rfl
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      RunInv G ctx (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && (Nauty.recover (n + 2) level out).orbits[tv]! == tv1
          then index + 1 else index)
        (Nauty.recover (n + 2) level out)).2.2 := by
    intro smaller hsub
    exact hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨Generic.Past.next htv, hready.positive, hready.partition, hready.target.subset hsub,
        (fun _ hv => VSet.nextElem_mem hv), hready.stored, hready.ancestor, hready.canonAncestor, hready.history, hready.recorded, hready.equitable, hready.boundary, hready.cheapBound, hready.path, hready.small⟩
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      RunInv G ctx (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hsub
    unfold Generic.resume
    dsimp only [policy, Generic.Policy.longprune, Generic.Policy.recover, Generic.Policy.orbit]
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
          apply_ite Prod.snd] using hlong (shortprune cell out) (fun v hv => Nauty.shortprune_subset (st := out) hv)

/-- Each later sibling calls an off-path child and resumes with the parent's recovered history. -/
theorem safety_sweep {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
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
  have hnodePre := hin.child hn0 hgsz hsymm
  have hd := hdescend false (level + 1) (numcells + 1) (child first level tc tv st) ⟨rfl, hnodePre⟩
  change RunInv G ctx (Generic.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child first level tc tv st)).2 at hd
  rw [← node_eq_generic] at hd
  have hready := hin.restore hn0 hgsz hsymm hd
  unfold Generic.sweepStep
  dsimp only [Generic.nodeCall, policy, Generic.Policy.child, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild, Generic.Policy.orbit, Generic.Policy.shortprune,
    Generic.Policy.longprune, Generic.Policy.recover]
  simp only [hflag, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run, apply_ite Prod.snd]
  split
  · rw [← node_eq_generic]
    generalize hcall : node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st) = result at hd hready ⊢
    obtain ⟨exit, out⟩ := result
    let left := { out with fixedpts := out.fixedpts.erase tv }
    have hleft : RunInv G ctx left := hd.leave tv
    exact safety_advance hnext first level numcells tc tv1 tv index cell left exit hleft hready
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨Generic.Past.next hpast, hin.positive, hin.partition, hin.target,
        (fun _ hv => VSet.nextElem_mem hv), hin.stored, hin.ancestor, hin.canonAncestor, hin.history, hin.recorded, hin.equitable, hin.boundary, hin.cheapBound, hin.path, hin.small⟩

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
    safety_sweep hn0 hgsz hsymm hd hn first level numcells tc tv1 tv index cell st hin

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

end Hex.GraphIso.Nauty
