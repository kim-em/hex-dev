/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Partition effects and canonical-reference effects share the same
entry conditions, including calls truncated by fuel exhaustion. -/
def canonContract (G : Colored n k) : Generic.Contract (Search n) n :=
  { Generic.reachContract G (fun st => st) with
    nodePost := fun _ _ level _ st result =>
      SearchOut G (level - 1) level st result.2 ∧ CanonOut level st result.2
    sweepPost := fun _ _ _ level _ _ _ _ _ _ st result =>
      SearchOut G level level st result.2.2 ∧ CanonOut level st result.2.2 }

/-- A node's completed sweep retains or installs its canonical reference. -/
theorem canon_finish {G : Colored n k} {fuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hnext : (canonContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells tc size : Nat) (cell : VSet n) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) :
    let tv := cell.nextElem none
    let r := next first level numcells tc (tv.getD 0) tv cell 0 st
    CanonOut level st (Id.run (match r.1 with
      | .done => pure (Generic.Exit.unwind (level - 1) false, afterSweep first level size r.2.1 r.2.2)
      | _ => pure (r.1, r.2.2))).2 := by
  have hout := (hnext first level numcells tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 st ⟨hlevel, hok, htarget, fun _ hv => VSet.nextElem_mem hv⟩).2
  dsimp only
  generalize hr : next first level numcells tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 st = r at hout ⊢
  obtain ⟨exit, index, out⟩ := r
  cases exit with
  | done => exact hout.afterSweep first size index
  | unwind => exact hout
  | fuel => exact hout

/-- Local node operations retain the reference or install one in the
refined partition, and refinement transports that fact to the entry. -/
theorem canon_node {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hnext : (canonContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st) :
    CanonOut level st (Generic.nodeStep ctx tcLevel next first level numcells st).2 := by
  let rp := reachPolicy G ctx tcLevel hn0
  have hv := rp.visit level numcells st hlevel hok
  have hvcanon : ∀ out, CanonOut level (visit ctx level numcells st).2.2 out →
      CanonOut level st out := fun _ h => h.visit hn0 hlevel hok
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.firstterminal, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hv ⊢
  generalize hr : visit ctx level numcells st = r at hv hvcanon ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst level code refined else compareCodes level code refined
  have hcomp : Generic.Local G (fun st => st) level nc refined compared := by
    cases first
    · exact rp.compare level code nc refined hv.1
    · exact rp.record level code nc refined hv.1
  have hcg : compared.gcaCanon = refined.gcaCanon := by
    cases first
    · exact compare_canon level code refined
    · rfl
  have hcc : compared.canonlab = refined.canonlab := by
    cases first
    · exact (compareCodes_frame level code refined).2.2.2
    · rfl
  have hcan : CanonOut level refined compared :=
    (CanonOut.refl level refined).fields hcc hcg
  have ht := rp.target first level nc compared hlevel hcomp.ok
  dsimp only [policy, Generic.Policy.chooseTarget] at ht
  have htc := (chooseTarget_frame first ctx tcLevel level nc compared).2.2.2
  have htg := target_canon first ctx tcLevel level nc compared
  change CanonOut level st (Id.run (do
    let (tc, cell, size, targeted) := chooseTarget first ctx tcLevel level nc compared
    let mut state := targeted
    if first then
      if nc == n then return (.unwind (level - 1) false, firstterminal level state)
    else
      let (leaf, classified) := classify ctx level nc state
      let (exit, out) := leafExit leaf level classified
      state := out
      match exit with
      | .done => pure ()
      | _ => return (exit, state)
    state := cheapCheck first level state
    let tv := cell.nextElem none
    let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 state
    match exit with
    | .done => return (.unwind (level - 1) false, afterSweep first level size index out)
    | _ => return (exit, out))).2
  generalize htval : chooseTarget first ctx tcLevel level nc compared = t at ht htc htg ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨htlocal, htarget⟩ := ht
  have hprepared := hcomp.trans htlocal
  have hcanPrepared : CanonOut level refined targeted := hcan.fields htc htg
  have hfinish : ∀ prepared, Generic.Local G (fun st => st) level nc refined prepared →
      CanonOut level refined prepared → Generic.Target (fun st => st) level tc.toNat cell prepared →
      CanonOut level st (let ready := cheapCheck first level prepared
        let tv := cell.nextElem none
        let r := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        (Id.run (match r.1 with
          | .done => pure (Generic.Exit.unwind (level - 1) false, afterSweep first level size r.2.1 r.2.2)
          | _ => pure (r.1, r.2.2))).2) := by
    intro prepared hp hcan ht
    have hc := rp.cheap first level nc prepared hp.ok
    have hcc : CanonOut level refined (cheapCheck first level prepared) := by
      unfold cheapCheck
      split <;> exact hcan.fields rfl rfl
    apply hvcanon
    apply hcc.trans _ (hp.trans hc).effect
    exact canon_finish hnext first level nc tc.toNat size cell _ hlevel hc.ok (ht.of_out hc.effect)
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · apply hvcanon
      apply hcanPrepared.trans _ hprepared.effect
      exact ⟨Nat.min_le_left _ _, Or.inr ⟨Nat.le_refl _, rfl, cellsPerm_refl _ _ _⟩⟩
    · exact hfinish targeted hprepared hcanPrepared htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hcl := rp.classify level nc targeted hprepared.ok
    dsimp only [policy, Generic.Policy.classify] at hcl
    have hcla : CanonOut level refined (classify ctx level nc targeted).2 :=
      hcanPrepared.fields (classify_frame ctx level nc targeted).2.2.2
        (classify_canon ctx level nc targeted)
    generalize hcval : classify ctx level nc targeted = classified at hcl hcla ⊢
    obtain ⟨leaf, classified⟩ := classified
    have hle := rp.leaf leaf level nc classified hcl.ok
    dsimp only [policy, Generic.Policy.leafExit] at hle
    have hlea := hcla.trans (canon_leaf leaf level classified) (hprepared.trans hcl).effect
    generalize hlval : leafExit leaf level classified = result at hle hlea ⊢
    obtain ⟨exit, out⟩ := result
    have hlocal := hprepared.trans (hcl.trans hle)
    cases exit with
    | done => exact hfinish out hlocal hlea ((htarget.of_out hcl.effect).of_out hle.effect)
    | unwind => exact hvcanon out hlea
    | fuel => exact hvcanon out hlea

/-- An intermediate sweep transports the child's reference; a receiving
sweep recovers the parent before composing the remaining siblings. -/
theorem canon_advance {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hnext : (canonContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (base out : Search n) (exit : Exit)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells base)
    (htarget : Generic.Target (fun st => st) level tc cell base)
    (hout : SearchOut G level level base out) (hcanon : CanonOut level base out) :
    CanonOut level base (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit).2.2 := by
  let rp := reachPolicy G ctx tcLevel hn0
  have hr := rp.recover level numcells base out hlevel hok hout
  dsimp only [policy, Generic.Policy.recover] at hr
  have hc := hcanon.recover (n + 2)
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      CanonOut level base (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && (Nauty.recover (n + 2) level out).orbits[tv]! == tv1
          then index + 1 else index)
        (Nauty.recover (n + 2) level out)).2.2 := by
    intro smaller hsub
    apply hc.trans ?_ hr.effect
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨hlevel, hr.ok, (htarget.subset hsub).of_out hr.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      CanonOut level base (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out).2.2 := by
    intro smaller hsub
    unfold Generic.resume
    dsimp only [policy, Generic.Policy.longprune, Generic.Policy.recover, Generic.Policy.orbit]
    split
    · exact hcontinue _ (fun v hv => hsub v (Nauty.longprune_subset hv))
    · exact hcontinue _ hsub
  unfold Generic.advance
  dsimp only [policy, Generic.Policy.shortprune]
  cases exit with
  | fuel => exact hcanon
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcanon
    · cases short with
      | false => exact hresume cell (fun _ hv => hv)
      | true =>
        exact hresume (shortprune cell out)
          (fun _ hv => Nauty.shortprune_subset (st := out) hv)

/-- One child and the remaining sweep compose their canonical effects,
including first-child bookkeeping and all non-local exits. -/
theorem canon_sweep {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {descend : Generic.NodeFn (Search n)} {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hdescend : (canonContract G).nodeValid fuel descend)
    (hnext : (canonContract G).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    CanonOut level st (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  let rp := reachPolicy G ctx tcLevel hn0
  have hc := rp.child first level numcells tc tv cell st hlevel hok htarget htv
  dsimp only [policy, Generic.Policy.child] at hc
  have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1)
    (child first level tc tv st) ⟨by omega, hc.1⟩
  unfold Generic.sweepStep
  dsimp only [policy, Generic.Policy.child, Generic.Policy.orbit,
    Generic.Policy.afterChildFirst, Generic.Policy.leaveChild]
  split
  · generalize hdval : descend (first && tv == tv1) (level + 1) (numcells + 1)
      (child first level tc tv st) = result at hd ⊢
    obtain ⟨exit, out⟩ := result
    have he := hc.2 out (by simpa only [Nat.add_sub_cancel] using hd.1)
    have ha := hd.2.child (ctx := ctx) first hn0 hlevel hok htarget htv
    split
    · apply canon_advance (ctx := ctx) (tcLevel := tcLevel) hn0 hnext first level numcells tc tv1 tv index cell st
        _ exit hlevel hok htarget
      · exact he.congr rfl rfl rfl rfl
      · exact ha.fields rfl rfl
    · apply canon_advance (ctx := ctx) (tcLevel := tcLevel) hn0 hnext first level numcells tc tv1 tv index cell st
        _ exit hlevel hok htarget
      · exact he.congr rfl rfl rfl rfl
      · exact ha.fields rfl rfl
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hlevel, hok, htarget, fun _ hv => VSet.nextElem_mem hv⟩).2

/-- Canonical-reference tracking is an instance of the common policy induction. -/
theorem canonPolicy (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (hn0 : 0 < n) :
    Generic.SoundPolicy ctx (n + 2) tcLevel (canonContract G) where
  node_zero := fun _ level _ st hin =>
    ⟨SearchOut.refl G (level - 1) level hin.2.reach, CanonOut.refl level st⟩
  node_step := by
    intro fuel next hnext first level numcells st hin
    have hr : (Generic.reachContract G (fun st => st)).sweepValid fuel (n + 1) next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨(reachPolicy G ctx tcLevel hn0).node_step hr first level numcells st hin.1 hin.2,
      canon_node hn0 hnext first level numcells st hin.1 hin.2⟩
  sweep_none := fun _ _ _ level _ _ _ _ _ st hin =>
    ⟨SearchOut.refl G level level hin.2.1.reach, CanonOut.refl level st⟩
  sweep_zero := fun _ _ level _ _ _ _ _ _ st hin =>
    ⟨SearchOut.refl G level level hin.2.1.reach, CanonOut.refl level st⟩
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st hin
    have hd : (Generic.reachContract G (fun st => st)).nodeValid fuel descend :=
      fun first level numcells st hin => (hdescend first level numcells st hin).1
    have hr : (Generic.reachContract G (fun st => st)).sweepValid fuel cfuel next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨(reachPolicy G ctx tcLevel hn0).sweep_step hd hr first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      canon_sweep (ctx := ctx) (tcLevel := tcLevel) hn0 hdescend hnext first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)⟩

/-- A whole node couples the stored canonical labelling to its ancestor counter. -/
theorem node_canon {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) :
    CanonOut level st (node first ctx (n + 2) tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic]
  exact (Generic.node_sound (canonPolicy G ctx tcLevel hn0) first fuel level numcells st ⟨hlevel, hok⟩).2

/-- A whole sweep couples its stored canonical labelling to its ancestor counter. -/
theorem sweep_canon {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st)
    (hcursor : ∀ v, cursor = some v → cell.mem v = true) :
    CanonOut level st (sweep first ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  rw [sweep_eq_generic]
  exact (Generic.sweep_sound (canonPolicy G ctx tcLevel hn0) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hlevel, hok, htarget, hcursor⟩).2

end Hex.GraphIso.Nauty
