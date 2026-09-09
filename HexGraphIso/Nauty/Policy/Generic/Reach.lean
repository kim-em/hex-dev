/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Sound
public import HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Search.Generic

public section

/-!
Reachability uses only the partition effects of policy operations.
Generator validity and the reasons for pruning do not enter this
argument: pruning removes vertices from a target cell, and every visited
child individualizes a vertex still in that cell.
-/

namespace Hex.GraphIso.Nauty.Generic

variable {n k : Nat} {σ : Type}

/-- The four arrays read by the partition-effect contract are unchanged. -/
structure FrameEq (view : σ → Search n) (st out : σ) : Prop where
  lab : (view out).lab = (view st).lab
  ptn : (view out).ptn = (view st).ptn
  first : (view out).firstlab = (view st).firstlab
  canon : (view out).canonlab = (view st).canonlab

/-- Bookkeeping changes preserve an already established call effect. -/
theorem FrameEq.out {view : σ → Search n} {G : Colored n k}
    {B level : Nat} {base st out : σ} (h : FrameEq view st out)
    (hbefore : SearchOut G B level (view base) (view st)) :
    SearchOut G B level (view base) (view out) :=
  hbefore.congr h.lab h.ptn h.first h.canon

/-- A local operation preserves the live partition and moves labels only
within its current cells, including any newly installed leaf references. -/
structure Local (G : Colored n k) (view : σ → Search n)
    (level numcells : Nat) (st out : σ) : Prop where
  ok : SearchOk G level numcells (view out)
  effect : SearchOut G level level (view st) (view out)

/-- Compose two local operations. -/
theorem Local.trans {G : Colored n k} {view : σ → Search n}
    {level numcells : Nat} {st middle out : σ}
    (h₁ : Local G view level numcells st middle)
    (h₂ : Local G view level numcells middle out) :
    Local G view level numcells st out := ⟨h₂.ok, h₁.effect.trans h₂.effect⟩

/-- A surviving target set consists of vertices in one nontrivial cell.
The empty set needs no target-cell witness. -/
def Target (view : σ → Search n) (level tc : Nat) (cell : VSet n) (st : σ) : Prop :=
  ∃ len, (cell ≠ VSet.empty →
      IsCell (view st).ptn level tc len ∧ 2 ≤ len ∧ tc + len ≤ n) ∧
    ∀ v, cell.mem v = true → v ∈ segN (view st).lab tc len

/-- Removing target vertices preserves the target-cell witness. -/
theorem Target.subset {view : σ → Search n} {level tc : Nat}
    {cell smaller : VSet n} {st : σ} (h : Target view level tc cell st)
    (hsub : ∀ v, smaller.mem v = true → cell.mem v = true) :
    Target view level tc smaller st := by
  obtain ⟨len, hcell, hmem⟩ := h
  refine ⟨len, ?_, fun v hv => hmem v (hsub v hv)⟩
  intro hne
  apply hcell
  intro heq
  apply hne
  apply VSet.ext
  intro v
  rw [VSet.mem_empty]
  cases hmemv : smaller.mem v with
  | false => rfl
  | true =>
    have hm := hsub v hmemv
    rw [heq, VSet.mem_empty] at hm
    cases hm

/-- A sweep's frame effect transports membership of every remaining
target vertex into the returned labelling. -/
theorem Target.of_out {view : σ → Search n} {G : Colored n k}
    {level tc : Nat} {cell : VSet n} {st out : σ}
    (h : Target view level tc cell st)
    (hout : SearchOut G level level (view st) (view out)) :
    Target view level tc cell out := by
  obtain ⟨len, hcell, hmem⟩ := h
  refine ⟨len, fun hne => ⟨isCell_of_low hout.low (hcell hne).1,
    (hcell hne).2⟩, ?_⟩
  intro v hv
  have hc := (hcell (mem_ne_empty hv)).1
  exact (hout.perm tc len hc).mem_iff.mp (hmem v hv)

variable [Policy σ n]

/-- Partition rules for the local policy operations. The child and
refinement rules compose their own changes with the finer recursive
effect; recovery restores the parent's level convention. -/
structure ReachPolicy (G : Colored n k) (ctx : Ctx n) (inf tcLevel : Nat)
    (view : σ → Search n) : Prop where
  visit : ∀ level numcells st, 1 ≤ level → SearchOk G level numcells (view st) →
    let r := Policy.visit ctx level numcells st
    SearchOk G level r.1 (view r.2.2) ∧
      ∀ out, SearchOut G level level (view r.2.2) (view out) →
        SearchOut G (level - 1) level (view st) (view out)
  record : ∀ level code numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.recordFirst (n := n) level code st)
  compare : ∀ level code numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.compareCodes (n := n) level code st)
  target : ∀ first level numcells st, 1 ≤ level → SearchOk G level numcells (view st) →
    let r := Policy.chooseTarget first ctx tcLevel level numcells st
    Local G view level numcells st r.2.2.2 ∧ Target view level r.1.toNat r.2.1 r.2.2.2
  firstterminal : ∀ level numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.firstterminal (n := n) level st)
  classify : ∀ level numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.classify ctx level numcells st).2
  leaf : ∀ leaf level numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.leafExit (n := n) leaf level st).2
  cheap : ∀ first level numcells st, SearchOk G level numcells (view st) →
    Local G view level numcells st (Policy.cheapCheck (n := n) first level st)
  child : ∀ first level numcells tc tv cell st, 1 ≤ level →
    SearchOk G level numcells (view st) → Target view level tc cell st → cell.mem tv = true →
    let child := Policy.child (n := n) first level tc tv st
    SearchOk G (level + 1) (numcells + 1) (view child) ∧
      ∀ out, SearchOut G level (level + 1) (view child) (view out) →
        SearchOut G level level (view st) (view out)
  afterChild : ∀ level tv st,
    FrameEq view st (Policy.afterChildFirst (n := n) level tv st)
  leave : ∀ tv st, FrameEq view st (Policy.leaveChild (n := n) tv st)
  short : ∀ (cell : VSet n) (st : σ) v,
    (Policy.shortprune (n := n) cell st).mem v = true → cell.mem v = true
  long : ∀ (cell : VSet n) (st : σ) v,
    (Policy.longprune (n := n) cell st).mem v = true → cell.mem v = true
  recover : ∀ level numcells st out, 1 ≤ level → SearchOk G level numcells (view st) →
    SearchOut G level level (view st) (view out) →
    Local G view level numcells st (Policy.recover (n := n) inf level out)
  afterSweep : ∀ first level size index st,
    FrameEq view st (Policy.afterSweep (n := n) first level size index st)

/-- Entry and exit assertions for partition reachability. They apply
also to truncated searches: exhaustion preserves all frame facts. -/
def reachContract (G : Colored n k) (view : σ → Search n) : Contract σ n where
  nodePre _ _ level numcells st := 1 ≤ level ∧ SearchOk G level numcells (view st)
  nodePost _ _ level _ st result := SearchOut G (level - 1) level (view st) (view result.2)
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ SearchOk G level numcells (view st) ∧ Target view level tc cell st ∧
      ∀ v, cursor = some v → cell.mem v = true
  sweepPost _ _ _ level _ _ _ _ _ _ st result :=
    SearchOut G level level (view st) (view result.2.2)

variable {G : Colored n k} {ctx : Ctx n} {inf tcLevel : Nat}
  {view : σ → Search n}

/-- Finishing a node's child sweep preserves its frame for every exit. -/
theorem ReachPolicy.finish (h : ReachPolicy G ctx inf tcLevel view)
    {fuel : Nat} {next : SweepFn σ n}
    (hnext : (reachContract G view).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells tc size : Nat) (cell : VSet n) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (htarget : Target view level tc cell st) :
    let tv := cell.nextElem none
    let r := next first level numcells tc (tv.getD 0) tv cell 0 st
    SearchOut G level level (view st)
      (view (Id.run (match r.1 with
        | .done => pure (Exit.unwind (level - 1) false,
            Policy.afterSweep (n := n) first level size r.2.1 r.2.2)
        | _ => pure (r.1, r.2.2))).2) := by
  have hout := hnext first level numcells tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 st
    ⟨hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv⟩
  dsimp only [reachContract] at hout
  dsimp only
  generalize hr : next first level numcells tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 st = r at hout ⊢
  obtain ⟨exit, index, out⟩ := r
  cases exit with
  | done => exact (h.afterSweep first level size index out).out hout
  | unwind => exact hout
  | fuel => exact hout

/-- Local partition rules compose across refinement and one node's
decisions, assuming the child sweep has its frame effect. -/
theorem ReachPolicy.node_step (h : ReachPolicy G ctx inf tcLevel view)
    {fuel : Nat} {next : SweepFn σ n}
    (hnext : (reachContract G view).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st)) :
    SearchOut G (level - 1) level (view st)
      (view (nodeStep ctx tcLevel next first level numcells st).2) := by
  have hv := h.visit level numcells st hlevel hok
  unfold nodeStep
  generalize hr : Policy.visit ctx level numcells st = r at hv ⊢
  obtain ⟨nc, code, refined⟩ := r
  obtain ⟨hokR, hvisit⟩ := hv
  let compared := if first then Policy.recordFirst (n := n) level code refined
    else Policy.compareCodes (n := n) level code refined
  have hcomp : Local G view level nc refined compared := by
    cases first
    · exact h.compare level code nc refined hokR
    · exact h.record level code nc refined hokR
  have ht := h.target first level nc compared hlevel hcomp.ok
  change SearchOut G (level - 1) level (view st)
    (view (Id.run (do
      let (tc, tcell, size, st) := Policy.chooseTarget first ctx tcLevel level nc compared
      let mut st := st
      if first then
        if nc == n then
          return (Exit.unwind (level - 1) false, Policy.firstterminal (n := n) level st)
      else
        let (leaf, st') := Policy.classify ctx level nc st
        let (exit, st') := Policy.leafExit (n := n) leaf level st'
        st := st'
        match exit with
        | .done => pure ()
        | _ => return (exit, st)
      st := Policy.cheapCheck (n := n) first level st
      let tv := tcell.nextElem none
      let (exit, index, st') := next first level nc tc.toNat (tv.getD 0) tv tcell 0 st
      match exit with
      | .done => return (Exit.unwind (level - 1) false,
          Policy.afterSweep (n := n) first level size index st')
      | _ => return (exit, st'))).2)
  generalize htval : Policy.chooseTarget first ctx tcLevel level nc compared = t at ht ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨htlocal, htarget⟩ := ht
  have hprepared := hcomp.trans htlocal
  have hfinish : ∀ prepared, Local G view level nc refined prepared →
      Target view level tc.toNat cell prepared →
      SearchOut G (level - 1) level (view st)
        (view (let ready := Policy.cheapCheck (n := n) first level prepared
          let tv := cell.nextElem none
          let r := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
          (Id.run (match r.1 with
          | .done => pure (Exit.unwind (level - 1) false,
              Policy.afterSweep (n := n) first level size r.2.1 r.2.2)
          | _ => pure (r.1, r.2.2))).2)) := by
    intro prepared hp ht
    have hc := h.cheap first level nc prepared hp.ok
    apply hvisit
    apply (hp.trans hc).effect.trans
    exact h.finish hnext first level nc tc.toNat size cell _ hlevel hc.ok
      (ht.of_out hc.effect)
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hvisit _ (hprepared.trans (h.firstterminal level nc targeted hprepared.ok)).effect
    · exact hfinish targeted hprepared htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hcl := h.classify level nc targeted hprepared.ok
    generalize hcval : Policy.classify ctx level nc targeted = classified at hcl ⊢
    obtain ⟨leaf, classified⟩ := classified
    have hle := h.leaf leaf level nc classified hcl.ok
    generalize hlval : Policy.leafExit (n := n) leaf level classified = result at hle ⊢
    obtain ⟨exit, out⟩ := result
    have hlocal := hprepared.trans (hcl.trans hle)
    cases exit with
    | done => exact hfinish out hlocal ((htarget.of_out hcl.effect).of_out hle.effect)
    | unwind => exact hvisit _ hlocal.effect
    | fuel => exact hvisit _ hlocal.effect

/-- Consume a child's exit, prune the remaining target, and recover the
parent before continuing the sweep. -/
theorem ReachPolicy.advance (h : ReachPolicy G ctx inf tcLevel view)
    {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (reachContract G view).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (base out : σ) (exit : Exit)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view base))
    (htarget : Target view level tc cell base)
    (hout : SearchOut G level level (view base) (view out)) :
    SearchOut G level level (view base) (view (Generic.advance inf next first level numcells tc tv1 tv cell index out exit).2.2) := by
  unfold Generic.advance
  have hr := h.recover level numcells base out hlevel hok hout
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      SearchOut G level level (view base) (view
        (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
          (if first && Policy.orbit (n := n) (Policy.recover (n := n) inf level out) tv == tv1
            then index + 1 else index)
          (Policy.recover (n := n) inf level out)).2.2) := by
    intro smaller hsub
    apply hr.effect.trans
    exact hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨hlevel, hr.ok, (htarget.subset hsub).of_out hr.effect,
        fun v hv => VSet.nextElem_mem hv⟩
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      SearchOut G level level (view base) (view (Generic.resume inf next first level numcells tc tv1 tv smaller index out).2.2) := by
    intro smaller hsub
    unfold Generic.resume
    split
    · exact hcontinue _ (fun v hv => hsub v (h.long smaller out v hv))
    · exact hcontinue _ hsub
  cases exit with
  | fuel => exact hout
  | done => exact hlong cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hout
    · cases short with
      | false =>
        simpa only [Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong cell (fun _ hv => hv)
      | true =>
        simpa only [ite_true, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong _ (fun v hv => h.short cell out v hv)

/-- One sweep iteration preserves its parent frame when both recursive
continuations preserve theirs. -/
theorem ReachPolicy.sweep_step (h : ReachPolicy G ctx inf tcLevel view)
    {fuel cfuel : Nat} {descend : NodeFn σ} {next : SweepFn σ n}
    (hdescend : (reachContract G view).nodeValid fuel descend)
    (hnext : (reachContract G view).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (htarget : Target view level tc cell st) (htv : cell.mem tv = true) :
    SearchOut G level level (view st)
      (view (sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2) := by
  have hc := h.child first level numcells tc tv cell st hlevel hok htarget htv
  have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1)
    (Policy.child (n := n) first level tc tv st) ⟨by omega, hc.1⟩
  dsimp only [reachContract] at hd
  simp only [Nat.add_sub_cancel] at hd
  unfold sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize hcall : descend (first && tv == tv1) (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = result at hd ⊢
    obtain ⟨exit, out⟩ := result
    have heffect := hc.2 out hd
    have hleave : ∀ returned, SearchOut G level level (view st) (view returned) →
        SearchOut G level level (view st)
          (view (Policy.leaveChild (n := n) tv returned)) :=
      fun returned hr => (h.leave tv returned).out hr
    split
    · exact h.advance hnext first level numcells tc tv1 tv index cell st _ exit hlevel hok
        htarget (hleave _ ((h.afterChild level tv1 out).out heffect))
    · exact h.advance hnext first level numcells tc tv1 tv index cell st _ exit hlevel hok
        htarget (hleave _ heffect)
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv⟩

/-- The local partition rules instantiate the generic recursion contract. -/
theorem ReachPolicy.sound (h : ReachPolicy G ctx inf tcLevel view) :
    SoundPolicy ctx inf tcLevel (reachContract G view) where
  node_zero := fun _ level _ _ hin => SearchOut.refl G (level - 1) level hin.2.reach
  node_step := fun _ _ hnext first level numcells st hin =>
    h.node_step hnext first level numcells st hin.1 hin.2
  sweep_none := fun _ _ _ level _ _ _ _ _ _ hin => SearchOut.refl G level level hin.2.1.reach
  sweep_zero := fun _ _ level _ _ _ _ _ _ _ hin => SearchOut.refl G level level hin.2.1.reach
  sweep_step := fun _ _ _ _ hdescend hnext first level numcells tc tv1 tv cell index st hin =>
    h.sweep_step hdescend hnext first level numcells tc tv1 tv index cell st
      hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)

/-- Every policy satisfying the local partition rules preserves node reachability. -/
theorem node_reach (h : ReachPolicy G ctx inf tcLevel view)
    (first : Bool) (fuel level numcells : Nat) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st)) :
    SearchOut G (level - 1) level (view st)
      (view (node first ctx inf tcLevel fuel level numcells st).2) :=
  node_sound h.sound first fuel level numcells st ⟨hlevel, hok⟩

/-- Every policy satisfying the local partition rules preserves sweep reachability. -/
theorem sweep_reach (h : ReachPolicy G ctx inf tcLevel view)
    (first : Bool) (fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (htarget : Target view level tc cell st)
    (hcursor : ∀ v, cursor = some v → cell.mem v = true) :
    SearchOut G level level (view st)
      (view (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2) :=
  sweep_sound h.sound first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hlevel, hok, htarget, hcursor⟩

end Hex.GraphIso.Nauty.Generic
