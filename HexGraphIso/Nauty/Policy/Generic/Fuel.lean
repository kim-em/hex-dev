/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n k : Nat} {σ : Type}

/-- A sweep has enough iterations to inspect every remaining vertex. -/
def CursorFuel (n fuel : Nat) (cursor : Option Nat) : Prop :=
  ∀ v, cursor = some v → n ≤ v + fuel

/-- Advancing a bitset cursor consumes at most one unit of the bound. -/
theorem CursorFuel.next {cfuel tv : Nat} {cell : VSet n}
    (h : n ≤ tv + (cfuel + 1)) : CursorFuel n cfuel (cell.nextElem (some tv)) := by
  intro v hv
  have hnext := ((VSet.nextElem_eq_some_iff).mp hv).2.1
  change tv + 1 ≤ v at hnext
  omega

/-- Partition reachability together with conditional absence of exhaustion.
The partition assertions hold even when the bounds are insufficient. -/
def fuelContract (G : Colored n k) (view : σ → Search n) : Contract σ n where
  nodePre := (reachContract G view).nodePre
  nodePost fuel first level numcells st result :=
    (reachContract G view).nodePost fuel first level numcells st result ∧
      (n + 1 ≤ level + fuel → result.1 ≠ .fuel)
  sweepPre := (reachContract G view).sweepPre
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result :=
    (reachContract G view).sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st result ∧
      (n ≤ level + fuel → CursorFuel n cfuel cursor → result.1 ≠ .fuel)

/-- Forget the node exhaustion guarantee while retaining its frame effect. -/
theorem fuel_node_reach {G : Colored n k} {view : σ → Search n}
    {fuel : Nat} {f : NodeFn σ} (h : (fuelContract G view).nodeValid fuel f) :
    (reachContract G view).nodeValid fuel f :=
  fun first level numcells st hin => (h first level numcells st hin).1

/-- Forget the sweep exhaustion guarantee while retaining its frame effect. -/
theorem fuel_sweep_reach {G : Colored n k} {view : σ → Search n}
    {fuel cfuel : Nat} {f : SweepFn σ n}
    (h : (fuelContract G view).sweepValid fuel cfuel f) :
    (reachContract G view).sweepValid fuel cfuel f :=
  fun first level numcells tc tv1 cursor cell index st hin =>
    (h first level numcells tc tv1 cursor cell index st hin).1

variable {γ : Type} [Policy σ n (γ := γ)]
variable {G : Colored n k} {ctx : γ} {inf tcLevel : Nat} {view : σ → Search n}

/-- Completing a child sweep cannot create exhaustion. -/
private theorem finish_safe {next : SweepFn σ n} {first : Bool}
    {level numcells tc size : Nat} {cell : VSet n} {st : σ}
    (hsafe : (next first level numcells tc ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 st).1 ≠ .fuel) :
    (Id.run (do
      let (exit, index, out) := next first level numcells tc ((cell.nextElem none).getD 0)
        (cell.nextElem none) cell 0 st
      match exit with
      | .done => return (Exit.unwind (level - 1) false,
          Policy.afterSweep (n := n) first level size index out)
      | _ => return (exit, out))).1 ≠ .fuel := by
  generalize hr : next first level numcells tc ((cell.nextElem none).getD 0)
    (cell.nextElem none) cell 0 st = r at hsafe ⊢
  obtain ⟨exit, index, out⟩ := r
  cases exit <;> simp_all

/-- Refinement and local node decisions cannot exhaust a sufficient bound. -/
theorem nodeStep_safe (h : ReachPolicy G ctx inf tcLevel view)
    (hleaf : ∀ leaf level (st : σ), (Policy.leafExit (n := n) leaf level st).1 ≠ .fuel)
    {fuel : Nat} {next : SweepFn σ n}
    (hnext : (fuelContract G view).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (hfuel : n + 1 ≤ level + (fuel + 1)) :
    (nodeStep ctx tcLevel next first level numcells st).1 ≠ .fuel := by
  have hv := h.visit level numcells st hlevel hok
  unfold nodeStep
  generalize hr : Policy.visit ctx level numcells st = r at hv ⊢
  obtain ⟨nc, code, refined⟩ := r
  obtain ⟨hokR, _⟩ := hv
  let compared := if first then Policy.recordFirst (n := n) level code refined
    else Policy.compareCodes (n := n) level code refined
  have hcomp : Local G view level nc refined compared := by
    cases first
    · exact h.compare level code nc refined hokR
    · exact h.record level code nc refined hokR
  have ht := h.target first level nc compared hlevel hcomp.ok
  change (Id.run (do
    let (tc, cell, size, targeted) := Policy.chooseTarget first ctx tcLevel level nc compared
    let mut prepared := targeted
    if first then
      if nc == n then return (Exit.unwind (level - 1) false,
        Policy.firstterminal (n := n) level prepared)
    else
      let (leaf, classified) := Policy.classify ctx level nc prepared
      let (exit, out) := Policy.leafExit (n := n) leaf level classified
      prepared := out
      match exit with
      | .done => pure ()
      | _ => return (exit, prepared)
    prepared := Policy.cheapCheck (n := n) first level prepared
    let tv := cell.nextElem none
    let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 prepared
    match exit with
    | .done => return (Exit.unwind (level - 1) false,
        Policy.afterSweep (n := n) first level size index out)
    | _ => return (exit, out))).1 ≠ .fuel
  generalize htval : Policy.chooseTarget first ctx tcLevel level nc compared = t at ht ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨htlocal, htarget⟩ := ht
  have hfinish : ∀ prepared, SearchOk G level nc (view prepared) →
      Target view level tc.toNat cell prepared →
      (Id.run (do
        let ready := Policy.cheapCheck (n := n) first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Exit.unwind (level - 1) false,
            Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).1 ≠ .fuel := by
    intro prepared hp ht
    have hc := h.cheap first level nc prepared hp
    apply finish_safe
    apply (hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hlevel, hc.ok, ht.of_out hc.effect, fun v hv => VSet.nextElem_mem hv⟩).2
    · omega
    · intro v _
      omega
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
    split
    · simp
    · exact hfinish targeted htlocal.ok htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hcl := h.classify level nc targeted htlocal.ok
    generalize hcval : Policy.classify ctx level nc targeted = classified at hcl ⊢
    obtain ⟨leaf, classified⟩ := classified
    have hle := h.leaf leaf level nc classified hcl.ok
    have hsafe := hleaf leaf level classified
    generalize hlval : Policy.leafExit (n := n) leaf level classified = result at hle hsafe ⊢
    obtain ⟨exit, out⟩ := result
    cases exit with
    | done => exact hfinish out hle.ok ((htarget.of_out hcl.effect).of_out hle.effect)
    | unwind => simp
    | fuel => exact (hsafe rfl).elim

/-- Returning from a child and advancing the target cursor preserves a
sufficient sweep bound. -/
private theorem advance_safe (h : ReachPolicy G ctx inf tcLevel view)
    {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (fuelContract G view).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (base out : σ) (exit : Exit)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view base))
    (htarget : Target view level tc cell base)
    (hout : SearchOut G level level (view base) (view out)) (hsafe : exit ≠ .fuel)
    (hfuel : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1)) :
    (Generic.advance inf next first level numcells tc tv1 tv cell index out exit).1 ≠ .fuel := by
  unfold Generic.advance
  have hr := h.recover level numcells base out hlevel hok hout
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && Policy.orbit (n := n) (Policy.recover (n := n) inf level out) tv == tv1
          then index + 1 else index)
        (Policy.recover (n := n) inf level out)).1 ≠ .fuel := by
    intro smaller hsub
    exact (hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨hlevel, hr.ok, (htarget.subset hsub).of_out hr.effect,
        fun v hv => VSet.nextElem_mem hv⟩).2 hfuel (CursorFuel.next hcursor)
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      (Generic.resume inf next first level numcells tc tv1 tv smaller index out).1 ≠ .fuel := by
    intro smaller hsub
    unfold Generic.resume
    split
    · exact hcontinue _ (fun v hv => hsub v (h.long smaller out v hv))
    · exact hcontinue _ hsub
  cases exit with
  | fuel => exact (hsafe rfl).elim
  | done => exact hlong cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
    split
    · simp
    · cases short with
      | false =>
        simpa only [Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.fst] using hlong cell (fun _ hv => hv)
      | true =>
        simpa only [ite_true, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.fst] using hlong _ (fun v hv => h.short cell out v hv)

/-- The child increases the level and the remaining sweep increases the
cursor, so both recursive calls have sufficient bounds. -/
theorem sweepStep_safe (h : ReachPolicy G ctx inf tcLevel view)
    {fuel cfuel : Nat} {descend : NodeFn σ} {next : SweepFn σ n}
    (hdescend : (fuelContract G view).nodeValid fuel descend)
    (hnext : (fuelContract G view).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (htarget : Target view level tc cell st) (htv : cell.mem tv = true)
    (hfuel : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1)) :
    (sweepStep inf descend next first level numcells tc tv1 tv cell index st).1 ≠ .fuel := by
  have hc := h.child first level numcells tc tv cell st hlevel hok htarget htv
  have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1)
    (Policy.child (n := n) first level tc tv st) ⟨by omega, hc.1⟩
  have hdsafe := hd.2 (by omega)
  have hdout := hd.1
  dsimp only [reachContract] at hdout
  simp only [Nat.add_sub_cancel] at hdout
  unfold sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  split
  · generalize hcall : descend (first && tv == tv1) (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = result at hdout hdsafe ⊢
    obtain ⟨exit, out⟩ := result
    have heffect := hc.2 out hdout
    have hleave : ∀ returned, SearchOut G level level (view st) (view returned) →
        SearchOut G level level (view st)
          (view (Policy.leaveChild (n := n) tv returned)) :=
      fun returned hr => (h.leave tv returned).out hr
    split
    · exact advance_safe h hnext first level numcells tc tv1 tv index cell st _ exit hlevel hok
        htarget (hleave _ ((h.afterChild level tv1 out).out heffect)) hdsafe hfuel hcursor
    · exact advance_safe h hnext first level numcells tc tv1 tv index cell st _ exit hlevel hok
        htarget (hleave _ heffect) hdsafe hfuel hcursor
  · exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv⟩).2 hfuel (CursorFuel.next hcursor)

/-- The partition rules and non-exhausting leaf actions suffice for the
generic search's level and cursor bounds. -/
theorem fuel_sound (h : ReachPolicy G ctx inf tcLevel view)
    (hleaf : ∀ leaf level (st : σ), (Policy.leafExit (n := n) leaf level st).1 ≠ .fuel) :
    SoundPolicy ctx inf tcLevel (fuelContract G view) where
  node_zero := by
    intro first level numcells st hin
    refine ⟨SearchOut.refl G (level - 1) level hin.2.reach, ?_⟩
    intro hfuel
    have := hin.2.bc
    have := bcount_le (view st).ptn level n
    omega
  node_step := by
    intro fuel next hnext first level numcells st hin
    exact ⟨h.node_step (fuel_sweep_reach hnext) first level numcells st hin.1 hin.2,
      nodeStep_safe h hleaf hnext first level numcells st hin.1 hin.2⟩
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact ⟨SearchOut.refl G level level hin.2.1.reach, fun _ _ => by simp⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    refine ⟨SearchOut.refl G level level hin.2.1.reach, ?_⟩
    intro _ hcursor
    have hv := VSet.mem_lt (hin.2.2.2 tv rfl)
    have hf := hcursor tv rfl
    omega
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st hin
    exact ⟨h.sweep_step (fuel_node_reach hdescend) (fuel_sweep_reach hnext)
      first level numcells tc tv1 tv index cell st hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      fun hfuel hcursor => sweepStep_safe h hdescend hnext
        first level numcells tc tv1 tv index cell st hin.1 hin.2.1 hin.2.2.1
        (hin.2.2.2 tv rfl) hfuel (hcursor tv rfl)⟩

/-- A valid node cannot exhaust a bound reaching beyond the maximum level. -/
theorem node_noFuel (h : ReachPolicy G ctx inf tcLevel view)
    (hleaf : ∀ leaf level (st : σ), (Policy.leafExit (n := n) leaf level st).1 ≠ .fuel)
    (first : Bool) (fuel level numcells : Nat) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (hfuel : n + 1 ≤ level + fuel) :
    (node first ctx inf tcLevel fuel level numcells st).1 ≠ .fuel :=
  (node_sound (fuel_sound h hleaf) first fuel level numcells st ⟨hlevel, hok⟩).2 hfuel

/-- A valid sweep cannot exhaust sufficient level and cursor bounds. -/
theorem sweep_noFuel (h : ReachPolicy G ctx inf tcLevel view)
    (hleaf : ∀ leaf level (st : σ), (Policy.leafExit (n := n) leaf level st).1 ≠ .fuel)
    (first : Bool) (fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : σ)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells (view st))
    (htarget : Target view level tc cell st)
    (hcursor : ∀ v, cursor = some v → cell.mem v = true)
    (hfuel : n ≤ level + fuel) (hcfuel : CursorFuel n cfuel cursor) :
    (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 ≠ .fuel :=
  (sweep_sound (fuel_sound h hleaf) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hlevel, hok, htarget, hcursor⟩).2 hfuel hcfuel

end Hex.GraphIso.Nauty.Generic
