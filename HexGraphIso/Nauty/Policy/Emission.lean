/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Preserve
public import HexGraphIso.Nauty.Policy.Instance
public import HexGraphIso.Nauty.Policy.First.Run
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Emission

variable {n : Nat} {κ : Type}

/-- The state shared by the proofs about the discovery and emission lists. -/
structure Log where
  trace : Array (Array Nat)
  emitted : Array (Array Nat)
  orbits : Array Nat
  numorbits : Nat
  numgenerators : Nat

@[expose] def log (st : SearchState n κ) : Log :=
  ⟨st.genTrace, st.emitted, st.orbits, st.numorbits, st.numgenerators⟩

@[expose] def Log.join (l : Log) (p : Array Nat) (n : Nat) : Log :=
  let (orbits, count) := orbjoin l.orbits p n
  { l with trace := l.trace.push p, orbits := orbits, numorbits := count }

@[expose] def Log.emit (l : Log) (p : Array Nat) : Log :=
  { l with emitted := l.emitted.push p, numgenerators := l.numgenerators + 1 }

private theorem prune_log (level : Nat) (st : SearchState n κ) :
    log (pruneReturn level st).2 = log st := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · unfold pushAuto; split <;> rfl
  · rfl

/-- Both automorphism classifications update the orbit array and discovery
trace. Only a canonical match that changes the orbit count is emitted. -/
theorem leaf_log (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    log (leafExit leaf level st).2 =
      match leaf with
      | .autoFirst => ((log st).join st.workperm n).emit st.workperm
      | .autoCanon =>
        let joined := (log st).join st.workperm n
        if joined.numorbits == (log st).numorbits then joined else joined.emit st.workperm
      | _ => log st := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite log, prune_log]
  all_goals try rfl
  all_goals simp only [admit, pushAuto, log, Log.join, Log.emit, Id.run_pure]
  all_goals repeat' first | rfl | split
  all_goals simp_all only [Bool.false_eq_true, ↓reduceIte]

/-- The reported list is a subsequence of the discovery trace and has
exactly the length recorded by nauty's generator counter. -/
structure Valid (l : Log) : Prop where
  sublist : List.Sublist l.emitted.toList l.trace.toList
  size : l.emitted.size = l.numgenerators

theorem Valid.leaf (leaf : Leaf) (level : Nat) (st : SearchState n κ)
    (h : Valid (log st)) : Valid (log (leafExit leaf level st).2) := by
  rw [leaf_log]
  have hj : Valid ((log st).join st.workperm n) := by
    refine ⟨?_, h.size⟩
    simp only [Log.join, Array.toList_push]
    exact h.sublist.trans (List.sublist_append_left _ _)
  have he : Valid (((log st).join st.workperm n).emit st.workperm) := by
    refine ⟨?_, ?_⟩
    · simp only [Log.emit, Log.join, Array.toList_push]
      exact h.sublist.append (List.Sublist.refl _)
    · simp only [Log.emit, Log.join, Array.size_push, h.size]
  cases leaf
  all_goals first | exact h | exact he | (dsimp only; split <;> assumption)

/-- Later search states retain the earlier discovery and emission lists. -/
structure Extends (before after : Log) : Prop where
  trace : List.Subset before.trace.toList after.trace.toList
  emitted : List.Subset before.emitted.toList after.emitted.toList

theorem Extends.refl (l : Log) : Extends l l :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem Extends.trans {a b c : Log} (hab : Extends a b) (hbc : Extends b c) : Extends a c :=
  ⟨fun _ h => hbc.trace (hab.trace h), fun _ h => hbc.emitted (hab.emitted h)⟩

theorem leaf_extends (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    Extends (log st) (log (leafExit leaf level st).2) := by
  rw [leaf_log]
  have hj : Extends (log st) ((log st).join st.workperm n) := by
    refine ⟨?_, fun _ h => h⟩
    intro γ hγ
    simp only [Log.join, Array.toList_push, List.mem_append]
    exact .inl hγ
  have he : Extends (log st) (((log st).join st.workperm n).emit st.workperm) := by
    refine ⟨hj.trace, ?_⟩
    intro γ hγ
    simp only [Log.emit, Log.join, Array.toList_push, List.mem_append]
    exact .inl hγ
  cases leaf
  all_goals first | exact .refl _ | exact he | (dsimp only; split <;> assumption)

theorem compare_log (level code : Nat) (st : SearchState n κ) :
    log (compareCodes level code st) = log st := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite log]
  repeat' first | rfl | split

theorem cheap_log (first : Bool) (level : Nat) (st : SearchState n κ) :
    log (cheapCheck first level st) = log st := by
  unfold cheapCheck
  split <;> rfl

theorem child_log (first : Bool) (level tc tv : Nat) (st : SearchState n κ) :
    log (child first level tc tv st) = log st := by
  cases first <;> rfl

theorem recover_log (inf level : Nat) (st : SearchState n κ) :
    log (Nauty.recover inf level st) = log st := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite log]
  repeat' first | rfl | split

theorem afterSweep_log (first : Bool) (level size index : Nat) (st : SearchState n κ) :
    log (afterSweep first level size index st) = log st := by
  unfold afterSweep
  split <;> rfl

private theorem target_log (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) : log (chooseTarget first ctx tcLevel level numcells st).2.2.2 = log st := by
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite log]
  repeat' first | rfl | split

private theorem classify_log (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    log (classify ctx level numcells st).2 = log st := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite log, scatter_eq]
  simp only [log, ite_self]

/-- For the dense policy, any invariant on the emission log only needs a
local preservation proof at the leaf action. -/
theorem preserve (ctx : Ctx n) (inf tcLevel : Nat) (P : Log → Prop)
    (leaf : ∀ v level (st : Search n), P (log st) → P (log (leafExit v level st).2)) :
    Generic.Preserve ctx inf tcLevel (fun st : Search n => P (log st)) where
  visit := fun _ _ _ h => h
  record := fun _ _ _ h => h
  compare := fun level code st h => (compare_log level code st).symm ▸ h
  target := fun first level numcells st h => (target_log first ctx tcLevel level numcells st).symm ▸ h
  terminal := fun _ _ h => h
  classify := fun level numcells st h => (classify_log ctx level numcells st).symm ▸ h
  leaf := leaf
  cheap := fun first level st h => (cheap_log first level st).symm ▸ h
  child := fun first level tc tv st h => (child_log first level tc tv st).symm ▸ h
  afterChild := fun _ _ _ h => h
  leave := fun _ _ h => h
  recover := fun level st h => (recover_log inf level st).symm ▸ h
  afterSweep := fun first level size index st h => (afterSweep_log first level size index st).symm ▸ h

/-- Both parts of the log grow through a complete dense search call. -/
theorem node_extends (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) : Extends (log st) (log (node first ctx inf tcLevel fuel level numcells st).2) := by
  rw [node_eq_generic]
  exact Generic.node_sound
    (preserve ctx inf tcLevel (Extends (log st)) (fun v l s h => h.trans (leaf_extends v l s))).sound
    first fuel level numcells st (.refl _)

theorem sweep_extends (first : Bool) (ctx : Ctx n) (inf tcLevel fuel cfuel : Nat)
    (level numcells tc tv1 : Nat) (cursor : Option Nat) (cell : VSet n) (index : Nat)
    (st : Search n) :
    Extends (log st) (log (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1
      cursor cell index st).2.2) := by
  rw [sweep_eq_generic]
  exact Generic.sweep_sound
    (preserve ctx inf tcLevel (Extends (log st)) (fun v l s h => h.trans (leaf_extends v l s))).sound
    first fuel cfuel level numcells tc tv1 cursor cell index st (.refl _)

theorem prepare_log (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    log (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2 = log st :=
  target_log true ctx tcLevel level _ _

/-- Installing the first terminal leaf leaves the emission log unchanged. -/
theorem terminal_log (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n)
    (hdisc : (Generic.prepareFirst ctx tcLevel level numcells st).1 = n) :
    log (node true ctx inf tcLevel (fuel + 1) level numcells st).2 = log st := by
  rw [node_first]
  let r := Generic.prepareFirst ctx tcLevel level numcells st
  have hd : r.1 = n := hdisc
  change log (Id.run (if r.1 == n then pure (.unwind (level - 1) false, firstterminal level r.2.2.2.2)
    else
      let s := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (cheapCheck true level r.2.2.2.2)
      match s.1 with
      | .done => pure (.unwind (level - 1) false, afterSweep true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => pure (s.1, s.2.2))).2 = log st
  simp only [hd, beq_self_eq_true, ite_true, Id.run_pure]
  exact prepare_log ctx tcLevel level numcells st

/-- The completed first-path node retains the log of its executed sweep. -/
theorem first_log (ctx : Ctx n) (inf tcLevel fuel level numcells tv : Nat) (st : Search n)
    (hopen : (Generic.prepareFirst ctx tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    log (node true ctx inf tcLevel (fuel + 1) level numcells st).2 =
      log (sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat tv (some tv)
        r.2.2.1 0 (cheapCheck true level r.2.2.2.2)).2.2 := by
  intro r
  rw [node_first]
  have hnc : r.1 ≠ n := hopen
  have hpick : r.2.2.1.nextElem none = some tv := htv
  change log (Id.run (if r.1 == n then pure (.unwind (level - 1) false, firstterminal level r.2.2.2.2)
    else
      let s := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (cheapCheck true level r.2.2.2.2)
      match s.1 with
      | .done => pure (.unwind (level - 1) false, afterSweep true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => pure (s.1, s.2.2))).2 = _
  simp only [beq_eq_false_iff_ne.mpr hnc, Bool.false_eq_true, ite_false, hpick, Option.getD_some]
  generalize h : sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat tv (some tv)
    r.2.2.1 0 (cheapCheck true level r.2.2.2.2) = out
  obtain ⟨exit, index, out⟩ := out
  cases exit
  · exact afterSweep_log true level r.2.2.2.1 index out
  · rfl
  · rfl

/-- The dense search reports exactly the recorded count, in discovery order. -/
theorem run_valid (n : Nat) (g : Array (VSet n)) (lab : Array Nat) (ends : List Nat) :
    Valid (log (runState n g lab ends).2) := by
  unfold runState
  split
  · exact ⟨.refl _, rfl⟩
  · rw [node_eq_generic]
    exact Generic.node_sound (preserve { g } (n + 2) 100 Valid Valid.leaf).sound
      true (n + 2) 1 ends.length _ ⟨.refl _, rfl⟩

end Hex.GraphIso.Nauty.Emission
