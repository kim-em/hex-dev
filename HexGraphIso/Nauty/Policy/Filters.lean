/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FixedState
import HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The shared prune tail requests a short filter only after admitting
its implicit pair at a level different from the saved boundary. -/
theorem pruneReturn_short {level target : Nat} {st : Search n}
    (h : (pruneReturn level st).1 = .unwind target true) : level ≠ st.noncheaplevel := by
  intro he
  unfold pruneReturn at h
  simp [he] at h

/-- The implicit prune tail returns no deeper than the parent of its
saved cheap boundary, including the signed-to-natural conversion. -/
theorem pruneReturn_bound {level target : Nat} {short : Bool} {st : Search n}
    (h : (pruneReturn level st).1 = .unwind target short) :
    target ≤ st.noncheaplevel - 1 := by
  unfold pruneReturn pushAuto at h
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at h
  repeat' split at h
  all_goals have ht := (Generic.Exit.unwind.inj h).1
  all_goals repeat' split at ht
  all_goals simp only [Int.ofNat_eq_natCast] at *
  all_goals omega

/-- Both implicit-pair leaf actions use the same bounded return target. -/
theorem leafExit_cheap_bound {level target : Nat} {short : Bool} {st : Search n} {leaf : Leaf}
    (ha : leaf = .bad ∨ ∃ sr, leaf = .better sr)
    (h : (leafExit leaf level st).1 = .unwind target short) :
    target ≤ st.noncheaplevel - 1 := by
  rcases ha with rfl | ⟨sr, rfl⟩
  all_goals unfold leafExit at h
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at h
  all_goals split at h
  all_goals
    have hb := pruneReturn_bound h
    exact hb

/-- With both saved ancestors below the node, every leaf return leaves
that node. The implicit return also respects the saved cheap boundary. -/
theorem leafExit_bound {level target : Nat} {short : Bool} {st : Search n} {leaf : Leaf}
    (hf : st.gcaFirst < level) (hc : st.gcaCanon < level)
    (hn : st.noncheaplevel ≤ level)
    (h : (leafExit leaf level st).1 = .unwind target short) : target < level := by
  cases leaf with
  | bad => have := leafExit_cheap_bound (Or.inl rfl) h; omega
  | better sr => have := leafExit_cheap_bound (Or.inr ⟨sr, rfl⟩) h; omega
  | internal =>
    change Generic.Exit.done = .unwind target short at h
    cases h
  | autoFirst | autoCanon =>
    unfold leafExit at h
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at h
    repeat' split at h
    all_goals have ht := (Generic.Exit.unwind.inj h).1
    all_goals simp only [admit_gca, admit_canon] at ht
    all_goals first | exact ht ▸ hf | exact ht ▸ hc

/-- A short code-2 return targets the saved canonical ancestor. -/
theorem leafExit_canon_target {level target : Nat} {st : Search n}
    (h : (leafExit .autoCanon level st).1 = .unwind target true) :
    target = (leafExit .autoCanon level st).2.gcaCanon := by
  rw [autoCanon_ancestor]
  unfold leafExit at h
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at h
  repeat' split at h
  all_goals simp only [Generic.Exit.unwind.injEq, admit_canon, Bool.false_eq_true, and_false] at h
  all_goals first | exact h.1.symm | contradiction

/-- A short return from a bad or better leaf satisfies the implicit-pair
admission test used by that very leaf action. -/
theorem leafExit_cheap_short {level target : Nat} {st : Search n} {leaf : Leaf}
    (ha : leaf = .bad ∨ ∃ sr, leaf = .better sr)
    (h : (leafExit leaf level st).1 = .unwind target true) : level ≠ st.noncheaplevel := by
  rcases ha with rfl | ⟨sr, rfl⟩
  all_goals unfold leafExit at h
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at h
  all_goals split at h
  all_goals
    have hp := pruneReturn_short h
    exact hp

/-- Each short-prune request exposes the pair admitted by the same leaf
action. Only code 2 and the implicit prune tail can set this flag. -/
theorem leafExit_short_pair {st : Search n} (hcap : 0 < st.wsCap)
    {leaf : Leaf} {level target : Nat}
    (hexit : (leafExit leaf level st).1 = .unwind target true) :
    (leaf = .autoCanon ∧
      (leafExit leaf level st).2.autos.back? = some (fmperm st.workperm n)) ∨
    ((leaf = .bad ∨ ∃ sr, leaf = .better sr) ∧
      (leafExit leaf level st).2.autos.back? = some (fmptn st.lab st.ptn st.noncheaplevel n)) := by
  cases leaf with
  | internal =>
    unfold leafExit at hexit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at hexit
    split at hexit <;> simp at hexit
  | autoFirst =>
    unfold leafExit at hexit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at hexit
    split at hexit <;> simp at hexit
  | autoCanon =>
    refine Or.inl ⟨rfl, ?_⟩
    rw [leafExit_autos, admit_autos]
    exact pushAuto_back hcap
  | bad =>
    have hne := leafExit_cheap_short (Or.inl rfl) hexit
    refine Or.inr ⟨Or.inl rfl, ?_⟩
    rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
    exact pushAuto_back hcap
  | better sr =>
    have hne := leafExit_cheap_short (Or.inr ⟨sr, rfl⟩) hexit
    refine Or.inr ⟨Or.inr ⟨sr, rfl⟩, ?_⟩
    rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
    exact pushAuto_back hcap

/-- Recovery retains the pruning workspace seen by the just-completed child. -/
theorem recover_autos (inf level : Nat) (st : Search n) :
    (Nauty.recover inf level st).autos = st.autos := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Both filters read the same workspace before and after parent recovery.
This lets the restored partition justify the filter that ran just before it. -/
theorem recover_filters (inf level : Nat) (cell : VSet n) (st : Search n) :
    let out := Nauty.recover inf level st
    Nauty.longprune cell out.fixedpts out.autos = Nauty.longprune cell st.fixedpts st.autos ∧
      shortprune cell out = shortprune cell st := by
  dsimp only
  constructor
  · rw [recover_fixed, recover_autos]
  · unfold shortprune
    rw [recover_autos]

end Hex.GraphIso.Nauty
