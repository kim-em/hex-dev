/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Positive capacity makes the newest slot readable even when insertion
overwrites the last slot of a full workspace. -/
theorem pushAuto_back {st : Search n} (hcap : 0 < st.wsCap) (pair : VSet n × VSet n) :
    (pushAuto st pair).autos.back? = some pair := by
  change (pushAuto st pair).view.autos.back? = some pair
  rw [view_pushAuto]
  exact Nauty.pushAuto_back hcap

/-- A valid workspace exposes the newly inserted pair to the short filter,
including the overwrite at capacity. -/
theorem RunInv.push_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (pair : VSet n × VSet n) :
    (pushAuto st pair).autos.back? = some pair :=
  pushAuto_back h.workspace.1 pair

/-- The short filter following an explicit admission reads that admission's pair. -/
theorem RunInv.auto_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) {leaf : Leaf} (level : Nat)
    (ha : leaf = .autoFirst ∨ leaf = .autoCanon) :
    (leafExit leaf level st).2.autos.back? = some (fmperm st.workperm n) := by
  rcases ha with rfl | rfl
  all_goals rw [leafExit_autos, admit_autos]
  all_goals exact h.push_back _

/-- The cheap prune tail exposes its frozen implicit pair to the short filter. -/
theorem RunInv.cheap_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) {leaf : Leaf} {level : Nat}
    (ha : leaf = .bad ∨ ∃ sr, leaf = .better sr) (hne : level ≠ st.noncheaplevel) :
    (leafExit leaf level st).2.autos.back? = some (fmptn st.lab st.ptn st.noncheaplevel n) := by
  rcases ha with rfl | ⟨sr, rfl⟩
  all_goals rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
  all_goals exact h.push_back _

/-- The shared prune tail requests a short filter only after admitting
its implicit pair at a level different from the saved boundary. -/
theorem pruneReturn_short {level target : Nat} {st : Search n}
    (h : (pruneReturn level st).1 = .unwind target true) : level ≠ st.noncheaplevel := by
  intro he
  unfold pruneReturn at h
  simp [he] at h

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

/-- The actual short flag supplies the premise for reading the newly
admitted implicit pair; no separate admission assumption is needed. -/
theorem RunInv.short_back {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) {leaf : Leaf} {level target : Nat}
    (ha : leaf = .bad ∨ ∃ sr, leaf = .better sr)
    (hexit : (leafExit leaf level st).1 = .unwind target true) :
    (leafExit leaf level st).2.autos.back? = some (fmptn st.lab st.ptn st.noncheaplevel n) :=
  h.cheap_back ha (leafExit_cheap_short ha hexit)

/-- Each short-prune request exposes the pair admitted by the same leaf
action. Only code 2 and the implicit prune tail can set this flag. -/
theorem leafExit_short_pair {st : Search n} (hcap : 0 < st.wsCap)
    {leaf : Leaf} {level target : Nat}
    (hexit : (leafExit leaf level st).1 = .unwind target true) :
    (leaf = .autoCanon ∧
      (leafExit leaf level st).2.autos.back? = some (fmperm st.workperm n)) ∨
    ((leaf = .bad ∨ ∃ sr, leaf = .better sr) ∧ level ≠ st.noncheaplevel ∧
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
    exact pushAuto_back hcap _
  | bad =>
    have hne := leafExit_cheap_short (Or.inl rfl) hexit
    refine Or.inr ⟨Or.inl rfl, hne, ?_⟩
    rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
    exact pushAuto_back hcap _
  | better sr =>
    have hne := leafExit_cheap_short (Or.inr ⟨sr, rfl⟩) hexit
    refine Or.inr ⟨Or.inr ⟨sr, rfl⟩, hne, ?_⟩
    rw [leafExit_autos, pruneReturn_autos, ite_eq_left (by simpa using hne)]
    exact pushAuto_back hcap _

/-- Recovery retains the pruning workspace seen by the just-completed child. -/
theorem recover_autos (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).autos = st.autos := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Both filters read the same workspace before and after parent recovery.
This lets the restored partition justify the filter that ran just before it. -/
theorem recover_filters (inf level : Nat) (cell : VSet n) (st : Search n) :
    let out := recoverLevels level (recoverPtn inf level st)
    Nauty.longprune cell out.fixedpts out.autos = Nauty.longprune cell st.fixedpts st.autos ∧
      shortprune cell out = shortprune cell st := by
  dsimp only
  constructor
  · rw [recover_fixed, recover_autos]
  · unfold shortprune
    rw [recover_autos]

/-- Fix-passing pairs at a sweep carry each vertex of the full
target cell to a surviving representative under a checked automorphism
stabilizing this partition and fixing its individualized path. -/
theorem SweepPre.window_carriers {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tc tv1 len : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st)
    (hn0 : 0 < n) (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n) :
    ∀ v, v < n → (windowSet n st.lab tc len).mem v = true →
      ∃ γ, checkAutom ctx.g γ = true ∧
        (∀ u, u < n → st.fixedpts.mem u = true → γ[u]! = u) ∧
        CellStab st.ptn level st.lab γ ∧
        (windowSet n st.lab tc len).mem γ[v]! = true ∧
        (Nauty.longprune (windowSet n st.lab tc len) st.fixedpts st.autos).mem γ[v]! = true :=
  Nauty.longprune_carried (labOk_of_reach h.partition.labSize h.partition.reach)
    h.partition.labSize h.partition.ptnSize (searchOk_end hn0 h.partition h.positive)
    hc hr h.local_pairs

end Hex.GraphIso.Nauty.Engine
