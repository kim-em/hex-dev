/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Boundary
public import HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Every workspace pair has checked realizers preserving the initial colours. -/
def PairsOk (G : Colored n k) (ctx : Ctx n) (st : Search n) : Prop :=
  AutosOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1 st.autos

/-- Equal workspaces have the same valid pairs. -/
theorem PairsOk.congr {G : Colored n k} {ctx : Ctx n} {st out : Search n}
    (h : PairsOk G ctx st) (ha : out.autos = st.autos) : PairsOk G ctx out := by
  unfold PairsOk
  rw [ha]
  exact h

/-- Appending or replacing a pair preserves the workspace ledger. -/
theorem PairsOk.push {G : Colored n k} {ctx : Ctx n} {st : Search n} {pair : VSet n × VSet n}
    (h : PairsOk G ctx st)
    (hp : PairOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1 pair.1 pair.2) :
    PairsOk G ctx (pushAuto st pair) := by
  have ha := autosOk_pushAuto (st := st) h hp

  exact ha

/-- Admission records the scratch permutation's explicit pair. -/
theorem admit_autos {κ : Type} (st : SearchState n κ) :
    (admit st).autos = (pushAuto st (fmperm st.workperm n)).autos := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

/-- A checked admission preserving the initial colours supplies a valid explicit pair. -/
theorem PairsOk.admit {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : PairsOk G ctx st) (hn0 : 0 < n)
    (hc : checkAutom ctx.g st.workperm = true) (hs : ColorStab G st.workperm) :
    PairsOk G ctx (Nauty.admit st) := by
  have hr := initial_nodeOk G hn0
  exact (h.push (pairOk_fmperm hr.labOk hr.labSize hr.ptnSize hr.ptnEnd hc hs)).congr
    (admit_autos st)

/-- The shared prune tail changes the workspace only by its frozen implicit pair. -/
theorem PairsOk.prune {G : Colored n k} {ctx : Ctx n} {st : Search n} {level : Nat}
    (h : PairsOk G ctx st)
    (hp : level ≠ st.noncheaplevel →
      PairOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1 (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    PairsOk G ctx (pruneReturn level st).2 := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · rename_i hne
    exact h.push (hp (by simpa using hne))
  · exact h

/-- The prune tail inserts exactly its implicit pair when the level differs from its boundary. -/
theorem pruneReturn_autos {κ : Type} (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.autos =
      if level != st.noncheaplevel then (pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)).autos
      else st.autos := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite SearchState.autos]

/-- Workspace effects depend only on the admission kind and the incoming pair fields. -/
theorem leafExit_autos {κ : Type} (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.autos =
      match leaf with
      | .internal => st.autos
      | .autoFirst | .autoCanon => (admit st).autos
      | .bad | .better _ => (pruneReturn level st).2.autos := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.autos, admit_autos, pruneReturn_autos, install]
  all_goals simp only [pushAuto, apply_ite SearchState.autos, ite_self]
  all_goals repeat' split
  all_goals first | rfl | contradiction

/-- All leaf actions preserve the ledger once the explicit and implicit admissions are justified. -/
theorem PairsOk.leaf {G : Colored n k} {ctx : Ctx n} {st : Search n} {level : Nat}
    (h : PairsOk G ctx st) (hn0 : 0 < n) (leaf : Leaf)
    (hc : leaf = .autoFirst ∨ leaf = .autoCanon → checkAutom ctx.g st.workperm = true)
    (hs : leaf = .autoFirst ∨ leaf = .autoCanon → ColorStab G st.workperm)
    (hp : level ≠ st.noncheaplevel →
      PairOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1 (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    PairsOk G ctx (leafExit leaf level st).2 := by
  cases leaf
  all_goals first
    | exact h.congr (leafExit_autos _ _ _)
    | exact (h.admit hn0 (hc (Or.inl rfl)) (hs (Or.inl rfl))).congr (leafExit_autos _ _ _)
    | exact (h.admit hn0 (hc (Or.inr rfl)) (hs (Or.inr rfl))).congr (leafExit_autos _ _ _)
    | exact (h.prune hp).congr (leafExit_autos _ _ _)

/-- Classification preserves the workspace while filling scratch and row-cache fields. -/
theorem classify_autos (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.autos = st.autos := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.autos, ite_self]

/-- The empty initial workspace satisfies the ledger. -/
theorem initial_pairs (G : Colored n k) (ctx : Ctx n) :
    PairsOk G ctx (initial n (initialPartition G).1 (initialPartition G).2) := by
  intro pair hp
  change pair ∈ ([] : List (VSet n × VSet n)) at hp
  simp at hp

end Hex.GraphIso.Nauty
