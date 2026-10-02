/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.EarlyReturn
public import HexGraphIso.Nauty.Invariant.Cursor
public import HexGraphIso.Nauty.Invariant.Carrier
import all HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.Reference.Leaf
import all HexGraphIso.Nauty.Policy.Canon.Scatter
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Generic.Short
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat} {κ : Type}

/-- A returned generator retains its reference endpoint or its strictly
smaller coset image. Cleanup does not erase this evidence. -/
inductive RefReturn (ctx : Ctx n) (target : Nat) (out : SearchState n κ) : Prop where
  | first (returned : target = out.gcaFirst)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (returned : target = out.gcaCanon)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | orbit (returned : target = out.gcaFirst)
      (smaller : out.orbits[out.cosetindex]! < out.cosetindex)

/-- A comparison prune can only return below one of its two saved
subtree boundaries. This statement has no generator premise. -/
theorem pruneReturn_boundary {level target : Nat} {st : SearchState n κ} {short : Bool}
    (he : (pruneReturn level st).1 = .unwind target short) :
    st.noncheaplevel ≤ target + 1 ∨ st.allsamelevel ≤ target + 1 := by
  unfold pruneReturn pushAuto at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  repeat' split at he
  all_goals cases he
  all_goals simp only [Int.ofNat_eq_natCast] at *
  all_goals omega

/-- A first-reference classification supplies the scatter's complete
pointwise action using the returned scratch and reference sizes. -/
theorem classify_first_map {ctx : Ctx n} {level numcells : Nat} {before out : Search n}
    (hc : classify ctx level numcells before = (.autoFirst, out))
    (hw : out.workperm.size = n) (hf : out.firstlab.size = n)
    (hp : out.firstlab.toList.Perm (List.range n)) :
    ∀ i, i < n → out.workperm[out.firstlab[i]!]! = out.lab[i]! := by
  obtain ⟨_, _, he, _⟩ := classify_first hc
  rw [he] at hw hf hp ⊢
  have hs : (scatter before.firstlab before).workperm.size = before.workperm.size := scatter_size ..
  have hws : before.workperm.size = n := hs.symm.trans hw
  exact scatter_map hws hf hp

/-- Every automorphism verdict carries evidence after its leaf action,
including canonical returns that do not merge any orbit. -/
theorem leaf_refReturn {G : Colored n k} {ctx : Ctx n} {level numcells target : Nat}
    {before : Search n} {short : Bool}
    (hn0 : 0 < n)
    (ha : (classify ctx level numcells before).1 = .autoFirst ∨
      (classify ctx level numcells before).1 = .autoCanon)
    (he : (leafExit (classify ctx level numcells before).1 level
      (classify ctx level numcells before).2).1 = .unwind target short)
    (hi : RunInv G ctx (leafExit (classify ctx level numcells before).1 level
      (classify ctx level numcells before).2).2) :
    RefReturn ctx target (leafExit (classify ctx level numcells before).1 level
      (classify ctx level numcells before).2).2 := by
  let c := classify ctx level numcells before
  let out := (leafExit c.1 level c.2).2
  have hwork : out.workperm = c.2.workperm := leafExit_workperm ..
  have htrace : c.2.workperm ∈ out.genTrace := by
    dsimp only [out]
    rw [leafExit_trace]
    rcases ha with ha | ha <;> change c.1 = _ at ha <;> rw [ha] <;> exact Array.mem_push_self
  have hcheck := hi.trace _ htrace
  have hsize : c.2.workperm.size = n := hwork ▸ hi.scratch
  have hlab : out.lab = c.2.lab := (leafExit_frame ..).1
  rcases ha with ha | ha
  · change c.1 = .autoFirst at ha
    have hf : out.firstlab = c.2.firstlab := (leafExit_frame ..).2.2.1
    have hm := classify_first_map (Prod.ext ha rfl) hsize (hf ▸ hi.firstSize) (hf ▸ hi.first)
    refine .first ?_ ⟨c.2.workperm, htrace, hcheck, ?_⟩
    · change target = (leafExit c.1 level c.2).2.gcaFirst
      rw [leafExit_gca]
      change (leafExit c.1 level c.2).1 = _ at he
      rw [ha] at he
      unfold leafExit at he
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
      split at he <;> cases he <;> rw [admit_gca]
    · rw [hf, hlab]; exact hm
  · change c.1 = .autoCanon at ha
    have hf : out.canonlab = c.2.canonlab := by dsimp only [out]; rw [ha, autoCanon_ref]
    have hfirst : out.canonlab.toList.Perm (List.range n) := by
      exact isPerm_of_cellsReach hi.canonical.1 hn0 hi.canonical.2
    have hm := classify_canon_out (ctx := ctx) (level := level) (numcells := numcells)
      (st := before) (show c.1 = .autoCanon from ha) hsize
      (hf ▸ hi.canonical.1) (hf ▸ hfirst)
    have hcarrier : LabelCarrier ctx out.canonlab out.lab out.genTrace :=
      ⟨c.2.workperm, htrace, hcheck, by rw [hf, hlab]; exact hm⟩
    change (leafExit c.1 level c.2).1 = _ at he
    rw [ha] at he
    change RefReturn ctx target (leafExit c.1 level c.2).2
    rw [ha]
    change LabelCarrier ctx (leafExit c.1 level c.2).2.canonlab
      (leafExit c.1 level c.2).2.lab (leafExit c.1 level c.2).2.genTrace at hcarrier
    rw [ha] at hcarrier
    unfold leafExit at he hcarrier ⊢
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd] at he hcarrier ⊢
    repeat' split at he
    all_goals cases he
    all_goals simp_all only [↓reduceIte]
    all_goals first | exact .canon rfl hcarrier | exact .orbit rfl (by assumption)

/-- Every non-generator leaf exit is bounded by a saved subtree
boundary, including installation of a better canonical leaf. -/
theorem leaf_boundary {leaf : Leaf} {level target : Nat} {st : SearchState n κ} {short : Bool}
    (hf : leaf ≠ .autoFirst) (hc : leaf ≠ .autoCanon)
    (he : (leafExit leaf level st).1 = .unwind target short) :
    (leafExit leaf level st).2.noncheaplevel ≤ target + 1 ∨
      (leafExit leaf level st).2.allsamelevel ≤ target + 1 := by
  rw [leafExit_noncheap, leafExit_same]
  cases leaf with
  | autoFirst => exact (hf rfl).elim
  | autoCanon => exact (hc rfl).elim
  | internal => cases he
  | better sr =>
    unfold leafExit at he
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
    split at he
    all_goals
      have hh := pruneReturn_boundary he
      exact hh
  | bad =>
    unfold leafExit at he
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
    split at he
    all_goals
      have hh := pruneReturn_boundary he
      exact hh

/-- Fixed-point cleanup preserves the emitted reference carrier. -/
theorem RefReturn.fixed {ctx : Ctx n} {target : Nat} {st : SearchState n κ}
    (h : RefReturn ctx target st) (fixed : VSet n) :
    RefReturn ctx target { st with fixedpts := fixed } := by
  cases h with
  | first hr hc => exact .first hr hc
  | canon hr hc => exact .canon hr hc
  | orbit hr hs => exact .orbit hr hs

/-- An actual unconsumed return above both subtree boundaries carries
the emitted automorphism evidence through every intermediate cleanup. -/
theorem EarlyReturn.reference {G : Colored n k} {ctx : Ctx n} {target bound : Nat}
    {short : Bool} {out : Search n} (h : EarlyReturn ctx target short out)
    (hn0 : 0 < n) (hi : RunInv G ctx out)
    (ht : target < bound) (hn : bound < out.noncheaplevel) (ha : bound < out.allsamelevel) :
    RefReturn ctx target out := by
  obtain ⟨level, numcells, before, he, hs⟩ := h
  let c := classify ctx level numcells before
  let emitted := leafExit c.1 level c.2
  have hauto : c.1 = .autoFirst ∨ c.1 = .autoCanon := by
    by_cases hf : c.1 = .autoFirst
    · exact Or.inl hf
    by_cases hc : c.1 = .autoCanon
    · exact Or.inr hc
    have hb := leaf_boundary hf hc he
    rw [hs] at hn ha
    change bound < emitted.2.noncheaplevel at hn
    change bound < emitted.2.allsamelevel at ha
    change emitted.2.noncheaplevel ≤ target + 1 ∨ emitted.2.allsamelevel ≤ target + 1 at hb
    omega
  have hstored : RunInv G ctx emitted.2 := by
    rw [hs] at hi
    exact hi.congr rfl rfl hi.cache rfl rfl rfl rfl rfl
  have hr := leaf_refReturn hn0 hauto he hstored
  rw [hs]
  exact hr.fixed _

/-- A short-prune request never targets the emitting first ancestor. -/
theorem leaf_short_first {leaf : Leaf} {level target : Nat} {st : SearchState n κ}
    (hpos : 0 < target) (he : (leafExit leaf level st).1 = .unwind target true) :
    target ≠ (leafExit leaf level st).2.gcaFirst := by
  rw [leafExit_gca]
  cases leaf <;> unfold leafExit pruneReturn install admit pushAuto at he
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  all_goals repeat' split at he
  all_goals try dsimp only at he
  all_goals simp_all only [Generic.Exit.unwind.injEq, Bool.and_eq_true, bne_iff_ne,
    Bool.false_eq_true, and_false, false_and, Int.ofNat_eq_natCast]
  all_goals try contradiction
  all_goals omega

/-- An off-path node cannot request short pruning at its first ancestor.
Only an enclosing first-child update could change that ancestor. -/
theorem node_short_first {ctx : Ctx n} {inf tcLevel fuel level numcells target : Nat}
    {st : Search n} (hpos : 0 < target)
    (he : (node false ctx inf tcLevel fuel level numcells st).1 = .unwind target true) :
    target ≠ st.gcaFirst := by
  obtain ⟨depth, cells, before, hemit, hs⟩ := node_short_early ctx inf tcLevel fuel level numcells st he
  have hh := leaf_short_first hpos hemit
  have hg := node_gca ctx inf tcLevel fuel level numcells st
  rw [hs] at hg
  change (leafExit (classify ctx depth cells before).1 depth (classify ctx depth cells before).2).2.gcaFirst = st.gcaFirst at hg
  rwa [hg] at hh

end Hex.GraphIso.Nauty
