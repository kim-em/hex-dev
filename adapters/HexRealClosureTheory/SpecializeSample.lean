/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.SpecializeReplay
public import HexSignDetTheory.RootModel
public import HexRealRootsTheory.RealClosed

public section

namespace Hex.RealClosure.Specialize
open Hex.SignDet HexRealRootsTheory HexPolyTheory.Interpret
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable {Ctx : Type u} [DecidableEq Ctx]

/-- Throughout one positive neighborhood, the actual ordinary real-root count
for every ordered sign condition equals its source table count. -/
theorem counts_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (context : Ctx) (p : Hex.DensePoly (Hex.RationalFn F))
    (a b : Hex.Endpoint (Hex.RationalFn F)) (qs : List (Hex.DensePoly (Hex.RationalFn F)))
    (r : Replay (Hex.RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ condition : List Int,
      ((Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
        ((a.specialize embedding t).map (fun x : ℝ => x))
        ((b.specialize embedding t).map (fun x : ℝ => x))).filter
        (fun x => signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial embedding q t)) x = condition)).card =
        (r.table accepted).count condition := by
  classical
  obtain ⟨η, positive, tables⟩ := r.table_near embedding ordered context p a b qs accepted
  refine ⟨η, positive, fun t ht small condition => ?_⟩
  obtain ⟨checked, counts⟩ := tables t ht small
  have counted := (r.specialize embedding t).count_roots (fun x : ℝ => x)
    (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun x : ℝ => (SignType.sign x : Int)) (fun _ => rfl) context
    (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t)
    (qs.map (fun q => polynomial embedding q t)) checked condition
  rw [← counted, ← Replay.table_lookup _ checked condition, counts condition]

/-- Every condition of positive source count has an ordinary real root
realizing all its signs together, throughout the same neighborhood. -/
theorem exists_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (context : Ctx) (p : Hex.DensePoly (Hex.RationalFn F))
    (a b : Hex.Endpoint (Hex.RationalFn F)) (qs : List (Hex.DensePoly (Hex.RationalFn F)))
    (r : Replay (Hex.RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ condition : List Int,
      0 < (r.table accepted).count condition →
      ∃ x, x ∈ Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
        ((a.specialize embedding t).map (fun x : ℝ => x))
        ((b.specialize embedding t).map (fun x : ℝ => x)) ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial embedding q t)) x = condition := by
  classical
  obtain ⟨η, positive, counts⟩ := counts_near embedding ordered context p a b qs r accepted
  refine ⟨η, positive, fun t ht small condition nonzero => ?_⟩
  have cardinal := counts t ht small condition
  obtain ⟨x, member⟩ := Finset.card_pos.mp (lt_of_lt_of_eq nonzero cardinal.symm)
  exact ⟨x, Finset.mem_filter.mp member⟩

/-- An accepted count-one infinitesimal replay has one ordinary real root
realizing its entire ordered sign condition, throughout one common positive
parameter neighborhood. No embedding of the infinitesimal field into ℝ is used. -/
theorem realizeReplay (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (context : Ctx) (p : Hex.DensePoly (Hex.RationalFn F))
    (a b : Hex.Endpoint (Hex.RationalFn F)) (qs : List (Hex.DensePoly (Hex.RationalFn F)))
    (r : Replay (Hex.RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true)
    (condition : List Int) (one : (r.table accepted).count condition = 1) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      ∃! x, x ∈ Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
        ((a.specialize embedding t).map (fun x : ℝ => x))
        ((b.specialize embedding t).map (fun x : ℝ => x)) ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial embedding q t)) x = condition := by
  classical
  obtain ⟨η, positive, counts⟩ := counts_near embedding ordered context p a b qs r accepted
  refine ⟨η, positive, fun t ht small => ?_⟩
  have cardinal := (counts t ht small condition).trans one
  obtain ⟨x, singleton⟩ := Finset.card_eq_one.mp cardinal
  have member : x ∈ (Tarski.rootsIn
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
      ((a.specialize embedding t).map (fun x : ℝ => x))
      ((b.specialize embedding t).map (fun x : ℝ => x))).filter
      (fun x => signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
        (qs.map (fun q => polynomial embedding q t)) x = condition) := by
    rw [singleton]
    exact Finset.mem_singleton_self x
  refine ⟨x, Finset.mem_filter.mp member, ?_⟩
  intro y hy
  have member : y ∈ (Tarski.rootsIn
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
      ((a.specialize embedding t).map (fun x : ℝ => x))
      ((b.specialize embedding t).map (fun x : ℝ => x))).filter
      (fun x => signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
        (qs.map (fun q => polynomial embedding q t)) x = condition) := Finset.mem_filter.mpr hy
  rw [singleton] at member
  exact Finset.mem_singleton.mp member

/-- The realizing parameter can be chosen below any prescribed positive cap.
This chooses a parameter below an earlier bound; neighborhood composition
uses `realizeReplay`. -/
theorem realizeBelow (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (context : Ctx) (p : Hex.DensePoly (Hex.RationalFn F))
    (a b : Hex.Endpoint (Hex.RationalFn F)) (qs : List (Hex.DensePoly (Hex.RationalFn F)))
    (r : Replay (Hex.RationalFn F) Ctx)
    (accepted : r.check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      context p a b qs = true)
    (condition : List Int) (one : (r.table accepted).count condition = 1)
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t, 0 < t ∧ t < cap ∧
      ∃! x, x ∈ Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding p t))
        ((a.specialize embedding t).map (fun x : ℝ => x))
        ((b.specialize embedding t).map (fun x : ℝ => x)) ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial embedding q t)) x = condition := by
  obtain ⟨η, hη, realize⟩ := realizeReplay embedding ordered context p a b qs r
    accepted condition one
  obtain ⟨t, ht, small⟩ := exists_between (lt_min hη positive)
  exact ⟨t, ht, lt_of_lt_of_le small (min_le_right _ _),
    realize t ht (lt_of_lt_of_le small (min_le_left _ _))⟩

/-- info: 'Hex.RealClosure.Specialize.realizeReplay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.realizeReplay

/-- info: 'Hex.RealClosure.Specialize.realizeBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.realizeBelow

/-- info: 'Hex.RealClosure.Specialize.counts_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.counts_near

/-- info: 'Hex.RealClosure.Specialize.exists_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_near

end Hex.RealClosure.Specialize
