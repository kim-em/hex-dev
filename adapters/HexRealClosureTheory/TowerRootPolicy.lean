/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRootPolicy
public import HexRealClosureTheory.TowerRoots
public import HexRealClosureTheory.RootPolicy
public import HexRealClosureTheory.TowerModel
public import HexRealClosureTheory.RootTotal
public import HexRealClosureTheory.TransportPolynomial
public import HexRealClosureTheory.TowerTransport

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Native roots retain the universal output exactly for semantic zero. -/
theorem Context.rootsWith_all (model : Model parent K) (policy : Isolation.Policy) (p : DensePoly parent.Value) :
    parent.rootsWith policy p = .all ↔ HexPolyTheory.Interpret.interpret model.value model.zero_iff p = 0 := by
  have generic := Roots.Policy.roots_all model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign model.neg model.inv model.div policy parent.signature p
  cases produced : Roots.Policy.roots policy parent.sign parent.signature p with
  | all => simpa [produced, Context.rootsWith, RootSet.ofOutput] using generic
  | finite entries => simpa [produced, Context.rootsWith, RootSet.ofOutput] using generic

/-- The diagnostic native producer succeeds and agrees with ordinary roots. -/
theorem Context.rootsWith?_success (model : Model parent K) (policy : Isolation.Policy) (p : DensePoly parent.Value) :
    parent.rootsWith? policy p = .ok (parent.rootsWith policy p) := by
  obtain ⟨output, built, returned⟩ := Roots.Policy.roots_success model.value model.zero_iff
    model.one model.add model.sub model.mul model.nat model.sign model.neg model.inv model.div
    policy parent.signature p
  simp only [Context.rootsWith?, Context.rootsWith, built, returned, Except.map]

/-- Native finite entries have exact coverage and original multiplicities,
interpreting their actual stored values in the common ambient model. -/
theorem Context.rootsWith_spec (model : Model parent K) (policy : Isolation.Policy) (p : DensePoly parent.Value)
    {out : List (RootEntry parent)} (returned : parent.rootsWith policy p = .finite out)
    (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.denote model = x ∧ entry.multiplicity = label) ↔
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff p).IsRoot x ∧
        label = (HexPolyTheory.Interpret.interpret model.value model.zero_iff p).rootMultiplicity x := by
  obtain ⟨entries, produced, rfl⟩ := Context.rootsWith_finite policy p returned
  rw [← Roots.Policy.roots_spec model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign model.neg model.inv model.div policy parent.signature p entries produced x label]
  constructor
  · rintro ⟨entry, member, value, multiplicity⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨original, present, (RootEntry.denote_ofEntry original model).symm.trans value,
      multiplicity⟩
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨RootEntry.ofEntry parent entry, List.mem_map.mpr ⟨entry, member, rfl⟩,
      (RootEntry.denote_ofEntry entry model).trans value, multiplicity⟩

/-- The actual native root values are strictly increasing across all factors. -/
theorem Context.rootsWith_sorted (model : Model parent K) (policy : Isolation.Policy) (p : DensePoly parent.Value)
    {out : List (RootEntry parent)} (returned : parent.rootsWith policy p = .finite out) :
    (out.map (fun entry => entry.denote model)).Pairwise (· < ·) := by
  obtain ⟨entries, produced, rfl⟩ := Context.rootsWith_finite policy p returned
  simpa only [List.map_map, Function.comp_def, RootEntry.denote_ofEntry, List.pairwise_map] using
    Roots.Policy.roots_sorted model.value model.zero_iff model.one model.add model.sub model.mul
      model.nat model.sign model.neg model.inv model.div policy parent.signature p entries produced

/-- All finite policies agree on the actual native root values and labels. -/
theorem Context.rootsWith_agreement (model : Model parent K) (first second : Isolation.Policy)
    (p : DensePoly parent.Value) {a b : List (RootEntry parent)}
    (left : parent.rootsWith first p = .finite a) (right : parent.rootsWith second p = .finite b)
    (x : K) (label : Nat) :
    (∃ entry ∈ a, entry.denote model = x ∧ entry.multiplicity = label) ↔
      (∃ entry ∈ b, entry.denote model = x ∧ entry.multiplicity = label) :=
  (Context.rootsWith_spec model first p left x label).trans
    (Context.rootsWith_spec model second p right x label).symm

/-- Native policies return equal ordered lists of interpreted root values
and multiplicities while retaining their own immutable owners. -/
theorem Context.rootsWith_equal (model : Model parent K) (first second : Isolation.Policy)
    (p : DensePoly parent.Value) {a b : List (RootEntry parent)}
    (left : parent.rootsWith first p = .finite a) (right : parent.rootsWith second p = .finite b) :
    (a.map fun e => (e.denote model, e.multiplicity)) =
      (b.map fun e => (e.denote model, e.multiplicity)) := by
  obtain ⟨entries, produced, rfl⟩ := Context.rootsWith_finite first p left
  obtain ⟨others, producedOther, rfl⟩ := Context.rootsWith_finite second p right
  have labels (entry : Roots.Entry parent.sign parent.signature) :
      (RootEntry.ofEntry parent entry).multiplicity = entry.multiplicity := rfl
  simpa only [List.map_map, Function.comp_def, RootEntry.denote_ofEntry, labels] using
    Roots.Policy.roots_equal model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign model.neg model.inv model.div first second
      parent.signature p entries others produced producedOther

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith_equal

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith_all

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith?_success

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith_spec

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith_sorted

/-- info: 'Hex.RealClosure.Tower.Context.rootsWith_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.rootsWith_agreement
